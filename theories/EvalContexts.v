From Stdlib Require Import
  Arith   
  Basics         
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Morphisms
  Nat
  Program.Basics
  List
  Lia
  Relations.

From LEpic Require Import Contexts Syntax.
Import Renamings.

Local Open Scope program_scope.
Local Open Scope bool_scope.


(* Evaluation Contexts (ECs) --------------------------------------------------- *)

Inductive EC_term :=
| Ebag (m n:nat) (EP : EC_proc)   (* nu. {f1...fm} {r1..rn} EP *)

with EC_proc :=
| Ehol
| Edeflam (r:rvar) (Et : EC_term)  (* r <- lam r'. Et *)
| Epar (EP : EC_proc) (P : proc). (* EP | P *)
(* May need left and right Epars *)


Scheme EC_term_ind_m := Induction for EC_term Sort Prop
  with EC_proc_ind_m := Induction for EC_proc Sort Prop.
Combined Scheme EC_ind from EC_term_ind_m, EC_proc_ind_m.

Scheme EC_term_rect_m := Induction for EC_term Sort Type
  with EC_proc_rect_m := Induction for EC_proc Sort Type.
Combined Scheme EC_rect from EC_term_rect_m, EC_proc_rect_m.

Scheme EC_term_rec_m := Induction for EC_term Sort Set
  with EC_proc_rec_m := Induction for EC_proc Sort Set.
Combined Scheme EC_rec from EC_term_rec_m, EC_proc_rec_m.


(* Projects the EC_term components *)
Definition get_fvars_Et Et := match Et with Ebag m _ _ => m end.
Definition get_rvars_Et Et := match Et with Ebag _ n _ => n end.
Definition get_proc_Et Et := match Et with Ebag _ _ EP => EP end.



Reserved Notation "Et <=[ P ]" (at level 55).
Reserved Notation "EP <=[ P ]p" (at level 55).
Reserved Notation "Et <=<[ EP ]" (at level 55).
Reserved Notation "EP <=<[ EP' ]p" (at level 55).

(* Fill an evaluation context with a process *)
Fixpoint fill_EC_term (Et : EC_term) (P : proc) : term :=
  match Et with
  | Ebag m n EP => bag m n (EP <=[ P ]p)
  end

with fill_EC_proc (EP : EC_proc) (P : proc) : proc :=
  match EP with
  | Ehol => P
  | Edeflam r Et => def r (lam (Et <=[ P ]))
  | Epar EP P' => par (EP <=[ P ]p) P' 
  end
  
where "Et <=[ P ]" := (fill_EC_term Et P)
and   "EP <=[ P ]p" := (fill_EC_proc EP P).

(* Fill an evaluation context with an EC process *)
Fixpoint EC_fill_EC_term (Et : EC_term) (EP : EC_proc) : EC_term :=
  match Et with
  | Ebag m n EP' => Ebag m n (EP' <=<[ EP ]p)
  end

with EC_fill_EC_proc (EP : EC_proc) (EP' : EC_proc) : EC_proc :=
  match EP with
  | Ehol => EP'
  | Edeflam r Et => Edeflam r (Et <=<[ EP' ])
  | Epar EP'' P => Epar (EP'' <=<[ EP' ]p) P 
  end
  
where "Et <=<[ EP ]" := (EC_fill_EC_term Et EP)
and   "EP <=<[ EP' ]p" := (EC_fill_EC_proc EP EP').



(* Returns true if the hole is not underneath a lambda binding.
   Otherwise returns false. *)
Fixpoint is_hole_scope_at_top Et := 
  is_hole_scope_at_top_proc (get_proc_Et Et)
with is_hole_scope_at_top_proc EP := 
  match EP with
  | Ehol => true
  | Edeflam _ _ => false
  | Epar EP' _ => is_hole_scope_at_top_proc EP'
  end.



(* HELPER FUNCTION! for split_hole_scope below.
  EP is the EC being traversed
  EP_acc accumulates the current scope as EP is traversed
  Et_trav accumulates EP_acc when EP traverses into a new scope
      (i.e. when an Edeflam is reached), upon which EP_acc resets  *)
Fixpoint split_hole_scope_builder (EP EP_acc : EC_proc) 
                                  (Et_trav : EC_term) : EC_term * EC_proc :=
  match EP with
  | Ehol => match EP_acc with  (* Case on if hole scope = top scope*)
            | Edeflam _ _ => (Et_trav, EP_acc)  (* hole scope <> top scope *)
            | _           => (Et_trav <=<[ EP_acc ], Ehol)  (* hole scope = top scope *)
            end
  | Edeflam r (Ebag m n EP') => split_hole_scope_builder EP' 
                                  (Edeflam r (Ebag m n Ehol))  (* Start accumulating new scope *)
                                  (Et_trav <=<[ EP_acc ])  (* Pass old scope to Et_trav *)
  | Epar EP' P => split_hole_scope_builder EP' 
                    (EP_acc <=<[ Epar Ehol P ]p) Et_trav
  end.


(* Given an Et, returns a pair whose 
      first element is the EC with the hole scope replaced by a hole and
      second element is the hole scope,
    UNLESS the hole scope of Et is the top scope, 
      in which case the first element is just Et
      and the second element is Ehol
      (because there was no deeper hole scope to split).
  This function is used in the semantics to
    get the scope of where the reductions occur
    (which is the hole scope of the EC being filled)  *)
Definition split_hole_scope (Et : EC_term) : EC_term * EC_proc :=
  match Et with
  | Ebag m n EP => split_hole_scope_builder EP Ehol (Ebag m n Ehol)
  end.


(* Projects the hole scope from split_hole_scope *)
Definition hole_scope Et := 
  match split_hole_scope Et with 
  | (_, Edeflam _ Et_lam) => Et_lam
  | _ => Et
  end.



(* Applies a funciton f at the hole scope, returning the result *)
Definition apply_at_hole_scope {X} (f : EC_term -> X) Et := 
  f (hole_scope Et).

(* Applies either f1 or f2 to the hole scope, depending on whether 
   the hole scope is the top scope *)
Definition case_hole_scope_at_top {X} (f1 f2 : EC_term -> X) (Et : EC_term) :=
  (if is_hole_scope_at_top Et then f1 else f2) (hole_scope Et).

(* Mutates the hole scope with a function f *)
Definition mutate_hole_scope (f : EC_term -> EC_term) (Et : EC_term) :=
  match split_hole_scope Et with
  | (_, Ehol) => f Et
  | (Et_os, Edeflam r Et_hs) => Et_os <=<[ Edeflam r (f Et_hs) ]
  | _ => Ebag 0 0 Ehol (* Cannot reach here *)
  end.

(* Mutates the hole scope with a function f *)
Definition mutate_under_hole_scope (f : EC_proc -> EC_proc) (Et : EC_term) :=
  match split_hole_scope Et with
  | (_, Ehol) => match Et with Ebag m n EP => Ebag m n (f EP) end
  | (Et_os, Edeflam r (Ebag m n EP)) => Et_os <=<[ Edeflam r (Ebag m n (f EP)) ]
  | _ => Ebag 0 0 Ehol (* Cannot reach here *)
  end.


Definition bound_rvars_at_hole_scope :=
  apply_at_hole_scope get_rvars_Et.

(* Gives the number of fvars bound by the hole scope *)
Definition bound_fvars_at_hole_scope : EC_term -> nat :=
  apply_at_hole_scope get_fvars_Et.

(* Gives the number of fvars bound in all scopes *)
Fixpoint bound_fvars_to_hole Et : nat :=
  match Et with Ebag m _ EP => m + (bound_fvars_to_hole_proc EP) end
with bound_fvars_to_hole_proc EP : nat :=
  match EP with
  | Ehol => 0
  | Epar EP' _ => bound_fvars_to_hole_proc EP'
  | Edeflam _ Et => bound_fvars_to_hole Et
  end.
  
(* Gives the number of fvars bound before the hole scope *)
Definition bound_fvars_before_hole_scope Et : nat :=
  (bound_fvars_to_hole Et) - (bound_fvars_at_hole_scope Et).



(* Apply renamings on ECs *)

Fixpoint rename_rvar_EC_proc {n n'} (v : ren n n') (EP : EC_proc) :=
  match EP with
  | Ehol => Ehol
  | Edeflam r Et => Edeflam (v r) Et
  | Epar EP P => Epar (rename_rvar_EC_proc v EP) (rename_rvar_proc v P)
  end.
Definition rename_rvar_EC_term {n n'} (v : ren n n') (Et : EC_term) :=
  match Et with
  | Ebag m n'' EP => Ebag m n'' (rename_rvar_EC_proc (ren_shift n'' v) EP)
  end.

Fixpoint rename_fvar_EC_proc {m m'} (v : ren m m') (EP : EC_proc) :=
  match EP with
  | Ehol => Ehol
  | Edeflam r Et => Edeflam r (rename_fvar_EC_term v Et)
  | Epar EP P => Epar (rename_fvar_EC_proc v EP) (rename_fvar_proc v P)
  end
with rename_fvar_EC_term {m m'} (v : ren m m') (Et : EC_term) :=
  match Et with
  | Ebag m'' n EP => Ebag m'' n (rename_fvar_EC_proc (ren_shift m'' v) EP)
  end.



(* Lemmas for EC functions *)

(* Filling twice is the same as first filling the filler *)
Lemma commute_fill :
    (forall Et EP P,  Et <=<[ EP ] <=[ P ] = 
                      Et <=[ EP <=[ P ]p ])
/\  (forall EP EP' P, EP <=<[ EP' ]p <=[ P ]p = 
                      EP <=[ EP' <=[ P ]p ]p).
Proof. apply EC_ind; simpl; intros; try rewrite H; auto. Qed.

Lemma commute_EC_fill :
    (forall Et EP1 EP2, Et <=<[ EP1 ] <=<[ EP2 ] = 
                        Et <=<[ EP1 <=<[ EP2 ]p ])
/\  (forall EP EP1 EP2, EP <=<[ EP1 ]p <=<[ EP2 ]p = 
                        EP <=<[ EP1 <=<[ EP2 ]p ]p).
Proof. apply EC_ind; simpl; intros; try rewrite H; auto. Qed.

Lemma commute_fill_term : forall Et EP P,
  Et <=<[ EP ] <=[ P ] = Et <=[ EP <=[ P ]p ].
Proof. apply commute_fill. Qed.
Lemma commute_fill_proc : forall EP EP' P,
  EP <=<[ EP' ]p <=[ P ]p = EP <=[ EP' <=[ P ]p ]p.
Proof. apply commute_fill. Qed.
Lemma commute_EC_fill_term : forall Et EP1 EP2,
  Et <=<[ EP1 ] <=<[ EP2 ] = Et <=<[ EP1 <=<[ EP2 ]p ].
Proof. apply commute_EC_fill. Qed.
Lemma commute_EC_fill_proc : forall EP EP1 EP2,
  EP <=<[ EP1 ]p <=<[ EP2 ]p = EP <=<[ EP1 <=<[ EP2 ]p ]p.
Proof. apply commute_EC_fill. Qed.



(* Pops the head construct from a filler,
    allowing it to fill independently *)
Lemma shift_Ehol_fill : 
    (forall Et, Et <=<[ Ehol ] = Et)
/\  (forall EP, EP <=<[ Ehol ]p = EP).
Proof. apply EC_ind; simpl; intros; try rewrite H; auto. Qed.

Lemma shift_Edeflam_fill : 
    (forall Et r m n EP, Et <=<[ Edeflam r (Ebag m n EP) ] = 
                        (Et <=<[ Edeflam r (Ebag m n Ehol) ]) <=<[ EP ])
/\  (forall EP r m n EP', EP <=<[ Edeflam r (Ebag m n EP') ]p = 
                        (EP <=<[ Edeflam r (Ebag m n Ehol) ]p) <=<[ EP' ]p).
Proof. apply EC_ind; simpl; intros; try rewrite H; auto. Qed.

Lemma shift_Epar_fill : 
    (forall Et P EP, Et <=<[ Epar EP P ] = 
                    (Et <=<[ Epar Ehol P ]) <=<[ EP ])
/\  (forall EP P EP', EP <=<[ Epar EP' P ]p = 
                    (EP <=<[ Epar Ehol P ]p) <=<[ EP' ]p).
Proof. apply EC_ind; simpl; intros; try rewrite H; auto. Qed.

Lemma shift_Ehol_fill_term : forall Et, Et <=<[ Ehol ] = Et.
Proof. apply shift_Ehol_fill. Qed.
Lemma shift_Ehol_fill_proc : forall EP, EP <=<[ Ehol ]p = EP.
Proof. apply shift_Ehol_fill. Qed.
Lemma shift_Edeflam_fill_term : forall Et r m n EP, 
  Et <=<[ Edeflam r (Ebag m n EP) ] = (Et <=<[ Edeflam r (Ebag m n Ehol) ]) <=<[ EP ].
Proof. apply shift_Edeflam_fill. Qed.
Lemma shift_Edeflam_fill_proc : forall EP r m n EP', 
  EP <=<[ Edeflam r (Ebag m n EP') ]p = (EP <=<[ Edeflam r (Ebag m n Ehol) ]p) <=<[ EP' ]p.
Proof. apply shift_Edeflam_fill. Qed.
Lemma shift_Epar_fill_term : forall Et P EP, 
  Et <=<[ Epar EP P ] = (Et <=<[ Epar Ehol P ]) <=<[ EP ].
Proof. apply shift_Epar_fill. Qed.
Lemma shift_Epar_fill_proc : forall EP P EP', 
  EP <=<[ Epar EP' P ]p = (EP <=<[ Epar Ehol P ]p) <=<[ EP' ]p.
Proof. apply shift_Epar_fill. Qed.

Ltac shift_fill_left :=
  repeat rewrite shift_Ehol_fill_term; repeat rewrite shift_Ehol_fill_proc;
  try rewrite shift_Edeflam_fill_term; try rewrite shift_Edeflam_fill_proc;
  try rewrite shift_Epar_fill_term; try rewrite shift_Epar_fill_proc.



(* Given whether hole scope = top scope for a filling and fillee,
    gives whether hole scope = top scope for the fill result *)
Lemma meet_hole_scope_at_top :
    (forall Et EP, is_hole_scope_at_top Et = true ->
                    is_hole_scope_at_top_proc EP = true ->
                    is_hole_scope_at_top (Et <=<[ EP ]) = true)
/\  (forall EP EP', is_hole_scope_at_top_proc EP = true ->
                    is_hole_scope_at_top_proc EP' = true ->
                    is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = true).
Proof. apply EC_ind; simpl; intros; try apply H; auto. Qed.

Lemma join_hole_scope_at_top :
    (forall Et EP, (is_hole_scope_at_top Et = false \/
                    is_hole_scope_at_top_proc EP = false) ->
                    is_hole_scope_at_top (Et <=<[ EP ]) = false)
/\  (forall EP EP', (is_hole_scope_at_top_proc EP = false \/
                    is_hole_scope_at_top_proc EP' = false) ->
                    is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = false).
Proof. 
  apply EC_ind; simpl; intros; try apply H; auto. 
  destruct H; auto. discriminate H.
Qed.

Lemma meet_hole_scope_at_top_term : forall Et EP, is_hole_scope_at_top Et = true ->
  is_hole_scope_at_top_proc EP = true -> is_hole_scope_at_top (Et <=<[ EP ]) = true.
Proof. apply meet_hole_scope_at_top. Qed.
Lemma meet_hole_scope_at_top_proc: forall EP EP', is_hole_scope_at_top_proc EP = true ->
  is_hole_scope_at_top_proc EP' = true -> is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = true.
Proof. apply meet_hole_scope_at_top. Qed.
Lemma left_join_hole_scope_at_top_term : forall Et EP, 
  is_hole_scope_at_top Et = false -> is_hole_scope_at_top (Et <=<[ EP ]) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.
Lemma right_join_hole_scope_at_top_term : forall Et EP, 
  is_hole_scope_at_top_proc EP = false -> is_hole_scope_at_top (Et <=<[ EP ]) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.
Lemma left_join_hole_scope_at_top_proc : forall EP EP', 
  is_hole_scope_at_top_proc EP = false -> is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.
Lemma right_join_hole_scope_at_top_proc : forall EP EP', 
  is_hole_scope_at_top_proc EP' = false -> is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.



(* Induction technique for inducting on the 
    traversed EP in split_hole_scope_builder.
  This is needed because split_hole_scope_builder
    doesn't always decrease the input by one construct
    (in Edeflam, the inner Ebag is also traversed).
  Unsafe because it does not force that you give
    a substructure of the inducted EP,
    but Qed will fail if you give anything that's not a substructure
    (use "Guarded." to check anytime that you've only given substructures).  *)
Ltac EP_ind_unsafe IH EP :=
  match goal with [|- forall x, @?P x] => refine (fix IH EP: _ := _) end;
    let r := fresh in let n := fresh in let m := fresh in let P := fresh in
  destruct EP as [ | r [ m n EP ] | EP P ].



(* NOTE: The lemmas concerning split_hole_scope
    start by destructing its argument and
    giving a new lemma that is essentially the same
    but concerning split_hole_scope_builder
    (and so may require some more machinery).  *)

(* split_hole_scope can only return Ehol or Edeflam as second element *)
Lemma inv_split_hole_scope :
  (forall (Et : EC_term),
    (exists Et_top,
      split_hole_scope Et = (Et_top, Ehol))
\/  (exists Et_top r Et_rest,
      split_hole_scope Et = (Et_top, Edeflam r Et_rest))).
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  enough (forall (EP EP_acc : EC_proc) (Et_trav : EC_term),
      (exists Et_top : EC_term, 
        split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Ehol))
   \/ (exists (Et_top : EC_term) (r : rvar) (Et_rest : EC_term),
        split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_rest)));
      try apply H.
  (* Edeflam and Epar immediate after IH *)
    EP_ind_unsafe IH EP; simpl; intros; auto.
  (* Ehol cases on if hole scope = top scope, both cases being trivial *)
    destruct EP_acc; eauto.
Qed.

Lemma inv_split_hole_scope_Epar :
  (forall Et Et_top EP P,
    split_hole_scope Et <> (Et_top, Epar EP P)).
Proof.
  unfold not; intros.
  destruct (inv_split_hole_scope Et).
  all: dest_conj_disj_exist; rewrite H0 in H; discriminate.
Qed.



(* If EP_acc is a deflam, this indicates that hole scope <> top scope *)
Lemma split_hole_scope_builder_Edeflam_acc :
  forall EP r Et_acc Et_trav Et_top,
    split_hole_scope_builder EP (Edeflam r Et_acc) Et_trav <> (Et_top, Ehol).
Proof. 
  (* All cases are immediate after IH *)
  EP_ind_unsafe IH EP; simpl; intros; auto.
  discriminate.
Qed.


(* If hole scope = top scope then split_hole_scope
    returns its input as the first element. *)
Lemma inv_split_hole_scope_Ehol_eq :
  forall (Et Et_top : EC_term),
    split_hole_scope Et = (Et_top, Ehol) ->
    Et_top = Et.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  (* The new lemma treats the "whole input" as EP filling EP_acc filling Et_trav
      since Et_trav accumulates scopes and EP_acc accumulates current scope from EP *)
    enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term),
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Ehol) ->
            Et_top = Et_trav <=<[ EP_acc <=<[ EP ]p ]); try apply H.
  (* All cases pop the head off EP with shift_fill_left *)
    EP_ind_unsafe IH EP; simpl; intros; shift_fill_left.
  (* Ehol cases on if hole scope = top scope *)
  - destruct EP_acc; simpl.
    all: injection H; intros; subst; repeat rewrite shift_Ehol_fill_proc; auto.
    discriminate H0.
  (* Edeflam is a contradiction *)
  - now apply split_hole_scope_builder_Edeflam_acc in H2.
  (* Epar is by IH *)
  - apply IH; auto.
Qed.


(* Asserts that hole scope = top scope
    if split_hole_scope returns Ehol as second element. *)
Lemma inv_split_hole_scope_Ehol_hs :
  forall (Et Et_top : EC_term),
    split_hole_scope Et = (Et_top, Ehol) ->
    is_hole_scope_at_top Et = true.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term),
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Ehol) ->
            is_hole_scope_at_top_proc EP = true); try apply H.
  EP_ind_unsafe IH EP; simpl; intros.
  (* Ehol gives hole scope = top scope *)
  - reflexivity.
  (* Edeflam is a contradiction *)
  - now apply split_hole_scope_builder_Edeflam_acc in H2.
  (* Epar is by IH *)
  - eapply IH; apply H.
Qed.


(* Asserts that hole scope <> top scope
    if split_hole_scope returns Edeflam as second element. *)
Lemma inv_split_hole_scope_Edeflam :
  forall (Et Et_top : EC_term) r Et_rest,
    split_hole_scope Et = (Et_top, Edeflam r Et_rest) ->
    is_hole_scope_at_top Et = false.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  (* An additional hypothesis is made that EP_acc's hole scope = top scope
      to remember that we are traversing the top scope
    (once we reach an Edeflam, we can prove hole scope <> top scope
      without ever needing to go under). *)
  enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term) r Et_rest,
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_rest) ->
            is_hole_scope_at_top_proc EP_acc = true ->
            is_hole_scope_at_top_proc EP = false); try (intros; eapply H; eauto).
  EP_ind_unsafe IH EP; simpl; intros.
  (* Ehol is a contradiction *)
  - destruct EP_acc; try discriminate H. discriminate H0.
  (* Edeflam gives hole scope <> top scope *)
  - reflexivity.
  (* Epar is by IH, but also needs to show 
      the new accumulator still has its hole scope = top scope *)
  - eapply IH; try apply H. 
    apply meet_hole_scope_at_top_proc; auto.
Qed.


(* Asserts that the second returned element of
    split_hole_scope is a hole scope. *)
Lemma split_hole_scope_gives_hole_scope :
  forall (Et Et_top : EC_term) r Et_rest,
    split_hole_scope Et = (Et_top, Edeflam r Et_rest) ->
    is_hole_scope_at_top Et_rest = true.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  (* The extra hypothesis tracks that EP_acc only builds one scope at a time *)
  enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term) r Et_rest,
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_rest) ->
            (forall r' Et_acc, EP_acc = Edeflam r' Et_acc -> 
                is_hole_scope_at_top Et_acc = true) ->
            is_hole_scope_at_top Et_rest = true).
  { intros; eapply H; eauto; discriminate. }
  EP_ind_unsafe IH EP; simpl; intros.
  (* Ehol uses that EP_acc wraps the hole scope *)
  - destruct EP_acc; try discriminate H.
    injection H; intros; subst. eauto.
  (* Edeflam is by IH (the extra hypothesis in the IH is immediate) *)
  - eapply IH; eauto.
    intros. injection H4; intros; subst. auto.
  (* Epar is by IH, but also needs to show 
      the new accumulator still has its hole scope = top scope *)
  - eapply IH; eauto. intros.
    (* Need to get that EP_acc = Edeflam r' Et *) 
    destruct EP_acc; try discriminate H1.
    injection H1; intros; subst.
    apply meet_hole_scope_at_top_term; eauto.
Qed.














(* Well Formedness on Evaluation Contexts -------------------------------- *)

(* An EC is well-formed under contexts G and D as well as 
   "hole contexts" G_hol and D_hol iff filling the EC with
   a process that is well-formed under G_hol and D_hol creates
   a term that is well-formed under G and D.

   wf_Ehol allows the hole to capture the unused linear resources 
   into G_hol and D_hol, indicating that any process filling the
   EC must use exactly those resources in G_hol and D_hol in order
   to preserve well-formedness. *)

Unset Elimination Schemes.

Inductive wf_EC_term : forall (m n m_hol n_hol:nat),
    lctxt m_hol -> lctxt n_hol -> EC_term -> Prop :=
| wf_Ebag :
  forall m n m' n' m_hol n_hol
    (HN' : n' <= 1)
    (G : lctxt m) (D : lctxt n)
    (G_hol : lctxt m_hol) (D_hol : lctxt n_hol)
    (UG : forall x, x < m -> (G x) = 1)
    (UD : forall x, x < n -> (D x) = 2 \/ (D x) = 0)
    (EP : EC_proc)
    (WFP : wf_EC_proc (m + m') (n + n') m_hol n_hol
                      (G ⊗ (zero m')) (D ⊗ (flat_ctxt 1 n')) 
                      G_hol D_hol EP),
    wf_EC_term m' n' m_hol n_hol G_hol D_hol (Ebag m n EP)

with wf_EC_proc : forall (m n m_hol n_hol:nat), 
    lctxt m -> lctxt n -> lctxt m_hol -> lctxt n_hol -> EC_proc -> Prop :=
| wf_Ehol :
  forall m n
    (G G_hol: lctxt m) (D D_hol: lctxt n)
    (HG : G ≡[m] G_hol)
    (HD : D ≡[n] D_hol),
    wf_EC_proc m n m n G D G_hol D_hol Ehol

| wf_Edeflam :
  forall m n m_hol n_hol
    (G : lctxt m) (G_hol : lctxt m_hol)
    (D : lctxt n) (D_hol : lctxt n_hol)
    (r : rvar) (HR : r < n)
    (Et : EC_term)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (one n r))
    (WFT : wf_EC_term m 1 m_hol n_hol G_hol D_hol Et),
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol (Edeflam r Et)

| wf_Epar :
  forall m n m_hol n_hol
    (G1 G2 G : lctxt m) (G_hol : lctxt m_hol)
    (D1 D2 D : lctxt n) (D_hol : lctxt n_hol)
    (EP : EC_proc) (P : proc)
    (WFP1 : wf_EC_proc m n m_hol n_hol G1 D1 G_hol D_hol EP)
    (WFP2 : wf_proc m n G2 D2 P)
    (HG : G ≡[m] (G1 ⨥ G2))
    (HD : D ≡[n] (D1 ⨥ D2)),
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol (Epar EP P).

Set Elimination Schemes.

Scheme wf_EC_term_ind := Induction for wf_EC_term Sort Prop
    with wf_EC_proc_ind := Induction for wf_EC_proc Sort Prop.

Combined Scheme wf_EC_ind from wf_EC_term_ind, wf_EC_proc_ind.



(* Prove that EC well-formedness respects context equivalence. *)
Lemma EC_equiv_wf :
  (forall m n m_hol n_hol G1_hol D1_hol Et,
    wf_EC_term m n m_hol n_hol G1_hol D1_hol Et ->
      forall G2_hol D2_hol,
    G1_hol ≡[m_hol] G2_hol ->
    D1_hol ≡[n_hol] D2_hol ->
      wf_EC_term m n m_hol n_hol G2_hol D2_hol Et)
  /\
  (forall m n m_hol n_hol G1 D1 G1_hol D1_hol EP,
    wf_EC_proc m n m_hol n_hol G1 D1 G1_hol D1_hol EP ->
      forall G2 D2 G2_hol D2_hol,
    G1 ≡[m] G2 ->
    D1 ≡[n] D2 ->
    G1_hol ≡[m_hol] G2_hol ->
    D1_hol ≡[n_hol] D2_hol ->
      wf_EC_proc m n m_hol n_hol G2 D2 G2_hol D2_hol EP).
Proof.
  apply wf_EC_ind; intros.
  (* Ebag *)
  - econstructor; eauto. apply H; auto; reflexivity.
  (* Ehol *)
  - econstructor; do 2 (eapply transitivity; eauto); symmetry; auto.
  (* Edeflam *)
  - econstructor; auto; eapply transitivity; eauto; symmetry; auto.
  (* Epar *)
  - econstructor; eauto.
    2, 3: eapply transitivity; eauto; symmetry; auto.
    apply H; auto; reflexivity.
Qed.  

#[global] Instance Proper_wf_EC_term {m n m_hol n_hol : nat} : 
  Proper ((@ctxt_eq nat m_hol) ==> (@ctxt_eq nat n_hol) ==> 
            eq ==> iff) (wf_EC_term m n m_hol n_hol).
Proof. repeat red; intros; subst. split; intros.
  - eapply EC_equiv_wf; eauto.
  - symmetry in H, H0. eapply EC_equiv_wf; eauto. Qed.

#[global] Instance Proper_wf_EC_proc {m n m_hol n_hol : nat} : 
  Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> 
          (@ctxt_eq nat m_hol) ==> (@ctxt_eq nat n_hol) ==> 
            eq ==> iff) (wf_EC_proc m n m_hol n_hol).
Proof. repeat red; intros; subst. split; intros.
  - eapply EC_equiv_wf; eauto.
  - symmetry in H, H0, H1, H2. eapply EC_equiv_wf; eauto. Qed.



(* Filling an EC preserves well-formedness *)
Lemma fill_wf_pres :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall P,
          wf_proc m_hol n_hol G_hol D_hol P ->
        wf_term m n (Et <=[ P ]))
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall P,
          wf_proc m_hol n_hol G_hol D_hol P ->
        wf_proc m n G D (EP <=[ P ]p)).
Proof.
  apply wf_EC_ind; intros.
  (* Ebag and Epar by IH *)
    all: try solve [ econstructor; eauto ].
  (* Ehol just needs rewriting (it gives P when filled) *)
  - rewrite HG, HD; auto.
  (* Edeflam builds two layers (using IH) *)
  - simpl. apply wf_def with (D' := zero n); try rewrite sum_zero_r; auto.
    constructor; auto; reflexivity.
Qed.

Lemma EC_fill_wf_pres :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall EP m_hol' n_hol' G_hol' D_hol',
          wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP ->
        wf_EC_term m n m_hol' n_hol' G_hol' D_hol' (Et <=<[ EP ]))
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall EP' m_hol' n_hol' G_hol' D_hol',
          wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP' ->
        wf_EC_proc m n m_hol' n_hol' G D G_hol' D_hol' (EP <=<[ EP' ]p)).
Proof.
  apply wf_EC_ind; intros.
  (* Most cases by IH *)
    all: try solve [ econstructor; eauto ].
  (* Ehol just needs rewriting (it gives P when filled) *)
    rewrite HG, HD; auto.
Qed.

Lemma fill_wf_pres_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> forall (P : proc),
  wf_proc m_hol n_hol G_hol D_hol P -> wf_term m n (Et <=[ P ]).
Proof. apply fill_wf_pres. Qed.
Lemma fill_wf_pres_proc : forall m n m_hol n_hol G D G_hol D_hol EP, 
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> forall (P : proc),
  wf_proc m_hol n_hol G_hol D_hol P -> wf_proc m n G D (EP <=[ P ]p).
Proof. apply fill_wf_pres. Qed.
Lemma EC_fill_wf_pres_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> forall EP m_hol' n_hol' G_hol' D_hol',
  wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP ->
  wf_EC_term m n m_hol' n_hol' G_hol' D_hol' (Et <=<[ EP ]).
Proof. apply EC_fill_wf_pres. Qed.
Lemma EC_fill_wf_pres_proc : forall m n m_hol n_hol G D G_hol D_hol EP, 
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> forall EP' m_hol' n_hol' G_hol' D_hol',
  wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP' ->
  wf_EC_proc m n m_hol' n_hol' G D G_hol' D_hol' (EP <=<[ EP' ]p).
Proof. apply EC_fill_wf_pres. Qed.



(* Useful tactic for the following two lemmas.
    Finishes a goal by using terms given by applying the IH. *)
Ltac finish_by_IH_inv_prem H WF := 
      apply H in WF;
      destruct WF as (m_hol & n_hol & G_hol & D_hol & WF1 & WF2);
      exists m_hol, n_hol, G_hol, D_hol; split; auto;
      econstructor; eauto.

(* If a filled term is well-formed,
    then the filler and fillee are both well-formed *)
Lemma inv_fill_wf :
  (forall Et P m n,
      wf_term m n (Et <=[ P ]) ->
      exists m_hol n_hol 
        (G_hol : lctxt m_hol) (D_hol : lctxt n_hol),
      wf_proc m_hol n_hol G_hol D_hol P /\
      wf_EC_term m n m_hol n_hol G_hol D_hol Et)
  /\
  (forall EP P m n (G : lctxt m) (D : lctxt n),
      wf_proc m n G D (EP <=[ P ]p) ->
      exists m_hol n_hol G_hol D_hol,
      wf_proc m_hol n_hol G_hol D_hol P /\
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP).
Proof.
  (* Most cases by inversion and IH *)
  apply EC_ind; intros.
  (* Ebag *)
  - inversion H0; subst. finish_by_IH_inv_prem H WFP.
  (* Ehol immediate (filling hole gives P) *)
  - exists m, n, G, D. split; auto. econstructor; reflexivity.
  (* Edeflam *)
  - inversion H0; inversion WFO; existT_eq; subst. finish_by_IH_inv_prem H WFT.
    rewrite HD, HD0, sum_zero_r; reflexivity.
  (* Epar *)
  - inversion H0; existT_eq; subst. finish_by_IH_inv_prem H WFP1.
Qed.

Lemma inv_EC_fill_wf :
    (forall Et EP m n m_hol' n_hol' G_hol' D_hol',
      wf_EC_term m n m_hol' n_hol' G_hol' D_hol' (Et <=<[ EP ]) ->
      exists m_hol n_hol G_hol D_hol,
      wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP /\
      wf_EC_term m n m_hol n_hol G_hol D_hol Et)
/\  (forall EP EP' m n m_hol' n_hol' G D G_hol' D_hol',
      wf_EC_proc m n m_hol' n_hol' G D G_hol' D_hol' (EP <=<[ EP' ]p) ->
      exists m_hol n_hol G_hol D_hol,
      wf_EC_proc m_hol n_hol m_hol' n_hol' G_hol D_hol G_hol' D_hol' EP' /\
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP).
Proof.
  (* Most cases by inversion and IH *)
  apply EC_ind; intros.
  (* Ebag *)
  - inversion H0; existT_eq; subst. finish_by_IH_inv_prem H WFP.
  (* Ehol immediate (filling hole gives EP') *)
  - exists m, n, G, D. split; auto. econstructor; reflexivity.
  (* Edeflam *)
  - inversion H0; inversion WFT; existT_eq; subst. finish_by_IH_inv_prem H WFT.
  (* Epar *)
  - inversion H0; existT_eq; subst. finish_by_IH_inv_prem H WFP1.
Qed.



(* The rvar hole context has a maximum binding of 2 *)
Lemma max_rvar_hole_EC_wf :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall r,
          r < n_hol ->
        D_hol r <= 2)
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall r,
          r < n_hol ->
        (D_hol r <= 2)
    \/  (n = n_hol /\ 
          (D r <= 2 ->
        D_hol r <= 2))).
Proof.
  apply wf_EC_ind; intros.
  (* Ebag by IH *)
  - destruct (H r); auto. destruct H1. apply H2. 
    unfold ctxt_app, flat_ctxt.
    (* Case which context r is in *)
    destruct (lt_dec r n); auto. destruct (UD r); lia.
  (* Ehol immediate *)
  - rewrite <- HD; auto.
  (* Elamdef immediate *)
  - auto.
  (* Epar by IH *)
  - destruct (H r); auto. destruct H1; subst.
    right; split; auto; intros.
    rewrite HD in H1; auto. unfold sum in H1; lia.
Qed.

Lemma max_rvar_hole_EC_wf_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
  forall r, r < n_hol -> D_hol r <= 2.
Proof. apply max_rvar_hole_EC_wf. Qed.



(* If a wf EC has hole scope = top scope,
    then bounds of top scope and current scope are the same. *)
Lemma hole_scope_at_top_wf_simpl :
    (forall m n m_hol n_hol G_hol D_hol Et,
      wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
      is_hole_scope_at_top Et = true ->
      m_hol = (get_fvars_Et Et) + m  /\
      n_hol = (get_rvars_Et Et) + n)
/\  (forall m n m_hol n_hol G D G_hol D_hol EP,
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
      is_hole_scope_at_top_proc EP = true ->
      m_hol = m  /\
      n_hol = n).
Proof.
  apply wf_EC_ind; simpl; intros.
  (* Most cases are immediate *)
  all: auto.
  (* Edeflam is a contradiction *)
  discriminate H0.
Qed.

Lemma hole_scope_at_top_wf_simpl_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> is_hole_scope_at_top Et = true ->
  m_hol = (get_fvars_Et Et) + m  /\ n_hol = (get_rvars_Et Et) + n.
Proof. apply hole_scope_at_top_wf_simpl. Qed.
Lemma hole_scope_at_top_wf_simpl_proc : forall m n m_hol n_hol G D G_hol D_hol EP,
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> is_hole_scope_at_top_proc EP = true ->
  m_hol = m  /\ n_hol = n.
Proof. apply hole_scope_at_top_wf_simpl. Qed.




(* If an EC is wf, then splitting it at its hole scope gives
    two wf ECs (the accumulated Et_top and the hole scope Et_hs).
  This case is when hole scope <> top scope,
    but this property is trivial when hole scope = top scope
    given inv_split_hole_scope_Ehol_eq. 
  We keep r < n_top so that the Edeflam can be reconstructed if desired. *)
Lemma split_hole_scope_pres :
  forall Et m n m_hol n_hol G_hol D_hol,
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
  forall Et_top r Et_hs,
    split_hole_scope Et = (Et_top, Edeflam r Et_hs) ->
    exists m_top n_top,
        wf_EC_term m n m_top n_top (zero m_top) (one n_top r) Et_top
    /\  wf_EC_term m_top 1 m_hol n_hol G_hol D_hol Et_hs
    /\  r < n_top.
Proof.
  intro Et; destruct Et as [m0 n0 EP0]; simpl.
  (* As above, the full term is given by EP filling EP_acc filling Et_trav *)
  enough (
      forall EP EP_acc Et_trav Et_top r Et_hs m n m_hol n_hol G_hol D_hol,
        wf_EC_term m n m_hol n_hol G_hol D_hol (Et_trav <=<[ EP_acc ] <=<[ EP ]) ->
        split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_hs) ->
        exists m_top n_top,
            wf_EC_term m n m_top n_top (zero m_top) (one n_top r) Et_top
        /\  wf_EC_term m_top 1 m_hol n_hol G_hol D_hol Et_hs
        /\  r < n_top
    ).
  { intros; eapply H; eauto; simpl; auto. }
  EP_ind_unsafe IH EP; simpl; intros.
  (* Ehol *)
  - destruct EP_acc; try discriminate H0. (* hole scope = top scope is contra *)
    injection H0; intros; subst.
    rewrite shift_Ehol_fill_term in H.
    (* Separate wf for Et_trav/Et_top and EP_acc,
        from which it's straightforward to get wf for Et_hs. *)
    apply inv_EC_fill_wf in H. dest_conj_disj_exist.
    inversion H; existT_eq; subst.
    rewrite HG, HD in H1. eauto.
  (* Edeflam by IH *)
  - rewrite shift_Edeflam_fill_term in H2.
    eapply IH; eauto.
  (* Epar by IH with lots of rewriting *)
  - rewrite shift_Epar_fill_term in H.
    repeat rewrite commute_EC_fill_term in H.
    rewrite <- commute_EC_fill_proc, <- commute_EC_fill_term in H.
    eapply IH; eauto.
Qed.



(* EC Renaming preserves well-formedness *)
Lemma rename_rvar_pres_wf_EC_hs :
  forall EP m n G D G_hol D_hol,
    wf_EC_proc m n m n G D G_hol D_hol EP ->
    is_hole_scope_at_top_proc EP = true ->
    forall (R : ren n n) (HWF : wf_ren R),
      wf_EC_proc m n m n G (lctxt_rename R D)
          G_hol (lctxt_rename R D_hol) (rename_rvar_EC_proc R EP).
Proof.
  induction EP; simpl; intros.
  (* Ehol by context rewriting *)
  - inversion H; existT_eq; subst.
    econstructor; eauto.
    now apply lctxt_rename_ctxt_eq.
  (* Edeflam is contradiction *)
  - discriminate.
  (* Epar is by IH, context rewriting,
      and process renaming preservation *)
  - inversion H; existT_eq; subst.
    econstructor; eauto.
    + apply rename_rvar_pres_wf; eauto.
    + rewrite lctxt_rename_ctxt_eq; eauto.
      now rewrite lctxt_rename_sum.
Qed.


Lemma rename_fvar_pres_wf_EC :
    (forall m n m_hol n_hol G_hol D_hol Et,
      wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
      forall (R : ren m m) (HWF : wf_ren R),
        let R_hol := ren_shift (bound_fvars_to_hole Et) R in
        wf_EC_term m n m_hol n_hol (lctxt_rename R_hol G_hol) D_hol (rename_fvar_EC_term R Et))
/\  (forall m n m_hol n_hol G D G_hol D_hol EP,
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
      forall (R : ren m m) (HWF : wf_ren R),
        let R_hol := ren_shift (bound_fvars_to_hole_proc EP) R in
        wf_EC_proc m n m_hol n_hol (lctxt_rename R G) D (lctxt_rename R_hol G_hol) D_hol 
                                                    (rename_fvar_EC_proc R EP)).
Proof.
  apply wf_EC_ind; simpl; intros.
  (* All cases are essentially context rewriting and IH when appropriate *)
  (* Ebag *)
  - econstructor; eauto.
    rewrite <- lctxt_rename_id with (c := G).
    rewrite <- (@lctxt_rename_zero m' m' R).
    rewrite <- lctxt_rename_app; auto using wf_ren_id.
    fold (@ren_shift m' m' m R).
    rewrite (Nat.add_comm m (bound_fvars_to_hole_proc EP)).
    rewrite <- ren_shift_combine.
    (* Need to rewrite addition associativity in the implicit parameters
        to make the goal and IH line up *)
    Set Printing All. repeat rewrite Nat.add_assoc in *.
    apply (H (ren_shift m R)). Unset Printing All.
    now apply wf_ren_shift.
    (* Ehol *)
  - econstructor; eauto.
    unfold ren_shift; rewrite ctxt_app_0_l; simpl.
    assert ((fun x : var => R x) = R) by now apply functional_extensionality.
    rewrite H; clear H.
    now apply lctxt_rename_ctxt_eq.
    (* Edeflam *)
  - econstructor; eauto.
    rewrite lctxt_rename_ctxt_eq; eauto.
    now rewrite lctxt_rename_zero.
    (* Epar *)
  - econstructor; eauto.
    + apply rename_fvar_pres_wf; eauto.
    + rewrite lctxt_rename_ctxt_eq; eauto.
      now rewrite lctxt_rename_sum.
Qed.




