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
  let f_term :=
    fun Et =>
      match Et with Ebag m n EP => Ebag m n (f EP) end
  in
  mutate_hole_scope f_term Et.

Definition mutate_hole_scope_proc (f : EC_term -> EC_term) (EP : EC_proc) :=
  match mutate_hole_scope f (Ebag 0 0 EP) with Ebag _ _ EP' => EP' end.

Definition mutate_under_hole_scope_proc (f : EC_proc -> EC_proc) (EP : EC_proc) :=
  match mutate_under_hole_scope f (Ebag 0 0 EP) with Ebag _ _ EP' => EP' end.


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



Lemma hole_scope_is_hs :
  forall Et,
    is_hole_scope_at_top (hole_scope Et) = true.
Proof.
  intros. unfold hole_scope.
  destruct (inv_split_hole_scope Et); dest_conj_disj_exist;
      rewrite H.
  - now apply inv_split_hole_scope_Ehol_hs in H.
  - now apply split_hole_scope_gives_hole_scope in H.
Qed.


(* Splitting a hole scope EP with an accumulated Edeflam
    gives a predictable pair *)
Lemma build_hs_correct_Edeflam : 
  forall EP r Et_acc Et_trav,
    is_hole_scope_at_top_proc EP = true ->
    split_hole_scope_builder EP (Edeflam r Et_acc) Et_trav = 
        (Et_trav, (Edeflam r Et_acc) <=<[ EP ]p).
Proof.
  induction EP; simpl; intros.
  - now rewrite shift_Ehol_fill_term.
  - discriminate.
  - rewrite (shift_Epar_fill_term _ _ EP). now apply IHEP.
Qed.

(* Splitting a hole scope EP with a non-Edeflam accumulator
    gives a predictable pair *)
Lemma build_hs_correct_Ehol_Epar : 
  forall EP EP_acc Et_trav,
    is_hole_scope_at_top_proc EP = true ->
    is_hole_scope_at_top_proc EP_acc = true ->
    split_hole_scope_builder EP EP_acc Et_trav = 
        (Et_trav <=<[ EP_acc ] <=<[ EP ], Ehol).
Proof.
  induction EP; simpl; intros.
  - rewrite shift_Ehol_fill_term.
    destruct EP_acc; simpl in H0; auto; discriminate.
  - discriminate.
  - rewrite IHEP; auto using meet_hole_scope_at_top_proc.
    rewrite (shift_Epar_fill_term _ _ EP). 
    now rewrite (commute_EC_fill_term _ EP_acc).
Qed.

(* Splitting a non-hole scope EP gives as the second element
    an Edeflam whose body is the hole scope of the splitee *)
Lemma build_not_hs_correct : 
  forall EP,
    is_hole_scope_at_top_proc EP = false ->
  exists EP' Et r, 
    EP = EP' <=<[ Edeflam r Et ]p /\
    is_hole_scope_at_top Et = true /\
    forall EP_acc Et_trav,
      split_hole_scope_builder EP EP_acc Et_trav = 
          (Et_trav <=<[ EP_acc ] <=<[ EP' ], Edeflam r Et).
Proof.
  EP_ind_unsafe IH EP; simpl; intros.
  - discriminate.
  - destruct (is_hole_scope_at_top_proc EP) eqn:H3.
    + exists Ehol; exists (Ebag H1 H0 EP); exists H.
      repeat split; auto; intros.
      rewrite build_hs_correct_Edeflam; auto; simpl.
      rewrite shift_Ehol_fill_term; auto.
    + remember (IH EP H3); clear Heqe IH. dest_conj_disj_exist; subst.
      exists (Edeflam H (Ebag H1 H0 x)); exists x0; exists x1; simpl.
      repeat split; auto; intros.
      rewrite H6. now rewrite commute_EC_fill_term.
  - remember (IH EP H); clear Heqe IH. dest_conj_disj_exist; subst.
    exists (Epar x H2); exists x0; exists x1; simpl.
    repeat split; auto; intros.
    rewrite H3. now rewrite <- commute_EC_fill_term, (commute_EC_fill_term _ _ x).
Qed.



(* Splitting a hole scope gives a predictable pair *)
Lemma inv_hole_scope_at_top : 
  forall (Et : EC_term),
    is_hole_scope_at_top Et = true ->
    split_hole_scope Et = (Et, Ehol).
Proof.
  intros. destruct (inv_split_hole_scope Et); dest_conj_disj_exist.
  - rewrite H0. apply inv_split_hole_scope_Ehol_eq in H0. subst; reflexivity.
  - apply inv_split_hole_scope_Edeflam in H0. rewrite H in H0. discriminate.
Qed.

(* Splitting a non-hole scope gives a predictable pair *)
Lemma inv_hole_scope_not_at_top : 
  forall (Et : EC_term),
    is_hole_scope_at_top Et = false ->
  exists Et1 Et2 r, 
    Et = Et1 <=<[ Edeflam r Et2 ] /\
    is_hole_scope_at_top Et2 = true /\
    split_hole_scope Et = (Et1, Edeflam r Et2).
Proof. 
  intros; destruct Et; simpl in *.
  remember (build_not_hs_correct EP H); clear Heqe.
  dest_conj_disj_exist; subst.
  exists (Ebag m n x); exists x0; exists x1; auto.
Qed.



(* hole_scope disregards everything above an Edeflam *)
Lemma hole_scope_of_fill_Edeflam : 
  forall Et r Et', 
    hole_scope (Et' <=<[ Edeflam r Et ]) = hole_scope Et.
Proof.
  enough ((forall EP m n r Et EP_acc Et_trav,
          (let (_, e0) := split_hole_scope_builder
                              (EP <=<[ Edeflam r Et ]p) EP_acc Et_trav in
          match e0 with
          | Edeflam _ Et_lam => Et_lam
          | _ => Ebag m n (EP <=<[ Edeflam r Et ]p)
          end) = 
          (let (_, e0) := split_hole_scope Et in
          match e0 with
          | Edeflam _ Et_lam => Et_lam
          | _ => Et
          end))).
  1: intros; unfold hole_scope at 1; destruct Et'; simpl; auto.
  EP_ind_unsafe IH EP; simpl; intros.
  - destruct Et; simpl.
    destruct (is_hole_scope_at_top_proc EP) eqn:H.
    + rewrite build_hs_correct_Edeflam; auto.
      rewrite build_hs_correct_Ehol_Epar; auto.
    + remember (build_not_hs_correct EP H); clear Heqe.
      dest_conj_disj_exist.
      now repeat rewrite H2.
  - rewrite <- (IH EP m n r Et (Edeflam H (Ebag H1 H0 Ehol)) 
                              (Et_trav <=<[ EP_acc])); eauto.
    destruct (build_not_hs_correct (EP <=<[ Edeflam r Et ]p)); dest_conj_disj_exist.
    1: generalize EP; EP_ind_unsafe IH EP_ind; simpl; auto.
    now repeat rewrite H4.


  - rewrite <- (IH EP m n r Et (EP_acc <=<[ Epar Ehol H2 ]p) 
                              Et_trav); eauto.
    destruct (build_not_hs_correct (EP <=<[ Edeflam r Et ]p)); dest_conj_disj_exist.
    1: generalize EP; EP_ind_unsafe IH EP; simpl; auto.
    now repeat rewrite H1.
Qed.

(* hole_scope disregards Epars not in the hole scope *)
Lemma hole_scope_of_fill_Epar : 
  forall Et EP P m n, 
    is_hole_scope_at_top_proc EP = false ->
    hole_scope (Et <=<[ Epar EP P ]) = hole_scope (Ebag m n EP).
Proof.
  enough (forall EP EP' P m1 n1 m2 n2 EP_acc Et_trav,
          is_hole_scope_at_top_proc EP' = false ->
          (let (_, e0) := split_hole_scope_builder
                              (EP <=<[ Epar EP' P ]p) EP_acc Et_trav in
          match e0 with
          | Edeflam _ Et_lam => Et_lam
          | _ => Ebag m1 n1 (EP <=<[ Epar EP' P]p)
          end) =
          (let (_, e0) := split_hole_scope_builder EP' Ehol (Ebag m2 n2 Ehol) in
          match e0 with
          | Edeflam _ Et_lam => Et_lam
          | _ => Ebag m2 n2 EP'
          end)).
  1: intros; unfold hole_scope; destruct Et; simpl; now apply H.
  EP_ind_unsafe IH EP; simpl; intros.
  - remember (build_not_hs_correct EP' H); clear Heqe.
    dest_conj_disj_exist.
    now repeat rewrite H2.
  - rewrite <- (IH EP EP' P m1 n1 m2 n2 (Edeflam H (Ebag H1 H0 Ehol))
                    (Et_trav <=<[ EP_acc])); eauto.
    destruct (build_not_hs_correct (EP <=<[ Epar EP' P ]p)); auto.
    + generalize EP; EP_ind_unsafe IH EP; simpl; auto.
    + dest_conj_disj_exist.
      now repeat rewrite H5.
  - rewrite <- (IH EP EP' P m1 n1 m2 n2 
                    (EP_acc <=<[ Epar Ehol H2 ]p) Et_trav); eauto.
    destruct (build_not_hs_correct (EP <=<[ Epar EP' P ]p)); auto.
    + generalize EP; EP_ind_unsafe IH EP; simpl; auto.
    + dest_conj_disj_exist.
      now repeat rewrite H3.
Qed.



(* EC Renaming preserves hole-scopedness *)
Lemma ren_pres_hs_proc :
  forall EP n n' (R : ren n n'),
    is_hole_scope_at_top_proc (rename_rvar_EC_proc R EP) =
        is_hole_scope_at_top_proc EP.
Proof.
  induction EP; simpl; intros; auto.
Qed.


(* EC Renaming does not rely on the bounds of the renaming *)
Lemma rename_rvar_EC_proc_indep :
  forall n1 n1' n2 n2' (R1 : ren n1 n1') (R2 : ren n2 n2'),
    R1 = R2 ->
      rename_rvar_EC_proc R1 = rename_rvar_EC_proc R2.
Proof.
  intros. apply functional_extensionality.
  induction x; simpl; intros.
  - auto.
  - rewrite H; auto.
  - erewrite IHx; eauto. 
    erewrite rename_rvar_ind_proc; eauto.
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



(* Lemma wf_EC_weaken_hs_vars :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall m_new n_new,
        wf_EC_term m n (m_hol + m_new) (n_hol + n_new)
            (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) Et)
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall m_new n_new,
          (is_hole_scope_at_top_proc EP = true ->
            wf_EC_proc (m + m_new) (n + n_new)
                (m_hol + m_new) (n_hol + n_new)
                (G ⊗ zero m_new) (D ⊗ zero n_new)
                (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) EP)
      /\ (is_hole_scope_at_top_proc EP = false ->
            wf_EC_proc m n (m_hol + m_new) (n_hol + n_new)
                G D (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) EP)). *)

Lemma wf_EC_weaken_vars_hs :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall m_new n_new,
        wf_EC_term m n (m_hol + m_new) (n_hol + n_new)
            (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) Et)
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall m_new n_new,
          (is_hole_scope_at_top_proc EP = true ->
            wf_EC_proc (m + m_new) (n + n_new)
                (m_hol + m_new) (n_hol + n_new)
                (G ⊗ zero m_new) (D ⊗ zero n_new)
                (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) EP)
      /\ (is_hole_scope_at_top_proc EP = false ->
            wf_EC_proc m n (m_hol + m_new) (n_hol + n_new)
                G D (G_hol ⊗ zero m_new) (D_hol ⊗ zero n_new) EP)).
Proof.
  apply wf_EC_ind; simpl; intros.
  (* Ebag *)
  - econstructor; eauto.
    destruct (H m_new n_new); clear H.
    destruct (is_hole_scope_at_top_proc EP) eqn:HS.
    + clear H1. admit.
    + auto.
  - split; intros; try discriminate; clear H.
    econstructor; try rewrite HG; try rewrite HD; reflexivity.
  - split; intros; try discriminate; clear H0.
    econstructor; auto.
  - split; intros.
    + econstructor.
      1: now apply H.
      1: eapply wf_weaken_free_vars; eauto.
      all: rewrite sum_app_zero.
      1: now rewrite HG.
      1: now rewrite HD.
    + econstructor; eauto. now apply H.
Admitted.



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



(* A wf hole scope has equal hole and scope variable bounds. *)
Lemma wf_hs_var_bounds_eq :
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

Lemma wf_hs_var_bounds_eq_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> is_hole_scope_at_top Et = true ->
  m_hol = (get_fvars_Et Et) + m  /\ n_hol = (get_rvars_Et Et) + n.
Proof. apply wf_hs_var_bounds_eq. Qed.
Lemma wf_hs_var_bounds_eq_proc : forall m n m_hol n_hol G D G_hol D_hol EP,
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> is_hole_scope_at_top_proc EP = true ->
  m_hol = m  /\ n_hol = n.
Proof. apply wf_hs_var_bounds_eq. Qed.



(* The context for a hole scope includes the resources 
    of the hole context *)
Lemma min_rvar_hs_EC_wf :
  forall EP m n m_hol n_hol G D G_hol D_hol r, 
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
    is_hole_scope_at_top_proc EP = true ->
    r < n_hol ->
    D r >= D_hol r.
Proof.
  induction EP; simpl; intros; inversion H; existT_eq; subst.
  - unfold ctxt_eq in HD. rewrite HD; auto.
  - discriminate.
  - apply wf_hs_var_bounds_eq in H; auto.
    destruct H; subst.
    unfold ctxt_eq in HD. rewrite HD; auto.
    eapply IHEP in WFP1; eauto.
    rewrite sum_correct; lia.
Qed.



(* n_hol and m_hol are greater or equal to the bound variables at hole scope *)
Lemma wf_hs_vars_correct :
    (forall m n m_hol n_hol G_hol D_hol Et,
      wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        bound_fvars_at_hole_scope Et <= m_hol /\
        bound_rvars_at_hole_scope Et <= n_hol)
/\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
      (is_hole_scope_at_top_proc EP = true /\ m = m_hol /\ n = n_hol) \/
      (forall m' n',
        is_hole_scope_at_top_proc EP = false /\
        bound_fvars_at_hole_scope (Ebag m' n' EP) <= m_hol /\
        bound_rvars_at_hole_scope (Ebag m' n' EP) <= n_hol)).
Proof. 
  unfold bound_fvars_at_hole_scope, bound_rvars_at_hole_scope, apply_at_hole_scope.
  apply wf_EC_ind; intros.
  (* Ebag by IH *)
  - dest_conj_disj_exist; subst.
    + unfold hole_scope. rewrite inv_hole_scope_at_top; auto. simpl; lia.
    + apply H.
  (* Ehol by construction *)
  - auto.
  (* Edeflam by IH *)
  - right; intros.
    assert (is_hole_scope_at_top (Ebag m' n' (Edeflam r Et)) = false) by auto.
    apply inv_hole_scope_not_at_top in H0; dest_conj_disj_exist.
    assert ((Ebag m' n' (Edeflam r Et)) = (Ebag m' n' Ehol) <=<[ Edeflam r Et]) by auto.
    rewrite H4. rewrite hole_scope_of_fill_Edeflam. auto.
  (* Epar by IH and casing on hs at top *)
  - destruct H.
    + auto.
    + right. intros; specialize H with m' n'; dest_conj_disj_exist.
      split; auto.
      unfold hole_scope in *; simpl in *.
      apply build_not_hs_correct in H; dest_conj_disj_exist.
      repeat rewrite H3 in *; auto.
Qed.



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



Lemma hole_scope_wf :
  forall Et m n m_hol n_hol G_hol D_hol,
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    wf_EC_term (m_hol - bound_fvars_at_hole_scope Et)
               (n_hol - bound_rvars_at_hole_scope Et)
                m_hol n_hol G_hol D_hol (hole_scope Et).
Proof.
  intros.
  unfold bound_fvars_at_hole_scope, bound_rvars_at_hole_scope,
      apply_at_hole_scope, hole_scope.
  destruct (is_hole_scope_at_top Et) eqn:HS.
  - rewrite inv_hole_scope_at_top; auto.
    assert (H0 := H); apply wf_hs_var_bounds_eq_term in H0; auto.
    destruct H0; subst.
    assert (get_fvars_Et Et + m - get_fvars_Et Et = m) by lia;
        assert (get_rvars_Et Et + n - get_rvars_Et Et = n) by lia.
    now rewrite H0, H1.
  - apply inv_hole_scope_not_at_top in HS; dest_conj_disj_exist.
    rewrite H2; clear H2; subst.
    eapply inv_EC_fill_wf in H; dest_conj_disj_exist; clear H0.
    inversion H; existT_eq; subst.
    assert (H0 := WFT); apply wf_hs_var_bounds_eq_term in H0; auto.
    destruct H0; subst.
    assert (get_fvars_Et x0 + x2 - get_fvars_Et x0 = x2) by lia;
        assert (get_rvars_Et x0 + 1 - get_rvars_Et x0 = 1) by lia.
    now rewrite H0, H2.
Qed.



(* Removing a resource requirement from the hole (changing 2 uses to 0 uses) 
   preserves EC well-formedness *)
Lemma rem_hole_rvar_EC_wf : 
  (forall m n m_hol n_hol G_hol D_hol Et,
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall r D_hol',
      D_hol ≡[n_hol] D_hol' ⨥ n_hol[r ↦ 2] ->
      r < n_hol ->
      D_hol' r = 0 ->
    wf_EC_term m n m_hol n_hol G_hol D_hol' Et)
  /\  
  (forall m n m_hol n_hol G D G_hol D_hol EP,
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
    forall r D_hol',
      D_hol ≡[n_hol] D_hol' ⨥ n_hol[r ↦ 2] ->
      r < n_hol ->
      D_hol' r = 0 ->
        (is_hole_scope_at_top_proc EP = false /\
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol' EP)
      \/
        (is_hole_scope_at_top_proc EP = true /\
        exists D',
          D ≡[n] D' ⨥ n[r ↦ 2] /\
        wf_EC_proc m n m_hol n_hol G D' G_hol D_hol' EP)).
Proof.
  apply wf_EC_ind; intros.
  (* Ebag *)
  - destruct (H r D_hol' H0 H1 H2); clear H. 
    + destruct H3; econstructor; eauto.
    + destruct H3 as (H3 & D' & H4 & H5).
      assert (H6 := H5); apply wf_hs_var_bounds_eq_proc in H5; auto.
      destruct H5; subst.
      symmetry in H0; rewrite sum_commutative in H0.
      apply delta_sum_ctxt_eq_inv in H0. destruct H0 as (D0 & -> & H).
      apply sum_app_inv_ctxt in H4. 
      destruct H4 as (D1 & D1r & D2 & D2r & HD1 & HD2 & HD3 & HD4).
      rewrite H, <- HD3 in WFP; clear H.
      apply delta_ctxt_eq_app_inv in HD2. 
      apply wf_Ebag with (G := G) (D := D1); auto; subst.
      * intros. unfold ctxt_eq in HD3; specialize HD3 with x.
        rewrite sum_correct in HD3. 
        specialize UD with x. rewrite <- HD3 in UD; auto.
        destruct HD2; destruct H0; clear H3.
        all: unfold ctxt_eq in H0; specialize H0 with x.
        all: rewrite <- H0 in UD; try lia; clear H0.
        all: destruct (UD H); unfold delta, zero, flat_ctxt in H0.
        all: destruct (lt_dec r n); destruct (Nat.eq_dec r x); lia.
      * rewrite <- HD4. rewrite HD1 in H6.
        destruct HD2; destruct H; clear H.
        -- rewrite <- H0, sum_zero_r. assumption.
        -- destruct (Nat.eq_dec n' 0); subst.
           ++ simpl in *. rewrite Nat.add_0_r in *. 
           rewrite (ctxt_app_l D1 (D2 ⨥ D2r)).
           rewrite (ctxt_app_l D1 D2) in H6. assumption.
           ++ assert (1 > 1).
              { rewrite <- H0 in HD4. unfold flat_ctxt, ctxt_eq in HD4.
                rewrite <- (HD4 (r - n)) at 1; try lia.
                unfold delta, sum. 
                destruct (lt_dec (r - n) n'); destruct (Nat.eq_dec (r - n) (r - n)); lia. }
              lia.
  (* Ehol *)
  - right; split; auto. exists D_hol'; repeat split; auto.
    + transitivity D_hol; auto.
    + constructor; auto; reflexivity.
  (* Elamdef *)
  - left. split; auto. constructor; auto. eapply H; eauto.
  (* Epar *)
  - destruct (H r D_hol'); auto; dest_conj_disj_exist.
    + left; split; auto. econstructor; eauto.
    + right; split; auto.
      exists (x ⨥ D2); repeat split.
      * rewrite <- sum_assoc, (sum_commutative D2), sum_assoc. 
        rewrite HD; rewrite H4. reflexivity.
      * econstructor; eauto; reflexivity.
Qed.

Lemma rem_hole_rvar_EC_wf_Et : 
  forall m n m_hol n_hol G_hol D_hol Et,
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall r D_hol',
      D_hol ≡[n_hol] D_hol' ⨥ n_hol[r ↦ 2] ->
      r < n_hol ->
      D_hol' r = 0 ->
    wf_EC_term m n m_hol n_hol G_hol D_hol' Et.
Proof. apply rem_hole_rvar_EC_wf. Qed.



Lemma rename_rvar_pres_wf_hs_EC :
  forall EP m n m_hol n_hol G D G_hol D_hol,
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
    is_hole_scope_at_top_proc EP = true ->
  forall (R : ren n_hol n_hol),
    wf_ren R ->
    wf_EC_proc m n m_hol n_hol G (lctxt_rename R D)
        G_hol (lctxt_rename R D_hol) (rename_rvar_EC_proc R EP).
Proof.
  induction EP; simpl; intros.
  - inversion H; existT_eq; subst.
    econstructor; eauto.
    now apply lctxt_rename_ctxt_eq.
  - discriminate.
  - inversion H; existT_eq; subst.
    apply wf_hs_var_bounds_eq_proc in H; auto.
    destruct H; subst; auto.
    econstructor; eauto.
    + apply rename_rvar_pres_wf; eauto.
    + rewrite <- lctxt_rename_sum.
      now apply lctxt_rename_ctxt_eq.
Qed.






Definition wf_hs_fun f Et m_hol n_hol G_hol D_hol 
                          m_hol' n_hol' G_hol' D_hol' :=
  forall m n,
    is_hole_scope_at_top Et = true ->
    wf_EC_term m n m_hol n_hol G_hol D_hol  Et ->
    wf_EC_term m n m_hol' n_hol' G_hol' D_hol' (f Et).

Lemma wf_hs_fun_hole_scope :
  forall f Et m_hol n_hol G_hol D_hol 
              m_hol' n_hol' G_hol' D_hol',
      let f_hs := mutate_under_hole_scope f in
      let f_ub := fun Et : EC_term =>
              match Et with Ebag m n EP => Ebag m n (f EP) end in
    wf_hs_fun f_hs (hole_scope Et) m_hol n_hol G_hol D_hol 
                      m_hol' n_hol' G_hol' D_hol' ->
    wf_hs_fun f_ub (hole_scope Et) m_hol n_hol G_hol D_hol 
                                   m_hol' n_hol' G_hol' D_hol'.
Proof.
  intros; unfold f_hs, f_ub in *; clear f_hs f_ub.
  unfold wf_hs_fun in *; intros.
  unfold mutate_under_hole_scope, mutate_hole_scope in H.
  rewrite inv_hole_scope_at_top in H; auto.
Qed.



(* EC renaming preserves well-formedness *)
Lemma mutate_hole_scope_wf :
    (forall m n m_hol n_hol G_hol D_hol Et,
      wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall f m_hol' n_hol' G_hol' D_hol',
      wf_hs_fun f (hole_scope Et) m_hol n_hol G_hol D_hol 
                    m_hol' n_hol' G_hol' D_hol' ->
      wf_EC_term m n m_hol' n_hol' G_hol' D_hol'
          (mutate_hole_scope f Et))
/\  (forall m n m_hol n_hol G D G_hol D_hol EP,
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
    forall f m_hol' n_hol' G_hol' D_hol',
      is_hole_scope_at_top_proc EP = false ->
      wf_hs_fun f (hole_scope (Ebag 0 0 EP)) m_hol n_hol G_hol D_hol 
                    m_hol' n_hol' G_hol' D_hol' ->
      wf_EC_proc m n m_hol' n_hol' G D G_hol' D_hol'
          (mutate_hole_scope_proc f EP)).
Proof.
  apply wf_EC_ind; simpl; intros.
  (* Ebag *)
  - clear H; unfold mutate_hole_scope; unfold hole_scope in H0.
    destruct (is_hole_scope_at_top (Ebag m n EP)) eqn:HS.
    + rewrite inv_hole_scope_at_top in *; auto.
      eapply H0; auto.
      econstructor; eauto.
    + apply inv_hole_scope_not_at_top in HS; dest_conj_disj_exist.
      rewrite H2 in *; clear H2; auto.
      destruct x; simpl in *.
      injection H; clear H; intros; subst.
      apply inv_EC_fill_wf in WFP; dest_conj_disj_exist.
      econstructor; eauto.
      eapply EC_fill_wf_pres_proc; eauto.
      inversion H; clear H; existT_eq; subst.
      econstructor; eauto.
  (* Ehol *)
  - discriminate.
  (* Edeflam *)
  - clear H0 WFT.
    replace (Ebag 0 0 (Edeflam r Et)) with 
        (Ebag 0 0 Ehol <=<[ Edeflam r Et ]) in H1 by auto.
    rewrite hole_scope_of_fill_Edeflam in H1. 
    assert (H0 := H1); apply H in H0; clear H.
    unfold mutate_hole_scope_proc, mutate_hole_scope in *.
    destruct Et; simpl in *.
    destruct (is_hole_scope_at_top_proc EP) eqn:HS.
    + rewrite build_hs_correct_Edeflam; auto; simpl.
      rewrite build_hs_correct_Ehol_Epar in H0; auto.
      econstructor; eauto.
    + apply build_not_hs_correct in HS; dest_conj_disj_exist.
      subst; rewrite H3 in *; clear H3; simpl in *.
      econstructor; eauto.
  (* Epar *)
  - replace (Ebag 0 0 (Epar EP P)) with 
        (Ebag 0 0 Ehol <=<[ Epar EP P ]) in H1 by auto.
    rewrite hole_scope_of_fill_Epar with (m := 0) (n := 0) in H1; auto. 
    apply H in H1; auto.
    apply build_not_hs_correct in H0; dest_conj_disj_exist.
    unfold mutate_hole_scope_proc, mutate_hole_scope in *; simpl in *.
    rewrite H3 in *; clear H3; subst; simpl in *.
    econstructor; eauto.
Qed.



