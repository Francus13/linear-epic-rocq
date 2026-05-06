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



Fixpoint EP_size EP :=
  match EP with
  | Ehol => 0
  | Edeflam _ (Ebag _ _ EP') => 1 + EP_size EP'
  | Epar EP' _ => 1 + EP_size EP'
  end.

Definition EP_lt EP1 EP2 := lt (EP_size EP1) (EP_size EP2).

Lemma EP_lt_wf : well_founded EP_lt.
Proof.
  unfold well_founded; intros. constructor; intros.
  unfold EP_lt in H. induction a.
  - inversion H.
  - destruct Et. simpl in H.
Admitted.

(* Inductive EC_lt_strict : (EC_term + EC_proc) -> (EC_term + EC_proc) -> Prop :=
| Ebag_lt : forall EP m n, 
                EC_lt_strict (inr EP) (inl (Ebag m n EP))
| Edeflam_lt : forall Et r, 
                EC_lt_strict (inl Et) (inr (Edeflam r Et))
| Epar_lt : forall EP P,
                EC_lt_strict (inr EP) (inr (Epar EP P)).

Definition EC_lt := clos_trans _ EC_lt_strict.

Lemma EC_lt_wf_helper :
    (forall Et, Acc EC_lt (inl Et))
/\  (forall EP, Acc EC_lt (inr EP)).
Proof.
  apply EC_ind; intros; constructor; intros.
  (* Ebag, Edeflam, and Epar are the same *)
  - remember (inl (Ebag m n EP)) as x; induction H0; subst.
    + inversion H0; auto.
    + apply (Acc_inv (IHclos_trans2 eq_refl)). apply H0_.
  (* Ehol is a base case *)
  - exfalso. remember (inr (Ehol)) as x; induction H; subst.
    + inversion H.
    + auto.
  - remember (inr (Edeflam r Et)) as x; induction H0; subst.
    + inversion H0; auto.
    + apply (Acc_inv (IHclos_trans2 eq_refl)). auto.
  - remember (inr (Epar EP P)) as x; induction H0; subst.
    + inversion H0; auto.
    + apply (Acc_inv (IHclos_trans2 eq_refl)). auto.
Qed.

Lemma EC_lt_wf : well_founded EC_lt.
Proof. unfold well_founded. intros; destruct a; apply EC_lt_wf_helper. Qed.
Definition EC_lt_ind := well_founded_induction EC_lt_wf.


Definition EP_lt EP1 := (EC_lt (inr EP1)) ∘ inr.
Lemma EP_lt_wf : well_founded EP_lt.
unfold well_founded, EP_lt. intros. constructor; intros.
Admitted. *)



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

(* Projects the EC_term components *)
Definition get_fvars_Et Et := match Et with Ebag m _ _ => m end.
Definition get_rvars_Et Et := match Et with Ebag _ n _ => n end.
Definition get_proc_Et Et := match Et with Ebag _ _ EP => EP end.



(* Returns true if the hole is not underneath a lambda binding.
   Otherwise returns false. *)
Fixpoint is_hole_scope_at_top Et := is_hole_scope_at_top_proc (get_proc_Et Et)
with is_hole_scope_at_top_proc EP := 
  match EP with
  | Ehol => true
  | Edeflam _ _ => false
  | Epar EP' _ => is_hole_scope_at_top_proc EP'
  end.



(* HELPER FUNCTION! for split_hole_scope.
 *)
Fixpoint split_hole_scope_builder (EP EP_acc : EC_proc) 
                                  (Et_trav : EC_term) : EC_term * EC_proc :=
  match EP with
  | Ehol => match EP_acc with
            | Edeflam _ _ => (Et_trav, EP_acc)
            | _           => (Et_trav <=<[ EP_acc ], Ehol)
            end
  | Edeflam r (Ebag m n EP') => split_hole_scope_builder EP' 
                                  (Edeflam r (Ebag m n Ehol)) 
                                  (Et_trav <=<[ EP_acc ])
  | Epar EP' P => split_hole_scope_builder EP' 
                    (EP_acc <=<[ Epar Ehol P ]p) Et_trav
  end.


(* Applies pop_EC_scope until the "hole scope" is reached,
      separating the hole scope from the rest of the EC.
   Given an EC, returns a pair whose 
      first element is the EC with the hole scope replaced by a hole
      and second element is the hole scope.
   The invariants of pop_EC_scope are also held by split_hole_scope. *)
Definition split_hole_scope (Et : EC_term) : EC_term * EC_proc :=
  match Et with
  | Ebag m n EP => split_hole_scope_builder EP Ehol (Ebag m n Ehol)
  end.


Definition hole_scope Et := 
  match split_hole_scope Et with 
  | (_, Edeflam _ Et_lam) => Et_lam
  | _ => Et   (* Only reachable when hole is at top scope *)
  end.



(* Applies a funciton f at the hole scope, returning the result *)
Definition apply_at_hole_scope {X} (f : EC_term -> X) := 
  f ∘ hole_scope.

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



Ltac split_hole_scope_generalize EP :=
    let Et := fresh in
  intro Et; destruct Et as [m n EP]; simpl;
  generalize (Ebag m n Ehol) as Et_trav; generalize Ehol as EP_acc;
  generalize dependent EP.

Ltac EP_ind_unsafe IH EP :=
  match goal with [|- forall x, @?P x] => refine (fix IH EP: _ := _) end;
    let r := fresh in let n := fresh in let m := fresh in let P := fresh in
  destruct EP as [ | r [ m n EP ] | EP P ].


Lemma inv_split_hole_scope :
      (forall (Et : EC_term),
          (exists Et_top,
            split_hole_scope Et = (Et_top, Ehol))
      \/  (exists Et_top r Et_rest,
            split_hole_scope Et = (Et_top, Edeflam r Et_rest))).
Proof.
  remember Ehol as x; split_hole_scope_generalize EP; subst.
  EP_ind_unsafe IH EP; simpl; intros; auto.
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


Lemma split_hole_scope_builder_Edeflam_acc :
  forall EP r Et_acc Et_trav Et_top,
    split_hole_scope_builder EP (Edeflam r Et_acc) Et_trav <> (Et_top, Ehol).
Proof. 
  EP_ind_unsafe IH EP; simpl; intros; auto.
  discriminate.
Qed.

Lemma inv_split_hole_scope_Ehol_eq :
  forall (Et Et_top : EC_term),
    split_hole_scope Et = (Et_top, Ehol) ->
    Et_top = Et.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term),
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Ehol) ->
            Et_top = Et_trav <=<[ EP_acc <=<[ EP ]p ]); try apply H.
  EP_ind_unsafe IH EP; simpl; intros; shift_fill_left.
  - destruct EP_acc; simpl.
    all: injection H; intros; subst; repeat rewrite shift_Ehol_fill_proc; auto.
    discriminate H0.
  - now apply split_hole_scope_builder_Edeflam_acc in H2.
  - apply IH; auto.
Qed.


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
  - reflexivity.
  - now apply split_hole_scope_builder_Edeflam_acc in H2.
  - eapply IH; apply H.
Qed.

Lemma inv_split_hole_scope_Edeflam :
  forall (Et Et_top : EC_term) r Et_rest,
    split_hole_scope Et = (Et_top, Edeflam r Et_rest) ->
    is_hole_scope_at_top Et = false.
Proof.
  intro Et; destruct Et as [m n EP0]; simpl.
  enough (forall (EP EP_acc : EC_proc) (Et_trav Et_top : EC_term) r Et_rest,
            split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_rest) ->
            is_hole_scope_at_top_proc EP_acc = true ->
            is_hole_scope_at_top_proc EP = false); try (intros; eapply H; eauto).
  EP_ind_unsafe IH EP; simpl; intros.
  - destruct EP_acc; try discriminate H. discriminate H0.
  - reflexivity.
  - eapply IH; try apply H. 
    apply meet_hole_scope_at_top_proc; auto.
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
  - econstructor; eauto. apply H; auto; reflexivity.
  - econstructor; do 2 (eapply transitivity; eauto); symmetry; auto.
  - econstructor; auto; eapply transitivity; eauto; symmetry; auto.
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
    (* Most cases are immediate or by IH *)
  all: try solve [
    try econstructor; try apply WFP2; try rewrite HG, HD; auto
  ].
    (* Edeflam *)
  - simpl. apply wf_def with (D' := zero n); auto.
    + rewrite sum_zero_r. auto.
    + apply wf_lam; auto. reflexivity.
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
    (* All cases are immediate or by IH *)
  all: try econstructor; try apply WFP2; simpl; 
        try rewrite HG, HD; simpl; auto.
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



Ltac finish_by_IH_inv_prem H WF := 
      apply H in WF;
      destruct WF as (m_hol & n_hol & G_hol & D_hol & WF1 & WF2);
      exists m_hol, n_hol, G_hol, D_hol; split; auto;
      econstructor; eauto.

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
  apply EC_ind; intros.
    (* Ebag *)
  - inversion H0; subst. finish_by_IH_inv_prem H WFP.
    (* Ehol *)
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
  apply EC_ind; intros.
    (* Ebag *)
  - inversion H0; existT_eq; subst. finish_by_IH_inv_prem H WFP.
    (* Ehol *)
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
  (* Ebag *)
  - destruct (H r); auto. destruct H1. apply H2. 
    unfold ctxt_app, flat_ctxt.
    destruct (lt_dec r n); auto. destruct (UD r); lia.
  (* Ehol *)
  - rewrite <- HD; auto.
  (* Elamdef *)
  - auto.
  (* Epar *)
  - destruct (H r); auto. destruct H1; subst.
    right; split; auto; intros.
    rewrite HD in H1; auto. unfold sum in H1; lia.
Qed.



(* Preservation Lemmas about EC Functions *)

(* If an EC is wf, then splitting it at its hole scope gives
    two wf ECs (the accumulated Et_top and the hole scope Et_hs) *)
Lemma split_hole_scope_pres :
  forall Et m n m_hol n_hol G_hol D_hol,
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
  forall Et_top r Et_hs,
    split_hole_scope Et = (Et_top, Edeflam r Et_hs) ->
    exists m_top n_top,
        wf_EC_term m n m_top n_top (zero m_top) (one n_top r) Et_top
    /\  wf_EC_term m_top 1 m_hol n_hol G_hol D_hol Et_hs.
Proof.
  intro Et; destruct Et as [m0 n0 EP0]; simpl.
  enough (
      forall EP EP_acc Et_trav Et_top r Et_hs m n m_hol n_hol G_hol D_hol,
        wf_EC_term m n m_hol n_hol G_hol D_hol (Et_trav <=<[ EP_acc ] <=<[ EP ]) ->
        split_hole_scope_builder EP EP_acc Et_trav = (Et_top, Edeflam r Et_hs) ->
        exists m_top n_top,
            wf_EC_term m n m_top n_top (zero m_top) (one n_top r) Et_top
        /\  wf_EC_term m_top 1 m_hol n_hol G_hol D_hol Et_hs
    ).
  1: intros; eapply H; eauto; simpl; auto.
  EP_ind_unsafe IH EP; simpl; intros.
  - destruct EP_acc; try discriminate H0.
    injection H0; intros; subst.
    rewrite shift_Ehol_fill_term in H.
    apply inv_EC_fill_wf in H. dest_conj_disj_exist.
    inversion H; existT_eq; subst.
    rewrite HG, HD in H1. eauto.
  - rewrite shift_Edeflam_fill_term in H2.
    eapply IH; eauto.
  - rewrite shift_Epar_fill_term in H.
    repeat rewrite commute_EC_fill_term in H.
    rewrite <- commute_EC_fill_proc, <- commute_EC_fill_term in H.
    eapply IH; eauto.
Qed.


