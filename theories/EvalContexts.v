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
  induction a.
  - inversion H.
  -
Qed.

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



(* Gives the number of lambda bindings encountered when traversing 
      to the hole (i.e. how many scopes deep the hole is) *)
Fixpoint hole_depth Et := hole_depth_proc (get_proc_Et Et)
with hole_depth_proc (EP : EC_proc) : nat :=
  match EP with
  | Ehol => 0
  | Edeflam _ Et => 1 + hole_depth Et
  | Epar EP' _ => hole_depth_proc EP'
  end.

Definition is_hole_scope_at_top := (eqb 0) ∘ hole_depth.
Definition is_hole_scope_at_top_proc := (eqb 0) ∘ hole_depth_proc.



(* HELPER FUNCTION! ACC is the proof of accessibility for Et_cur 
    (i.e. that the hole_depth of Et_cur decreases at each call) *)
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

Lemma inv_split_hole_scope :
      (forall (Et : EC_term),
          (exists Et_top,
            split_hole_scope Et = (Et_top, Ehol))
      \/  (exists Et_top r Et_rest,
            split_hole_scope Et = (Et_top, Edeflam r Et_rest))).
Proof.
  intros. destruct Et; simpl.
  induction (@inr EC_term EC_proc EP) using EC_lt_ind. ; simpl; intros.
  - left; eauto.
  - right; destruct Et.
Qed.







Lemma inv_pop_EC_scope :
      (forall (Et : EC_term),
          (exists Et_top,
            pop_EC_scope Et = (Et_top, Ehol))
      \/  (exists Et_top r Et_rest,
            pop_EC_scope Et = (Et_top, Edeflam r Et_rest)))
  /\  (forall (EP : EC_proc),
          (exists EP_top,
            pop_EC_scope_proc EP = (EP_top, Ehol))
      \/  (exists EP_top r Et_rest,
            pop_EC_scope_proc EP = (EP_top, Edeflam r Et_rest))).
Proof.
  apply EC_ind; intros.
  - destruct H as [[EP_top H] | [EP_top [r [Et_rest H]]]].
    + left; eexists; simpl. rewrite H; auto.
    + right; repeat eexists; simpl. rewrite H; auto.
  - left; eexists; simpl; eauto.
  - right; repeat eexists.
  - destruct H as [[EP_top H] | [EP_top [r [Et_rest H]]]].
    + left; eexists; simpl. rewrite H; auto.
    + right; repeat eexists; simpl. rewrite H; auto.
Qed.

Lemma inv_pop_EC_scope_term : 
  forall (Et : EC_term),
      (exists Et_top,
        pop_EC_scope Et = (Et_top, Ehol))
  \/  (exists Et_top r Et_rest,
        pop_EC_scope Et = (Et_top, Edeflam r Et_rest)).
Proof. apply inv_pop_EC_scope. Qed.


Lemma inv_pop_EC_scope_Ehol_eq :
      (forall (Et Et_top : EC_term),
        pop_EC_scope Et = (Et_top, Ehol) ->
        Et = Et_top)
  /\  (forall (EP EP_top : EC_proc),
        pop_EC_scope_proc EP = (EP_top, Ehol) ->
        EP = EP_top).
Proof.
  apply EC_ind; intros.
  - unfold pop_EC_scope in H0. destruct (pop_EC_scope_proc EP) eqn:popEQ.
    injection H0; intros; subst. 
    rewrite (H e); auto.
  - unfold pop_EC_scope_proc in H. injection H; auto.
  - unfold pop_EC_scope_proc in H0. 
    injection H0; intros; subst; auto.
  - unfold pop_EC_scope_proc in H0. fold pop_EC_scope_proc in H0.   (* FRAN *)
    destruct (pop_EC_scope_proc EP) eqn:popEQ.
    injection H0; intros; subst. 
    rewrite (H e); auto.
Qed.

Lemma inv_pop_EC_scope_Ehol_hs :
      (forall (Et Et_top : EC_term),
        pop_EC_scope Et = (Et_top, Ehol) ->
        is_hole_scope_at_top Et = true)
  /\  (forall (EP EP_top : EC_proc),
        pop_EC_scope_proc EP = (EP_top, Ehol) ->
        is_hole_scope_at_top_proc EP = true).
Proof.
  unfold is_hole_scope_at_top, is_hole_scope_at_top_proc, compose. 
  apply EC_ind; intros.
  all : solve [
    simpl in *; auto;
    try discriminate H0;  (* For Elamdef case, which cannot return Ehol as 2nd elem *)
    destruct (hole_depth_proc EP); auto; destruct (pop_EC_scope_proc EP) eqn:popEQ;
    injection H0; intros; subst; ediscriminate H; auto
  ].
Qed.

Lemma inv_pop_EC_scope_Edeflam :
      (forall (Et Et_top : EC_term) r Et_rest,
        pop_EC_scope Et = (Et_top, Edeflam r Et_rest) ->
        is_hole_scope_at_top Et = false)
  /\  (forall (EP EP_top : EC_proc) r Et_rest,
        pop_EC_scope_proc EP = (EP_top, Edeflam r Et_rest) ->
        is_hole_scope_at_top_proc EP = false).
Proof.
  unfold is_hole_scope_at_top, is_hole_scope_at_top_proc, compose. 
  apply EC_ind; intros.
  all : solve [
    simpl in *; auto;
    try discriminate H;  (* For Ehol case, which cannot return Edeflam as 2nd elem *)
    destruct (hole_depth_proc EP); auto; destruct (pop_EC_scope_proc EP) eqn:popEQ;
    injection H0; intros; subst; ediscriminate H; auto
  ].
Qed.

Lemma inv_pop_EC_scope_Epar :
  (forall Et Et_top EP P,
    pop_EC_scope Et <> (Et_top, Epar EP P)).
Proof.
  unfold not; intros.
  destruct (inv_pop_EC_scope_term Et); dest_conj_disj_exist.
  all: rewrite H0 in H; discriminate.
Qed.



Lemma inv_split_hole_scope_builder :
  forall Et_cur r Et_acc ACC,
    exists Et_outer r' Et_hs,
    split_hole_scope_builder r Et_acc Et_cur ACC = 
    (Et_outer, Edeflam r' Et_hs).
Proof.
  induction Et_cur using (well_founded_induction hole_depth_lt_wf).
  destruct Et_cur; destruct EP; intros; destruct ACC.
  - simpl. now repeat eexists.
  - apply (H Et). unfold hole_depth_lt; auto.
  - unfold split_hole_scope_builder. fold split_hole_scope_builder.
    generalize (pop_EC_scope_reduces_hole_depth (Ebag m n (Epar EP P)))
        as pf_HD.
    destruct (inv_pop_EC_scope_term (Ebag m n (Epar EP P))).
    all: dest_conj_disj_exist; rewrite H0; clear H0; intros.
    + now repeat eexists.
    + apply (H x1 (pf_HD x1 x x0 eq_refl) _ _ _).
Qed.

Lemma inv_split_hole_scope_builder_Ehol_Epar :
    (forall Et_cur r Et_acc ACC Et_outer,
      split_hole_scope_builder r Et_acc Et_cur ACC <> (Et_outer, Ehol))
/\  (forall Et_cur r Et_acc ACC Et_outer EP P,
      split_hole_scope_builder r Et_acc Et_cur ACC <> (Et_outer, Epar EP P)).
Proof.
  split; intros.
  all: destruct (inv_split_hole_scope_builder Et_cur r Et_acc ACC) 
          as (Et_outer' & r' & Et_hs & H).
  all: rewrite H; discriminate.
Qed.

Lemma inv_split_hole_scope_Ehol_eq :
  forall (Et Et_top : EC_term),
    split_hole_scope Et = (Et_top, Ehol) ->
    Et = Et_top.
Proof.
  intro Et; destruct (inv_pop_EC_scope_term Et); dest_conj_disj_exist.
  all: unfold split_hole_scope; rewrite H; intros.
  - injection H0; auto.
  - apply inv_split_hole_scope_builder_Ehol_Epar in H0; destruct H0.
Qed.

Lemma inv_split_hole_scope_Ehol_hs :
  forall (Et Et_top : EC_term),
    split_hole_scope Et = (Et_top, Ehol) ->
    is_hole_scope_at_top Et = true.
Proof.
  intro Et; destruct (inv_pop_EC_scope_term Et); dest_conj_disj_exist.
  all: unfold split_hole_scope; rewrite H; intros.
  - eapply inv_pop_EC_scope_Ehol_hs. eauto.
  - apply inv_split_hole_scope_builder_Ehol_Epar in H0. destruct H0.
Qed.

Lemma inv_split_hole_scope_Edeflam :
  forall (Et Et_top : EC_term) r Et_rest,
    split_hole_scope Et = (Et_top, Edeflam r Et_rest) ->
    is_hole_scope_at_top Et = false.
Proof.
  intro Et; destruct (inv_pop_EC_scope_term Et); dest_conj_disj_exist.
  all: unfold split_hole_scope; rewrite H; intros.
  - discriminate H0.
  - eapply inv_pop_EC_scope_Edeflam. eauto.
Qed.

Lemma inv_split_hole_scope_Epar :
  (forall Et Et_top EP P,
    split_hole_scope Et <> (Et_top, Epar EP P)).
Proof.
  unfold not; intros.
  destruct (inv_split_hole_scope Et).
  - destruct H0. rewrite H0 in H; discriminate.
  - destruct H0 as (a & b & c & H0). rewrite H0 in H; discriminate.
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


(* Filling an EC preserves well-formedness *)
Lemma fill_EC_wf_pres :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
        forall (P : proc),
          wf_proc m_hol n_hol G_hol D_hol P ->
        wf_term m n (Et <=[ P ]))
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
        forall (P : proc),
          wf_proc m_hol n_hol G_hol D_hol P ->
        wf_proc m n G D (EP <=[ P ]p)).
Proof.
  apply wf_EC_ind; intros.
    (* Most cases are immediate or by IH *)
  all: try solve [try econstructor; try apply WFP2; try rewrite HG, HD; auto].
    (* Edeflam *)
  - simpl. apply wf_def with (D' := zero n); auto.
    + rewrite sum_zero_r. auto.
    + apply wf_lam; auto. reflexivity.
Qed.

Lemma fill_EC_wf_pres_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> forall (P : proc),
  wf_proc m_hol n_hol G_hol D_hol P -> wf_term m n (Et <=[ P ]).
Proof. apply fill_EC_wf_pres. Qed.
Lemma fill_EC_wf_pres_proc : forall m n m_hol n_hol G D G_hol D_hol EP, 
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> forall (P : proc),
  wf_proc m_hol n_hol G_hol D_hol P -> wf_proc m n G D (EP <=[ P ]p).
Proof. apply fill_EC_wf_pres. Qed.


Lemma drill_term_wf_pres :
  (forall Et P m n,
      wf_term m n (Et <=[ P ]) ->
      exists m_hol n_hol 
        (G_hol : lctxt m_hol) (D_hol : lctxt n_hol),
      wf_proc m_hol n_hol G_hol D_hol P /\
      wf_EC_term m n m_hol n_hol G_hol D_hol Et)
  /\
  (forall EP P m n (G : lctxt m) (D : lctxt n),
      wf_proc m n G D (EP <=[ P ]p) ->
      exists m_hol n_hol 
        (G_hol : lctxt m_hol) (D_hol : lctxt n_hol),
      wf_proc m_hol n_hol G_hol D_hol P /\
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP).
Proof.
  apply EC_ind; intros.
  Ltac drill_by_IH H WF := 
        apply H in WF;
        destruct WF as (m_hol & n_hol & G_hol & D_hol & WF1 & WF2);
        exists m_hol, n_hol, G_hol, D_hol; split; auto;
        econstructor; eauto.
    (* Ebag *)
  - inversion H0; subst. drill_by_IH H WFP.
    (* Ehol *)
  - exists m, n, G, D. split; auto. econstructor; reflexivity.
    (* Edeflam *)
  - inversion H0; inversion WFO; existT_eq; subst. drill_by_IH H WFT.
    rewrite HD, HD0, sum_zero_r; reflexivity.
    (* Epar *)
  - inversion H0; existT_eq; subst. drill_by_IH H WFP1.
Qed.


(* Prove that well-formedness respects context equivalence. *)
Lemma EC_equiv_wf :
(* The first element is trivial, but allows using wf_tpo_ind *)
  (forall m n m_hol n_hol G_hol1 D_hol1 Et,
    wf_EC_term m n m_hol n_hol G_hol1 D_hol1 Et ->
    forall G_hol2 D_hol2,
      G_hol1 ≡[m_hol] G_hol2 ->
      D_hol1 ≡[n_hol] D_hol2 ->
    wf_EC_term m n m_hol n_hol G_hol2 D_hol2 Et)
  /\
  (forall m n m_hol n_hol G1 D1 G_hol1 D_hol1 EP,
    wf_EC_proc m n m_hol n_hol G1 D1 G_hol1 D_hol1 EP ->
    forall G2 D2 G_hol2 D_hol2,
      G1 ≡[m] G2 ->
      D1 ≡[n] D2 ->
      G_hol1 ≡[m_hol] G_hol2 ->
      D_hol1 ≡[n_hol] D_hol2 ->
    wf_EC_proc m n m_hol n_hol G2 D2 G_hol2 D_hol2 EP).
Proof.
  apply wf_EC_ind; intros.
  (* All cases are by transitivity (the rewrites).
     Most cases are one transitivity and IH *)
  all: try solve [
    try rewrite H0, H1 in *; econstructor; eauto; try (eapply H; auto; reflexivity)
  ].
  (* Ehol is by two transitivities. *)
  - econstructor; eauto.
    + rewrite <- H, HG, H1; reflexivity.
    + rewrite <- H0, HD, H2; reflexivity.
Qed.

#[global] Instance Proper_wf_EC_term {m n m_hol n_hol: nat}: Proper ((@ctxt_eq nat m_hol) ==> (@ctxt_eq nat n_hol) ==> eq ==> iff) (wf_EC_term m n m_hol n_hol).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply EC_equiv_wf; eauto.
  - symmetry in H, H0.
    eapply EC_equiv_wf; eauto.
Qed.

#[global] Instance Proper_wf_EC_proc {m n m_hol n_hol: nat} : Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> (@ctxt_eq nat m_hol) ==> (@ctxt_eq nat n_hol) ==> eq ==> iff) (wf_EC_proc m n m_hol n_hol).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply EC_equiv_wf; eauto.
  - symmetry in H, H0, H1, H2.
    eapply EC_equiv_wf; eauto.
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

(* If an EC is wf, then popping a scope gives
    two wf ECs (the top scope and the remainder) *)
Lemma pop_EC_scope_pres :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
      forall Et_top r Et_rest,
        pop_EC_scope Et = (Et_top, Edeflam r Et_rest) ->
        let m_inner := get_fvars_Et Et + m in
        let n_inner := get_rvars_Et Et + n in
            wf_EC_term m n m_inner n_inner (zero m_inner) (one n_inner r) Et_top
        /\  wf_EC_term m_inner 1 m_hol n_hol G_hol D_hol Et_rest)
  /\  (forall m n m_hol n_hol G D G_hol D_hol EP, 
        wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
      forall EP_top r Et_rest,
        pop_EC_scope_proc EP = (EP_top, Edeflam r Et_rest) ->
            wf_EC_proc m n m n G D (zero m) (one n r) EP_top
        /\  wf_EC_term m 1 m_hol n_hol G_hol D_hol Et_rest). 
Proof.
  apply wf_EC_ind; simpl; intros.
  (* Ebag *)
  - destruct (pop_EC_scope_proc EP). injection H0; intros; subst. split.
    + econstructor; eauto. now eapply H.
    + now eapply H.
  (* Ehol *)
  - discriminate H.
  (* Edeflam *)
  - injection H0; intros; subst. split.
    + constructor; auto.
    + auto.
  (* Epar *)
  - destruct (pop_EC_scope_proc EP). injection H0; intros; subst. split.
    + econstructor; eauto. now eapply H.
    + now eapply H.
Qed.

(* If an EC is wf, then splitting it at its hole scope gives
    two wf ECs (the accumulated EC and the hole scope) *)
Lemma split_hole_scope_builder_pres :
      (forall m n m_hol n_hol G_hol D_hol Et,
        wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
      forall r' Et_top ACC Et_acc r Et_hs,
        split_hole_scope_builder r' Et_top Et ACC = (Et_acc, Edeflam r Et_hs) ->
        exists m_acc n_acc,
            wf_EC_term m n m_acc n_acc (zero m_acc) (one n_acc r) Et_acc
        /\  wf_EC_term m_acc 1 m_hol n_hol G_hol D_hol Et_hs).
Proof.
  induction Et using (well_founded_induction hole_depth_lt_wf); intros.
  destruct ACC; inversion H0; inversion WFP; existT_eq; subst; simpl in H1.
  (* Ehol *)
  - injection H1; intros; subst. eexists; eexists; split.
    2: econstructor; eauto.
  (* Edeflam *)
  -
  (* Epar *)
  -


  
  induction Et_cur using (well_founded_induction hole_depth_lt_wf).
  destruct Et_cur; destruct EP; intros; destruct ACC.
  - simpl. now repeat eexists.
  - apply (H Et). unfold hole_depth_lt; auto.
  - unfold split_hole_scope_builder. fold split_hole_scope_builder.
    generalize (pop_EC_scope_reduces_hole_depth (Ebag m n (Epar EP P)))
        as pf_HD.
    destruct (inv_pop_EC_scope_term (Ebag m n (Epar EP P))).
    all: dest_conj_disj_exist; rewrite H0; clear H0; intros.
    + now repeat eexists.
    + apply (H x1 (pf_HD x1 x x0 eq_refl) _ _ _).
Qed.

