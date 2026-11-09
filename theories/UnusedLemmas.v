(* Lemmas and definitions that are not used anywhere else in the development.
   They were moved here from EvalContexts.v, Semantics.v and Preservation.v
   (including lemmas that were already commented out there),
   grouped by their origin file and kept in their original order.
   This file is not listed in _CoqConfig, so `make` does not build it.
   To check it: rocq compile -Q theories LEpic theories/UnusedLemmas.v *)

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

From LEpic Require Import Contexts Syntax EvalContexts Semantics.
Import Renamings.
Import Stdlib.Relations.Relation_Operators.

Local Open Scope program_scope.
Local Open Scope bool_scope.



(* ================================================== *)
(* From EvalContexts.v *)
(* ================================================== *)

(* Applies either f1 or f2 to the hole scope, depending on whether 
   the hole scope is the top scope *)
Definition case_hole_scope_at_top {X} (f1 f2 : EC_term -> X) (Et : EC_term) :=
  (if is_hole_scope_at_top Et then f1 else f2) (hole_scope Et).

(* Mutates the hole scope with a function f *)
Definition mutate_under_hole_scope (f : EC_proc -> EC_proc) (Et : EC_term) :=
  let f_term :=
    fun Et =>
      match Et with Ebag m n EP => Ebag m n (f EP) end
  in
  mutate_hole_scope f_term Et.

Definition mutate_under_hole_scope_proc (f : EC_proc -> EC_proc) (EP : EC_proc) :=
  match mutate_under_hole_scope f (Ebag 0 0 EP) with Ebag _ _ EP' => EP' end.

Lemma commute_fill_proc : forall EP EP' P,
  EP <=<[ EP' ]p <=[ P ]p = EP <=[ EP' <=[ P ]p ]p.
Proof. apply commute_fill. Qed.

Lemma commute_EC_fill_proc : forall EP EP1 EP2,
  EP <=<[ EP1 ]p <=<[ EP2 ]p = EP <=<[ EP1 <=<[ EP2 ]p ]p.
Proof. apply commute_EC_fill. Qed.

Lemma meet_hole_scope_at_top_term : forall Et EP, is_hole_scope_at_top Et = true ->
  is_hole_scope_at_top_proc EP = true -> is_hole_scope_at_top (Et <=<[ EP ]) = true.
Proof. apply meet_hole_scope_at_top. Qed.
Lemma left_join_hole_scope_at_top_term : forall Et EP, 
  is_hole_scope_at_top Et = false -> is_hole_scope_at_top (Et <=<[ EP ]) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.

Lemma right_join_hole_scope_at_top_term : forall Et EP, 
  is_hole_scope_at_top_proc EP = false -> is_hole_scope_at_top (Et <=<[ EP ]) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.

Lemma right_join_hole_scope_at_top_proc : forall EP EP', 
  is_hole_scope_at_top_proc EP' = false -> is_hole_scope_at_top_proc (EP <=<[ EP' ]p) = false.
Proof. intros; apply join_hole_scope_at_top. auto. Qed.

Lemma inv_split_hole_scope_Epar :
  (forall Et Et_top EP P,
    split_hole_scope Et <> (Et_top, Epar EP P)).
Proof.
  unfold not; intros.
  destruct (inv_split_hole_scope Et).
  all: dest_conj_disj_exist; rewrite H0 in H; discriminate.
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

(*  hole_scope ignores prefixes before reaching the hs  *)
Lemma hole_scope_fill_not_hs :
  forall Et EP m n,
    is_hole_scope_at_top_proc EP = false ->
    hole_scope (Et <=<[ EP ]) = hole_scope (Ebag m n EP).
Proof.
  destruct Et; generalize dependent m; generalize dependent n;
      generalize dependent EP; EP_ind_unsafe IH EP; simpl in *; intros.
  - unfold hole_scope; simpl.
    apply build_not_hs_correct in H; dest_conj_disj_exist.
    now repeat rewrite H1.
  - assert (forall EP, Ebag m n EP = Ebag m n Ehol <=<[ EP ]) by auto.
    repeat rewrite H3, hole_scope_of_fill_Edeflam; auto.
  - replace (Ebag m n (Epar (EP <=<[ EP0 ]p) H2)) with (Ebag m n Ehol <=<[ Epar (EP <=<[ EP0 ]p) H2 ]) by auto.
    rewrite hole_scope_of_fill_Epar with (m := m) (n := n); auto.
    now apply right_join_hole_scope_at_top_proc.
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

Lemma fill_wf_pres_proc : forall m n m_hol n_hol G D G_hol D_hol EP, 
  wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP -> forall (P : proc),
  wf_proc m_hol n_hol G_hol D_hol P -> wf_proc m n G D (EP <=[ P ]p).
Proof. apply fill_wf_pres. Qed.

Lemma wf_hs_var_bounds_eq_term : forall m n m_hol n_hol G_hol D_hol Et,
  wf_EC_term m n m_hol n_hol G_hol D_hol Et -> is_hole_scope_at_top Et = true ->
  m_hol = (get_fvars_Et Et) + m  /\ n_hol = (get_rvars_Et Et) + n.
Proof. apply wf_hs_var_bounds_eq. Qed.

(*  G_hol always maps free fvars to 0.  *)
Lemma wf_hs_G_hol_bounds :
    (forall m n m_hol n_hol G_hol D_hol Et,
      wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall x,
      bound_fvars_at_hole_scope Et <= x < m_hol ->
      G_hol x = 0)
/\  (forall m n m_hol n_hol G D G_hol D_hol EP,
      wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
      (is_hole_scope_at_top_proc EP = true ->
        forall x,
          x < m_hol ->
          G_hol x <= G x)
  /\  (is_hole_scope_at_top_proc EP = false ->
        forall x,
          bound_fvars_at_hole_scope (Ebag 0 0 EP) <= x < m_hol ->
          G_hol x = 0)).
Proof.
  apply wf_EC_ind; unfold bound_fvars_at_hole_scope, apply_at_hole_scope;
      simpl; intros; dest_conj_disj_exist.
  - destruct (is_hole_scope_at_top_proc EP) eqn:HS.
    + clear H2; specialize H with x. 
      rewrite hole_scope_id in H0; auto; simpl in H0.
      rewrite ctxt_app_r in H; auto.
      unfold zero, flat_ctxt in H. lia.
    + clear H; apply H2; auto. 
      rewrite (hole_scope_change_bounds m n); auto.
  - split; try discriminate; intros.
    unfold ctxt_eq in HG. specialize HG with x; lia.
  - split; try discriminate; intros.
    apply H.
    replace (Ebag 0 0 (Edeflam r Et)) with 
        (Ebag 0 0 Ehol <=<[ Edeflam r Et ]) in H1 by auto.
    now rewrite hole_scope_of_fill_Edeflam in H1.
  - split; intros.
    + clear H0; specialize H with x.
      unfold ctxt_eq in HG. specialize HG with x.
      rewrite sum_correct in HG.
      apply wf_hs_var_bounds_eq in WFP1; auto;
          dest_conj_disj_exist; subst.
      apply H in H1; lia.
    + clear H; specialize H0 with x.
      replace (Ebag 0 0 (Epar EP P)) with 
        (Ebag 0 0 Ehol <=<[ Epar EP P ]) in H2 by auto.
      rewrite hole_scope_of_fill_Epar with (m := 0) (n := 0) in H2; auto. 
Qed.

(*  All G_hol end in zero.  *)
(* Lemma wf_hs_split_G_hol :
  forall m n m_free m_bound n_hol G_hol D_hol Et,
    m_bound = bound_fvars_at_hole_scope Et ->
    wf_EC_term m n (m_bound + m_free) n_hol G_hol D_hol Et ->
  exists G,
    G_hol ≡[m_bound + m_free] G ⊗ zero (m_free).
Proof.
  intros. exists G_hol. solve_ctxt_eq.
  eapply wf_hs_G_hol_bounds in H0; eauto; lia.
Qed. *)

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



(* ================================================== *)
(* From Semantics.v *)
(* ================================================== *)

(* Replaces x for y or y for x if either are below n.
    If neither are below n, then it is just an identity renaming. 
  To note, n_scope is only used in the renaming's type
    and does not affect behavior, so 
    forall x y, (rename_var x) = (rename_var y). *)
Definition rename_var n_scope n (x:var) (y:var) : ren n_scope n_scope :=
  fun z => if lt_dec x n
           then if Nat.eq_dec z x
                then y
                else z
           else if lt_dec y n
           then if Nat.eq_dec z y
                then x
                else z
           else z.

(* The appropriate n_scope is not given,
    but can be replaced via rewrite since rename_var
    does not depend on its first argument.
    Hence, n_scope just uses n. *)
Definition rename_at_hole_scope n r1 r2 Et :=
  let apply_ren := (rename_rvar_EC_proc (rename_var n n r1 r2)) in
  mutate_under_hole_scope apply_ren Et.

Lemma rename_var_wf :
  forall n_scope n x y,
    n <= n_scope ->
    x < n_scope ->
    y < n_scope ->
    wf_ren (rename_var n_scope n x y).
Proof. unfold wf_ren, rename_var; intros; split; lia_goal. Qed.

Lemma rename_var_correct :
  forall n_scope n x y,
    x < n \/ y < n ->
    rename_var n_scope n x y x = rename_var n_scope n x y y.
Proof. intros; unfold rename_var; lia_goal. Qed.

Lemma rename_var_correct_y :
  forall n_scope n x y,
    x < n ->
    rename_var n_scope n x y y = y.
Proof. intros; unfold rename_var; lia_goal. Qed.

Lemma rename_var_correct_x :
  forall n_scope n x y,
    ~ (x < n) ->
    rename_var n_scope n x y x = x.
Proof. intros; unfold rename_var; lia_goal. Qed.

Lemma rename_var_wf_hs_fun :
  forall Et m_hol n_hol G_hol x y,
    let n := get_rvars_Et Et in
    (* n <= n_hol -> *)
    x < n_hol ->
    y < n_hol ->
    x < n \/ y < n ->
    let ren_fun := mutate_under_hole_scope
        (rename_rvar_EC_proc (rename_var n_hol n x y)) in
    wf_hs_fun ren_fun Et m_hol n_hol G_hol (one n_hol x ⨥ one n_hol y)
                      m_hol n_hol G_hol (zero n_hol).
Proof.
  unfold wf_hs_fun; intros.
  unfold mutate_under_hole_scope, mutate_hole_scope.
  rewrite inv_hole_scope_at_top; auto.
  inversion H3; clear H3; existT_eq; subst; simpl in *.

  assert (x < n0 -> D x = 2) as HDx.
  {
    intros; apply min_rvar_hs_EC_wf with (r := x) in WFP; auto.
    unfold one in WFP; 
        rewrite sum_correct, delta_id in WFP; auto.
    rewrite ctxt_app_l in WFP; auto.
    specialize UD with x; lia.
  }
  assert (y < n0 -> D y = 2) as HDy.
  {
    intros; apply min_rvar_hs_EC_wf with (r := y) in WFP; auto.
    unfold one in WFP; 
        rewrite sum_correct, delta_id in WFP; auto.
    rewrite ctxt_app_l in WFP; auto.
    specialize UD with y; lia.
  }

  assert (WFP' := WFP); apply wf_hs_var_bounds_eq_proc in WFP'; auto.
  destruct WFP'; subst.

  apply rename_rvar_pres_wf_hs_EC 
      with (R := (rename_var (n0 + n) n0 x y)) in WFP; auto.
  2: apply rename_var_wf; auto; lia.

  unfold one in WFP.
  rewrite lctxt_rename_sum in WFP.
  repeat (rewrite lctxt_rename_delta in WFP; auto).
  rewrite rename_var_correct in WFP; auto.
  rewrite delta_sum in WFP; simpl in WFP.

  assert (forall D j k r o, j <= r -> j <= k ->
            @lctxt_rename_helper (n0 + n) (n0 + n) j
            (fun z : var => if Nat.eq_dec z r then o else z)
            (@ctxt_app _ n0 n D (flat_ctxt 1 n)) k = 0)
      as LRH1.
  {
    induction j; simpl; intros.
    - unfold zero; auto.
    - rewrite sum_correct.
      destruct (Nat.eq_dec j r); try lia.
      rewrite delta_neq; auto; try lia.
      rewrite IHj; lia.
  }
  assert (forall D j k r o, r < j <= k -> r < n0 ->
            @lctxt_rename_helper (n0 + n) (n0 + n) j
            (fun z : var => if Nat.eq_dec z r then o else z)
            (@ctxt_app _ n0 n D (flat_ctxt 1 n)) k =
            (n0 + n) [o ↦ D r] k)
      as LRH2.
  {
    induction j; simpl; intros; try lia.
    rewrite sum_correct.
    destruct (Nat.eq_dec j r); subst.
    - rewrite LRH1; try lia.
      rewrite ctxt_app_l; lia.
    - rewrite IHj; try lia.
      rewrite delta_neq; lia.
  }

  assert (forall D r o, r < n0 -> o < n0 + n ->
  forall i,
      (i <= r ->
        @lctxt_rename_helper (n0 + n) (n0 + n) i
              (fun z => if Nat.eq_dec z r then o else z)
              (@ctxt_app _ n0 n D (flat_ctxt 1 n))
        ≡[i] @ctxt_app _ n0 n D (flat_ctxt 1 n))
  /\  (r < i <= n0 + n ->
        @lctxt_rename_helper (n0 + n) (n0 + n) i
              (fun z => if Nat.eq_dec z r then o else z)
              (@ctxt_app _ n0 n D (flat_ctxt 1 n))
        ≡[i] (@ctxt_app _ n0 n
                (fun z => if Nat.eq_dec z r then 0 else D z)
                (flat_ctxt 1 n)) 
              ⨥ (n0 + n)[o ↦ D r]))
      as LRH.
  {
    intros. unfold ctxt_eq; induction i; try (split; lia).
    destruct IHi; simpl. split; intros; rewrite sum_correct.
    - destruct (Nat.eq_dec i r); try lia.
      destruct (Nat.eq_dec x0 i); subst.
      + rewrite delta_id; try lia. rewrite LRH1; lia.
      + rewrite delta_neq; auto; simpl.
        rewrite H5; auto; try lia.
    - destruct (Nat.eq_dec i r); destruct (Nat.eq_dec x0 i); subst.
      + rewrite LRH1; auto. rewrite Nat.add_0_r.
        rewrite sum_correct.
        repeat (rewrite ctxt_app_l; auto).
        destruct (Nat.eq_dec r r); lia.
      + rewrite H5; try lia.
        rewrite sum_correct.
        repeat (rewrite ctxt_app_l; try lia).
        destruct (Nat.eq_dec x0 r); lia.
      + rewrite delta_id; try lia.
        rewrite sum_correct.
        rewrite LRH2; try lia.
        destruct (lt_dec i n0).
        * repeat (rewrite ctxt_app_l; auto).
          destruct (Nat.eq_dec i r); lia.
        * repeat (rewrite ctxt_app_r; auto); lia.
      + rewrite H6; try lia.
        rewrite delta_neq; auto.
  }
  clear LRH1 LRH2.

  assert (forall D r o, r < n0 -> o < n0 + n ->
    @lctxt_rename (n0 + n) (n0 + n)
                  (fun z => if Nat.eq_dec z r then o else z)
                  (@ctxt_app _ n0 n D (flat_ctxt 1 n))
        ≡[n0 + n] (@ctxt_app _ n0 n 
                (fun z => if Nat.eq_dec z r then 0 else D z)
                (flat_ctxt 1 n)) 
              ⨥ (n0 + n)[o ↦ D r])
      as LR.
  {
    intros. destruct (LRH D0 r o H3 H4 (n0 + n)); clear LRH H5.
    unfold lctxt_rename. rewrite H6; try lia; reflexivity.
  }
  clear LRH.

  unfold rename_var in WFP at 1.
  destruct (lt_dec x n0).
  - clear H1 HDy. rewrite LR in WFP; auto; clear LR.
    rewrite rename_var_correct_y in WFP; auto.
    rewrite HDx in WFP; auto; clear HDx.

    apply rem_hole_rvar_EC_wf with 
        (r := y) (D_hol' := (zero (n0 + n))) in WFP;
        eauto.
    2: now rewrite sum_zero_l.
    dest_conj_disj_exist.
    1: rewrite ren_pres_hs_proc in H1; now rewrite H1 in H2.

    apply ctxt_eq_sum_inv in H3.
    rewrite <- H3 in H4; clear H3.
    eapply wf_Ebag with (D := 
        (fun z : var => if Nat.eq_dec z x then 0 else D z)); eauto.
    intros. destruct (Nat.eq_dec x1 x); auto.
  - destruct (lt_dec y n0); try lia; clear H1 HDx.
    rewrite LR in WFP; auto; clear LR.

    rewrite <- rename_var_correct, rename_var_correct_x in WFP; auto.
    rewrite HDy in WFP; auto; clear HDy.

    apply rem_hole_rvar_EC_wf with 
        (r := x) (D_hol' := (zero (n0 + n))) in WFP;
        eauto.
    2: now rewrite sum_zero_l.
    dest_conj_disj_exist.
    1: rewrite ren_pres_hs_proc in H1; now rewrite H1 in H2.

    apply ctxt_eq_sum_inv in H3.
    rewrite <- H3 in H4; clear H3.
    eapply wf_Ebag with (D := 
        (fun z : var => if Nat.eq_dec z y then 0 else D z)); eauto.
    intros. destruct (Nat.eq_dec x1 y); auto.
Qed.

(* Helper functions for garbage collecting functions *)

(* Returns true if P contains a call to f, false otherwise *)
Fixpoint contains_fvar_call f P :=
  match P with
  | def _ (lam (bag m _ P')) => contains_fvar_call (m + f) P'
  | par P1 P2 => contains_fvar_call f P1 || contains_fvar_call f P2
  | app f' _ => f =? f'
  | _ => false
  end.

(* Returns true if Et contains no call to f, assuming f is bound in the 
   hole scope of Et. Returns false otherwise. *)
Definition can_remove_function f Et :=
  let P := get_proc ((hole_scope Et) <=[ nul ]) in
  negb (contains_fvar_call f P).



(* ================================================== *)
(* From Preservation.v *)
(* ================================================== *)

(* Lemma wf_prim_step_nul :
  forall m n Et P,
    wf_term m n (Et <=[ par P nul ]) ->
    wf_term m n (Et <=[ P ]).
Proof.
  intros. destr_inv_fill_wf H. eapply fill_wf_pres_term; eauto.
  inversion H1; inversion WFP2; existT_eq; subst; rewrite_ctxt_equivs.
  repeat rewrite sum_zero_r; auto.
Qed. *)
