From Stdlib Require Import
  Arith   
  Basics         
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Morphisms
  Nat
  Program.Basics
  List
  Lia.

From LEpic Require Import Contexts Syntax EvalContexts Semantics.
Import Renamings.
Import Stdlib.Relations.Relation_Operators.

Local Open Scope program_scope.
Local Open Scope bool_scope.



(* Preservation of prim_step and step *)

Lemma wf_prim_step_nul :
  forall m n Et P,
    wf_term m n (Et <=[ par P nul ]) ->
    wf_term m n (Et <=[ P ]).
Proof.
  intros. destr_inv_fill_wf H. eapply fill_wf_pres_term; eauto.
  inversion H1; inversion WFP2; existT_eq; subst; rewrite_ctxt_equivs.
  repeat rewrite sum_zero_r; auto.
Qed.



Lemma wf_prim_step_emp :
  forall m n Et r,
    wf_term m n (Et <=[ par (def r emp) (def r emp) ]) ->
    wf_term m n (Et <=[ nul ]).
Proof.
  intros. destr_inv_fill_wf H.
  inversion H1; inversion WFP1; inversion WFP2; inversion WFO; 
    inversion WFO0; existT_eq; subst; rewrite_ctxt_equivs; 
    clear H1 WFP1 WFP2 WFO WFO0.
  repeat rewrite sum_zero_r in H2.
  unfold one in H2; rewrite delta_sum in H2; simpl in H2.
  assert ((zero n_hol) r = 0) as Z by auto.
  eapply rem_hole_rvar_EC_wf in H2; try exact Z; auto.
  - eapply fill_wf_pres_term; eauto. constructor; reflexivity.
  - rewrite sum_zero_l; reflexivity.
Qed.



Lemma wf_prim_step_tup :
  forall m n Et r r1 r2 r1' r2',
    wf_term m n (Et <=[ par (def r (tup r1 r2)) (def r (tup r1' r2')) ]) ->
    wf_term m n (Et <=[ par (req r1 r1') (req r2 r2') ]).
Proof.
  intros. destr_inv_fill_wf H.
  inversion H1; inversion WFP1; inversion WFP2; inversion WFO; 
    inversion WFO0; existT_eq; subst; rewrite_ctxt_equivs; 
    clear H1 WFP1 WFP2 WFO WFO0.
  rewrite sum_zero_r in H2.
  unfold one at 1 4 in H2.
  assert (forall c1 c2, ((n_hol [r ↦ 1] ⨥ c1) ⨥ (n_hol [r ↦ 1] ⨥ c2))
                ≡[n_hol]  c1 ⨥ c2 ⨥ n_hol [r ↦ 2]) as Z.
    { unfold delta, sum, ctxt_eq; intros. lia_goal. }
  rewrite Z in H2; clear Z.
  assert (H3 := H2).
  eapply rem_hole_rvar_EC_wf in H2; try reflexivity; auto.
  - eapply fill_wf_pres_term; eauto. repeat econstructor; auto.
    unfold sum, one, ctxt_eq, delta; lia.
  - apply max_rvar_hole_EC_wf_term with (r := r) in H3; auto.
    unfold one, delta, sum in *; lia_destruct; lia_goal.
Qed.



Lemma wf_prim_step_req :
  forall m n Et r1 r2,
    let n_bound := bound_rvars_at_hole_scope Et in
    r1 < n_bound \/ r2 < n_bound ->
    wf_term m n (Et <=[ req r1 r2 ]) ->
    wf_term m n ((rename_at_hole_scope n_bound r1 r2 Et) <=[ nul ]).
Proof.
  intros. destr_inv_fill_wf H0.
  inversion H1; existT_eq; subst; rewrite_ctxt_equivs; clear H1.
  eapply (fill_wf_pres_term m n m_hol n_hol); eauto. 
  2: econstructor; reflexivity.

  unfold rename_at_hole_scope.
  eapply mutate_hole_scope_wf; eauto.
  apply wf_hs_fun_hole_scope.
  erewrite rename_rvar_EC_proc_indep 
      with (R2 := rename_var n_hol n_bound r1 r2); eauto.
  apply rename_var_wf_hs_fun; auto.
Qed.



Lemma wf_prim_step_app_same_scope :
  forall m n Et t f rf r,
    let new_body := ready_body_same_scope Et t r in
    let Et_fun := Et <=<[ (Epar Ehol
                          (par (def rf (lam t))
                               (def rf (bng f)))) ] in
    let Et_shifted := shift_hs_by_term_vars t Et_fun in
    wf_term m n (Et_fun     <=[ app f r ]) ->
    wf_term m n (Et_shifted <=[ new_body ]).
Proof.
  intros.
  unfold Et_fun in H. rewrite commute_fill_term in H; simpl in H.
  destr_inv_fill_wf H.
  inversion H1; inversion WFP1; existT_eq; subst; 
      clear H1 WFP1; rewrite_ctxt_equivs.
  rewrite sum_zero_l in H2.
  destruct t; simpl in *.
  inversion WFP2; inversion WFP1; inversion WFP0; 
      inversion WFO; inversion WFO0; inversion WFT; 
      existT_eq; subst; rewrite_ctxt_equivs; 
      rewrite sum_zero_l, sum_zero_r in *;
      unfold one in *; rewrite delta_sum in *; simpl in *;
      clear WFP1 WFP0 WFO WFO0 WFT G0 D0 G1 D1 G2 D2 G3 D3.

  unfold bound_fvars_at_hole_scope, bound_rvars_at_hole_scope,
      apply_at_hole_scope in new_body.
  destruct (hole_scope Et) eqn:HS; simpl in *.
  remember (m_hol - m1) as m_free.
  remember (n_hol - n1) as n_free.
  assert (m_hol = (m1 + m_free) /\ n_hol = (n1 + n_free)).
  {
    apply wf_hs_vars_correct in H2.
    unfold bound_fvars_at_hole_scope, bound_rvars_at_hole_scope,
        apply_at_hole_scope in H2.
    rewrite HS in H2; simpl in H2; lia.
  }
  clear Heqm_free Heqn_free; destruct H; subst.

  assert (f < m1). {
    replace m1 with (bound_fvars_at_hole_scope Et) by
        (unfold bound_fvars_at_hole_scope, apply_at_hole_scope; now rewrite HS).
    eapply fvar_bound_hs; eauto.
    rewrite delta_id; auto.
  }
  assert (rf < n1). {
    replace n1 with (bound_rvars_at_hole_scope Et) by
        (unfold bound_rvars_at_hole_scope, apply_at_hole_scope; now rewrite HS).
    eapply rvar_bound_hs; eauto.
    eapply max_rvar_hole_EC_wf in H2; eauto.
    rewrite sum_correct, delta_id, delta_neq in *; auto;
        destruct (Nat.eq_dec r rf); auto; subst; rewrite delta_id in *; lia.
  }
  replace ((m1 + m_free) [f ↦ 1]) with 
          (@ctxt_app _ m1 m_free (m1 [f ↦ 1]) (zero m_free)) in * by
      now rewrite delta_app_zero_r.
  replace ((n1 + n_free) [rf ↦ 2]) with 
          (@ctxt_app _ n1 n_free (n1 [rf ↦ 2]) (zero n_free)) in * by
      now rewrite delta_app_zero_r.

  unfold ready_body_fvar_same_scope, ready_body_rvar in new_body.
  remember (ready_var r n1 (n0 + 1)) as r_new.
  apply fill_wf_pres_term with 
      (m_hol := m1 + m0 + m_free)
      (n_hol := n1 + (n0 + 1) + n_free)
      (G_hol := @ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free))
      (D_hol := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥
                (@ctxt_app _ (n1 + (n0 + 1)) n_free
                    (zero n1 ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free))).

  - unfold Et_shifted; clear Et_shifted new_body.
    unfold shift_hs_by_term_vars; simpl.

    do 2 (try eapply mutate_hole_scope_wf); eauto; unfold Et_fun.
    + eapply EC_fill_wf_pres_term; eauto.
      econstructor; eauto.
      2: now rewrite sum_zero_l.
      2: reflexivity.
      econstructor; reflexivity.

    + rewrite hole_scope_fill_hs, HS; auto; simpl.
      rewrite <- app_zero.
      apply add_fvars_wf_hs_fun; eauto.

    + unfold add_fvars_hole_scope.
      rewrite hole_scope_mutate_hole_scope.
      2: intros; destruct Et0; induction EP0; auto.
      rewrite hole_scope_fill_hs, HS; auto; simpl.
      unfold add_fvars; simpl.
      unfold ready_var in Heqr_new; destruct (lt_dec r n1); subst.
      * repeat rewrite Nat.add_0_r.
        repeat rewrite <- delta_app_zero_r; try lia;
            repeat rewrite lctxt_sum_app_dist;
            rewrite sum_zero_l.
        repeat rewrite sum_zero_r.
        apply add_rvars_wf_hs_fun.
        intros. unfold ctxt_app; destruct (lt_dec x n0); auto.
      * replace r with (n1 + (r - n1)) by lia.
        replace (n1 + (r - n1) + (n0 + 1)) with (n1 + (n0 + 1) + (r - n1)) by lia.
        repeat rewrite <- delta_app_zero_l; try lia;
            do 2 rewrite <- app_zero;
            repeat rewrite lctxt_sum_app_dist;
            repeat rewrite sum_zero_l;
            repeat rewrite sum_zero_r.
        apply add_rvars_wf_hs_fun.
        intros. unfold ctxt_app; destruct (lt_dec x n0); auto.

  - unfold new_body; clear Et_shifted new_body; simpl.
    apply wf_par with
        (G1 := zero (m1 + m0 + m_free))
        (D1 := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥ 
                  ((zero n1 ⊗ (zero n0 ⊗ flat_ctxt 1 1)) ⊗ zero n_free))
        (G2 := @ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free))
        (D2 := @ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 1 1)) (zero n_free)).

    + econstructor; try lia; try reflexivity.
      * subst. unfold ready_var.
        destruct (lt_dec r n1); lia.
      * solve_ctxt_eq.

    + remember (ren_commute_str 0 m0 m1 m_free) as Rf.
      remember (weaken_ren ((n0 + 1) + n_free) n1) as Rr. 
      erewrite rename_fvar_ind_proc with (R2 := Rf); auto.
      erewrite rename_rvar_ind_proc with (R2 := Rr); auto.

      assert (@ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free) ≡[m1 + m0 + m_free]
          lctxt_rename Rf (@ctxt_app _ m0 (m1 + m_free) G8 (zero (m1 + m_free)))). {
        rewrite <- (ctxt_app_null_l (zero 0) (G8 ⊗ zero (m1 + m_free))), <- app_zero.
        repeat rewrite ctxt_app_assoc.
        replace (m1 + m0 + m_free) with (0 + m1 + m0 + m_free) by lia.
        subst; rewrite ren_commute_str_lctxt_rename.
        simpl; now rewrite ctxt_app_null_l.
      }
      rewrite H1; clear H1.
      apply rename_fvar_pres_wf; 
          try (subst; remember (ren_commute_str_wf_ren 0); now simpl in *); clear HeqRf Rf.

      assert (@ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 1 1)) (zero n_free)
          ≡[n1 + (n0 + 1) + n_free] (lctxt_rename Rr ((D8 ⊗ flat_ctxt 1 1) ⊗ zero n_free))). {
        replace (n1 + (n0 + 1) + n_free) with (n1 + (n0 + 1 + n_free)) by lia.
        subst; rewrite weaken_ren_lctxt_rename; now repeat rewrite ctxt_app_assoc.
      }
      rewrite H1; clear H1.
      replace (n1 + (n0 + 1) + n_free) with (n1 + (n0 + 1 + n_free)) by lia;
          apply rename_rvar_pres_wf; try (subst; apply weaken_ren_wf_ren); clear HeqRr Rr.

      apply wf_weaken_free_vars with (m' := 0) (n' := n_free) in WFP.
      rewrite Nat.add_0_r, ctxt_app_l in WFP; simpl.
      now repeat rewrite Nat.add_assoc in *.

    + now rewrite sum_zero_l.
    + rewrite <- sum_assoc; repeat rewrite lctxt_sum_app_dist; 
          repeat rewrite sum_zero_l.
      solve_ctxt_eq.
Qed.



Lemma wf_prim_step_app_diff_scope :
  forall m n Et Et' t f rf rl r,
    let f' := f + (bound_fvars_to_hole Et) in
    let new_body := ready_body_diff_scope Et t r in
    let Et_shifted := shift_hs_by_term_vars t Et in
    let Et_fun := Et' <=<[ (Epar Ehol
                           (par (def rf (lam t))
                                (def rf (bng f)))) ] in
    wf_term m n (Et_fun <=[ def rl (lam (Et         <=[ app f' r ])) ]) ->
    wf_term m n (Et_fun <=[ def rl (lam (Et_shifted <=[ new_body ])) ]).
Proof.
  intros.
  unfold Et_fun in H. rewrite commute_fill_term in H; simpl in H.
  destr_inv_fill_wf H.
  inversion H1; inversion WFP1; inversion WFO; existT_eq; subst; 
      clear H1 WFP1 WFO; rewrite_ctxt_equivs.
  rewrite sum_zero_l, sum_zero_r in H2.
  apply inv_fill_wf in WFT;
      destruct WFT as (m_hol' & n_hol' & G_hol' & D_hol' & H3 & H4).
  inversion H3; existT_eq; subst; clear H3; rewrite_ctxt_equivs. 
  destruct t; simpl in *.
  inversion WFP2; inversion WFP1; inversion WFP0; 
      inversion WFO; inversion WFO0; inversion WFT; 
      existT_eq; subst; rewrite_ctxt_equivs; 
      rewrite sum_zero_l, sum_zero_r in *;
      unfold one in *; rewrite delta_sum in *; simpl in *;
      clear WFP1 WFP0 WFO WFO0 WFT G0 D0 G1 D1 G2 D2 G3 D3.

  unfold bound_fvars_before_hole_scope,
      bound_fvars_at_hole_scope, bound_rvars_at_hole_scope,
      apply_at_hole_scope in new_body.
  destruct (hole_scope Et) eqn:HS; simpl in *.
  remember (m_hol' - m1) as m_free.
  remember (n_hol' - n1) as n_free.
  assert (m_hol' = (m1 + m_free) /\ n_hol' = (n1 + n_free)).
  {
    apply wf_hs_vars_correct in H4.
    unfold bound_fvars_at_hole_scope, bound_rvars_at_hole_scope,
        apply_at_hole_scope in H4.
    rewrite HS in H4; simpl in H4; lia.
  }
  clear Heqm_free Heqn_free; destruct H; subst.

  apply fill_wf_pres_term with 
      (m_hol := m_hol)
      (n_hol := n_hol)
      (G_hol := zero m_hol)
      (D_hol := n_hol [rl ↦ 1]).

  1: unfold Et_fun.
  1: eapply EC_fill_wf_pres_term; eauto.
  1: econstructor; eauto; try reflexivity; try now rewrite sum_zero_l.
  1: constructor; reflexivity.
  
  econstructor; eauto; try solve [unfold one; now rewrite sum_zero_r].
  econstructor; eauto; try reflexivity.

  remember (ready_var r n1 (n0 + 1)) as r_new.
  apply fill_wf_pres_term with 
      (m_hol := m1 + m0 + m_free)
      (n_hol := n1 + (n0 + 1) + n_free)
      (G_hol := @ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free))
      (D_hol := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥
                (@ctxt_app _ (n1 + (n0 + 1)) n_free
                    (zero n1 ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free))).

  - unfold Et_shifted; clear Et_shifted new_body.
    unfold shift_hs_by_term_vars; simpl.

    do 2 (try eapply mutate_hole_scope_wf); eauto.

    + rewrite HS; auto; simpl.
      rewrite <- app_zero.
      apply add_fvars_wf_hs_fun; eauto.

    + unfold add_fvars_hole_scope.
      rewrite hole_scope_mutate_hole_scope.
      2: intros; destruct Et0; induction EP0; auto.
      rewrite HS; auto; simpl.
      unfold add_fvars; simpl.
      unfold ready_var in Heqr_new; destruct (lt_dec r n1); subst.
      * repeat rewrite Nat.add_0_r.
        repeat rewrite <- delta_app_zero_r; try lia;
            repeat rewrite lctxt_sum_app_dist;
            rewrite sum_zero_l.
        repeat rewrite sum_zero_r.
        apply add_rvars_wf_hs_fun.
        intros. unfold ctxt_app; destruct (lt_dec x n0); auto.
      * replace r with (n1 + (r - n1)) by lia.
        replace (n1 + (r - n1) + (n0 + 1)) with (n1 + (n0 + 1) + (r - n1)) by lia.
        repeat rewrite <- delta_app_zero_l; try lia;
            do 2 rewrite <- app_zero;
            repeat rewrite lctxt_sum_app_dist;
            repeat rewrite sum_zero_l;
            repeat rewrite sum_zero_r.
        apply add_rvars_wf_hs_fun.
        intros. unfold ctxt_app; destruct (lt_dec x n0); auto.

  - unfold new_body; clear Et_shifted new_body; simpl.
    apply wf_par with
        (G1 := zero (m1 + m0 + m_free))
        (D1 := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥ 
                  ((zero n1 ⊗ (zero n0 ⊗ flat_ctxt 1 1)) ⊗ zero n_free))
        (G2 := @ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free))
        (D2 := @ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 1 1)) (zero n_free)).

    + econstructor; try lia; try reflexivity.
      * subst. unfold ready_var.
        destruct (lt_dec r n1); lia.
      * solve_ctxt_eq.

    + remember (bound_fvars_to_hole Et - m1) as m_bbhs.
      assert (m_free = m_bbhs + m_hol).
      {
        apply wf_hs_fvars_eq_free_plus_bound in H4; subst.
        remember (fvars_to_hole_include_at_hs Et); clear Heql.
        unfold bound_fvars_at_hole_scope, apply_at_hole_scope in l.
        rewrite HS in l; simpl in l; lia.
      }
      clear Heqm_bbhs; subst.
      
      remember (ren_commute_str m1 m_bbhs m0 m_hol) as Rf1.
      remember (weaken_ren (m0 + m_hol) (m1 + m_bbhs)) as Rf2.
      remember (weaken_ren ((n0 + 1) + n_free) n1) as Rr. 
      erewrite rename_fvar_ind_proc with (R2 := Rf1); auto.
      erewrite rename_fvar_ind_proc with (R2 := Rf2)
          (R1 := (weaken_ren m0 (m1 + m_bbhs))); auto.
      erewrite rename_rvar_ind_proc with (R2 := Rr); auto.

      assert (@ctxt_app _ (m1 + m0) (m_bbhs + m_hol) (zero m1 ⊗ G8) (zero (m_bbhs + m_hol)) ≡[m1 + m0 + (m_bbhs + m_hol)]
          lctxt_rename Rf1 (@ctxt_app _ (m1 + m_bbhs) (m0 + m_hol) (zero (m1 + m_bbhs)) (G8 ⊗ zero m_hol))). {
        repeat rewrite ctxt_app_assoc.
        repeat rewrite <- app_zero.
        replace (m1 + m0 + (m_bbhs + m_hol)) with (m1 + m0 + m_bbhs + m_hol) by lia.
        subst; rewrite ren_commute_str_lctxt_rename.
        now rewrite ctxt_app_assoc.
      }
      rewrite H; clear H.
      replace (m1 + m0 + (m_bbhs + m_hol)) with (m1 + (m0 + m_bbhs) + m_hol) by lia;
          apply rename_fvar_pres_wf;
          try (subst; remember (ren_commute_str_wf_ren m1); now simpl in *); clear HeqRf1 Rf1.

      assert (@ctxt_app _ (m1 + m_bbhs) (m0 + m_hol) (zero (m1 + m_bbhs)) (G8 ⊗ zero m_hol) ≡[m1 + (m_bbhs + m0) + m_hol]
          lctxt_rename Rf2 (G8 ⊗ zero m_hol)). {
        replace (m1 + (m_bbhs + m0) + m_hol) with ((m1 + m_bbhs) + (m0 + m_hol)) by lia.
        subst; now rewrite weaken_ren_lctxt_rename.
      }
      rewrite H; clear H.
      replace (m1 + (m_bbhs + m0) + m_hol) with (m1 + m_bbhs + (m0 + m_hol)) by lia;
          apply rename_fvar_pres_wf;
          try (subst; apply weaken_ren_wf_ren); clear HeqRf2 Rf2.

      assert (@ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 1 1)) (zero n_free)
          ≡[n1 + (n0 + 1) + n_free] (lctxt_rename Rr ((D8 ⊗ flat_ctxt 1 1) ⊗ zero n_free))). {
        replace (n1 + (n0 + 1) + n_free) with (n1 + (n0 + 1 + n_free)) by lia.
        subst; rewrite weaken_ren_lctxt_rename; now repeat rewrite ctxt_app_assoc.
      }
      rewrite H; clear H.
      replace (n1 + (n0 + 1) + n_free) with (n1 + (n0 + 1 + n_free)) by lia;
          apply rename_rvar_pres_wf; try (subst; apply weaken_ren_wf_ren); clear HeqRr Rr.
      
      apply wf_weaken_free_vars with (m' := 0) (n' := n_free) in WFP.
      rewrite Nat.add_0_r, ctxt_app_l in WFP; simpl.
      now repeat rewrite Nat.add_assoc in *.

    + now rewrite sum_zero_l.
    + rewrite <- sum_assoc; repeat rewrite lctxt_sum_app_dist; 
          repeat rewrite sum_zero_l.
      solve_ctxt_eq.
Qed.









Lemma wf_prim_step :
  forall m n t t',
    wf_term m n t ->
    prim_step t t' ->
    wf_term m n t'.
Proof.
  intros. inversion H0; subst; clear H0.
  - eapply wf_prim_step_nul; eauto.
  - eapply wf_prim_step_emp; eauto.
  - eapply wf_prim_step_tup; eauto.
  - eapply wf_prim_step_app_same_scope; eauto.
  - eapply wf_prim_step_app_diff_scope; eauto.
  - eapply wf_prim_step_req; eauto.
Qed.

Lemma wf_step :
  forall m n t t',
    wf_term m n t ->
    step t t' ->
    wf_term m n t'.
Proof.
  intros. inversion H0; subst; clear H0.
  eapply wf_prim_step; try (exact H2).
  eapply tpo_wf_seq; try symmetry; eauto.
Qed.

Lemma wf_multi_step :
  forall m n t t',
    wf_term m n t ->
    multi_step t t' ->
    wf_term m n t'.
Proof.
  intros. induction H0; auto.
  apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n H1.
  eapply wf_step; eauto.
Qed.
































(*

b1 || b2






True =  \ (?t, ?f, r). t r
False = \ (?t, ?f, r). f r

\setTrue (r) = r <- True
\setFalse (r) = r <- False

b1 : 1 -> Bool
Bool := all R. !R -o !R -o R


OR = 
\ (?b1, ?b2, r). [r1 r2]
  b1 r1
  b2 r2
  r2 <- ?b2res

  \callR2 (r) = b2res (setTrue, setFalse, r)
  
  r1 (setTrue, callR2, r)

==> True r




IF =  OR (?b1, ?b2, (?tb, ?fb, r))
IF (?b, ?tb, ?fb) = 






*)
