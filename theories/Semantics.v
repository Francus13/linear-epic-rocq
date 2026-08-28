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

From LEpic Require Import Contexts Syntax EvalContexts.
Import Renamings.

Local Open Scope program_scope.
Local Open Scope bool_scope.




(* Useful tactics *)

Ltac destr_inv_fill_wf H := apply inv_fill_wf in H;
  destruct H as (m_hol & n_hol & G_hol & D_hol & H1 & H2).

Ltac rewrite_ctxt_equivs :=
repeat match goal with
| H : ?C1 ≡[ ?n ] ?C2 |- _ => rewrite H in *; clear H
end; repeat match goal with
| H : ?C1 ≡[ ?n ] ?C2 |- _ => rewrite <- H in *; clear H
end.



(* Extending Renamings and Contexts ---------------------------------------------------------- *)

(* FRAN: This is inconsistent in canonicity with ren_id,
    since it weakens variables out of scope.
    Update: It actually needs to weaken variables out of scope
    so that we don't need to track the free variables in the semantics.
    Also why lt_dc instead of < (lt)? *)
(* A renaming that changes the last m variables to (m + m'') *)
Definition weaken_tail_ren (m m' m'' : nat) : ren (m' + m) (m' + m'' + m) :=
  fun f =>
    if lt_dec f m' then f 
    else f + m''.

Definition weaken_ren (m n : nat) : ren m (n + m) :=
  weaken_tail_ren m 0 n.

Lemma ren_shift_weaken_commute : 
forall (m' m0 m1 m2 : nat),
  ren_shift m' (weaken_tail_ren m0 m1 m2) =
  weaken_tail_ren m0 (m' + m1) m2.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  unfold ren_shift, weaken_tail_ren, ctxt_app, ren_id.
  lia_goal.
Qed.



(* A renaming that commutes two adjacent variable spaces 
    (m1 and m2 in length) starting after m0 variables *)
Definition ren_commute_str m0 m1 m2 m3 : 
        ren (m0 + (m1 + m2) + m3) (m0 + (m2 + m1) + m3) :=
  fun x =>
    if (lt_dec x m0) then x 
    else if (lt_dec x (m0 + m1)) then (x + m2)
         else if (lt_dec x (m0 + m1 + m2)) then (x - m1)
                  else x.












(* Operational Semantics --------------------------------------------------- *)

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







(* Helper functions for function application *)

(* Adds new bound vars to the end of the top scope, shifting all free fvars *)
Definition add_fvars m_new Et : EC_term :=
  let Et_new := rename_fvar_EC_term (weaken_ren 0 m_new) Et in
  match Et_new with Ebag m n EP => Ebag (m + m_new) n EP end.

(* Adds new bound fvars to the hole scope, shifting all its free fvars *)
Definition add_fvars_hole_scope m_new : EC_term -> EC_term :=
  mutate_hole_scope (add_fvars m_new).

(* Adds new bound rvars to the end of the top scope *)
Definition add_rvars n_new Et : EC_term :=
  let Et_new := rename_rvar_EC_term (weaken_ren 0 n_new) Et in
  match Et_new with Ebag m n EP => Ebag m (n + n_new) EP end.

(* Adds new bound rvars to the hole scope, shifting all its free fvars *)
Definition add_rvars_hole_scope n_new : EC_term -> EC_term :=
  mutate_hole_scope (add_rvars n_new).



(* Adding vars preserves well-formedness *)
Lemma add_fvars_rename :
    (forall t m m_new m_free n,
      wf_term (m + m_free) n t ->
      wf_term (m + m_new + m_free) n
          (rename_fvar_term (ren_shift m (weaken_ren 0 m_new)) t))
/\  (forall P m m_new m_free n G G_free D,
      wf_proc (m + m_free) n (@ctxt_app _ m m_free G G_free) D P ->
      wf_proc (m + m_new + m_free) n (G ⊗ zero m_new ⊗ G_free) D
          (rename_fvar_proc (ren_shift m (weaken_ren 0 m_new)) P))
/\  (forall o m m_new m_free n G G_free D,
      wf_oper (m + m_free) n (@ctxt_app _ m m_free G G_free) D o ->
      wf_oper (m + m_new + m_free) n (G ⊗ zero m_new ⊗ G_free) D
          (rename_fvar_oper (ren_shift m (weaken_ren 0 m_new)) o)).
Proof.
  apply tpo_ind; simpl; intros.
  all: try (inversion H1; clear H1); try (inversion H0; clear H0); 
          try (inversion H; clear H); existT_eq; subst.
  5: apply sum_app_inv_ctxt in HG; dest_conj_disj_exist; rewrite_ctxt_equivs.
  all: econstructor; eauto.
  all: try reflexivity.
  all: try solve [
    rewrite <- app_zero in HG;
    assert (HG' := HG); apply ctxt_app_inv_l_eq in HG;
        apply ctxt_app_inv_r_eq in HG'; rewrite HG, HG';
    now repeat rewrite app_zero
  ].
  all: try solve [
    unfold ren_shift, ren_id, weaken_ren, weaken_tail_ren;
    solve_ctxt_eq
  ].

  (* Ebag Process wf *)
  - repeat rewrite <- app_zero, ctxt_app_assoc;
        rewrite ren_shift_combine;
        repeat rewrite Nat.add_assoc in *.
    specialize H with (m + m0) m_new m_free (n + n0)
        (G ⊗ zero m0) (zero m_free) (D ⊗ flat_ctxt 1 n0).
        repeat rewrite Nat.add_0_r in *;
        apply H; clear H.
    now rewrite <- ctxt_app_assoc, app_zero.

  (* Bng base case for renaming *)
  - clear HD; unfold ren_shift, weaken_ren, ren_id, weaken_tail_ren in *.
    solve_ctxt_eq; subst.
    1, 2, 3: specialize HG with x; solve_ctxt_eq.
    1, 3: replace (x - (m + m_new)) with (x - m_new - m) by lia;
          specialize HG with (x - m_new); solve_ctxt_eq.
    replace (m + (f - m + m_new) - (m + m_new)) with (f - m) by lia.
      specialize HG with f; solve_ctxt_eq.
Qed.

Lemma add_rvars_rename :
    (forall (t : term), True)
/\  (forall P m n n_new n_free G D D_free,
      wf_proc m (n + n_free) G (@ctxt_app _ n n_free D D_free) P ->
      wf_proc m (n + n_new + n_free) G (D ⊗ zero n_new ⊗ D_free)
          (rename_rvar_proc (ren_shift n (weaken_ren 0 n_new)) P))
/\  (forall o m n n_new n_free G D D_free,
      wf_oper m (n + n_free) G (@ctxt_app _ n n_free D D_free) o ->
      wf_oper m (n + n_new + n_free) G (D ⊗ zero n_new ⊗ D_free)
          (rename_rvar_oper (ren_shift n (weaken_ren 0 n_new)) o)).
Proof.
  apply tpo_ind; simpl; intros.
  all: try (inversion H1; clear H1); try (inversion H0; clear H0); 
          try (inversion H; clear H); existT_eq; subst.
  all: try (apply sum_app_inv_ctxt in HD; dest_conj_disj_exist; rewrite_ctxt_equivs).
  all: econstructor; eauto.
  all: try reflexivity.
  all: try solve [
    rewrite <- app_zero in HD;
    assert (HD' := HD); apply ctxt_app_inv_l_eq in HD;
        apply ctxt_app_inv_r_eq in HD'; rewrite HD, HD';
    now repeat rewrite app_zero
  ].
  all:
    try rename HD into H;
    unfold ren_shift, ren_id, weaken_ren, weaken_tail_ren in *; 
    solve_ctxt_eq; subst;
    try rename x into x3;
    try solve [try specialize H with x3;
                try specialize H0 with x3; solve_ctxt_eq];
    try solve [replace (x3 - (n + n_new)) with (x3 - n_new - n) by lia;
        try specialize H with (x3 - n_new);
        try specialize H0 with (x3 - n_new); solve_ctxt_eq];
    try solve [ try rename r1 into r;
        replace (n + (r - n + n_new) - (n + n_new)) with (r - n) by lia;
        try specialize H with r;
        try specialize H0 with r; solve_ctxt_eq];
    try solve [ try rename r2 into r;
        replace (n + (r - n + n_new) - (n + n_new)) with (r - n) by lia;
        try specialize H with r;
        try specialize H0 with r; solve_ctxt_eq].
Qed.



(* Adding vars to hs transforms hs wf *)
Lemma add_fvars_wf_hs_fun :
  forall m_new (G_new : lctxt m_new) m_free (G_free : lctxt m_free)
        m n EP n_hol G D_hol,
    (forall x, x < m_new -> G_new x = 1) ->
    wf_hs_fun (add_fvars m_new) (Ebag m n EP)
        (m + m_free) n_hol (G ⊗ G_free) D_hol
        (m + m_new + m_free) n_hol (G ⊗ G_new ⊗ G_free) D_hol.
Proof.
  unfold wf_hs_fun; intros.
  inversion H1; existT_eq; subst; clear H1.
  assert (m0 = m_free) by 
      (apply wf_hs_var_bounds_eq_proc in WFP; auto; lia); subst.
  unfold add_fvars; simpl.
  eapply wf_Ebag with (G := G0 ⊗ G_new); eauto.
  - intros. destruct (lt_dec x m).
    + rewrite ctxt_app_l; eauto.
    + rewrite ctxt_app_r; try lia. apply H; lia.
  - clear UG UD H; generalize dependent WFP; generalize dependent G0;
        generalize (@ctxt_app _ n n0 D (flat_ctxt 1 n0)) as D'.
    
    induction EP; simpl; intros; inversion WFP; existT_eq; subst; 
        rewrite HD in *; clear HD WFP.
    + econstructor; auto; try reflexivity.
      assert (HG' := HG);
          apply ctxt_app_inv_l_eq in HG;
          apply ctxt_app_inv_r_eq in HG'; 
          now rewrite HG, HG'.
    + discriminate.
    + apply sum_app_inv_ctxt in HG; dest_conj_disj_exist.
      assert (H4 := H3); apply sum_zero_inv_l_eq in H3;
          apply sum_zero_inv_r_eq in H4.
      rewrite_ctxt_equivs; clear x1 x2.
      econstructor; try reflexivity.
      * apply IHEP; eauto.
      * apply add_fvars_rename; eauto.
      * repeat rewrite lctxt_sum_app_dist; 
        now repeat rewrite sum_zero_r.
Qed.

Lemma add_rvars_wf_hs_fun :
  forall n_new (D_new : lctxt n_new) n_free (D_free : lctxt n_free)
        m n EP m_hol G_hol D,
    (forall x, x < n_new -> D_new x = 2 \/ D_new x = 0) ->
    wf_hs_fun (add_rvars n_new) (Ebag m n EP)
        m_hol (n + n_free) G_hol (D ⊗ D_free)
        m_hol (n + n_new + n_free) G_hol (D ⊗ D_new ⊗ D_free).
Proof.
  unfold wf_hs_fun; intros.
  inversion H1; existT_eq; subst; clear H1.
  assert (n0 = n_free) by 
      (apply wf_hs_var_bounds_eq_proc in WFP; auto; lia); subst.
  unfold add_rvars; simpl.
  eapply wf_Ebag with (D := D0 ⊗ D_new); eauto.
  - intros. destruct (lt_dec x n).
    + rewrite ctxt_app_l; eauto.
    + rewrite ctxt_app_r; try lia. apply H; lia.
  - clear UG UD H. generalize dependent WFP; generalize dependent D0;
        generalize dependent (flat_ctxt 1 n_free);
        generalize (@ctxt_app _ m m0 G (zero m0)) as G'.
    
    induction EP; simpl; intros; inversion WFP; existT_eq; subst; 
        rewrite HG in *; clear HG WFP.
    + econstructor; auto; try reflexivity.
      assert (HD' := HD); apply ctxt_app_inv_l_eq in HD;
          apply ctxt_app_inv_r_eq in HD'; now rewrite HD, HD'.
    + discriminate.
    + apply sum_app_inv_ctxt in HD; dest_conj_disj_exist.
      rewrite_ctxt_equivs.
      econstructor; try reflexivity.
      * apply IHEP; eauto.
      * apply add_rvars_rename; eauto.
      * repeat rewrite lctxt_sum_app_dist; 
        now repeat rewrite sum_zero_r.
Qed.



(* Gives the new variable after an application 
    If x is one of the bound vars in the applicaiton scope
    (i.e. x < bound) then x is unchanged.
    Otherwise, x is weakened by the number of added vars
    (those bound by the function body, given by body) *)
Definition ready_var (x bound body : nat) : nat :=
  x + (if lt_dec x bound then 0 else body).

(* Renames rvars in a lambda body for its application
    - n rvars are bound in the lambda body
    - n_app rvars are bound in the application's scope
    - r_arg is the application's rvar argument   *)
Definition ready_body_rvar (n_app n r_arg : nat) (P : proc) : proc :=
    (* Weaken the scope : [n + 1] -> [n_app + n + 1] *)
  let P1 := rename_rvar_proc (weaken_ren (n + 1) n_app) P in
    (* Equate the single free rvar (i.e. the parameter) with the argument rvar *)
  let new_arg := ready_var r_arg n_app n in
  par (req (n + n_app) new_arg) P1.

(* Renames fvars in a lambda body for an application,
   for when the lambda and application are in the same scope
          (the two cases require different treatments of the fvars 
           bound in the scope containing the lambda)
    - m fvars are bound in the lambda body
    - m_app fvars are bound in the application/lambda's scope   *)
Definition ready_body_fvar_same_scope (m_app m : nat) (P : proc) : proc :=
    (* Move the m bindings to end of new local scope : 
        [m + m_app + m_free] -> [m_app + m + m_free] *)
  rename_fvar_proc (ren_commute_str 0 m m_app 0) P.

(* Renames fvars in a lambda body for an application,
   for when the lambda and application are in different scopes (read above)
    - m fvars are bound in the lambda body
    - m_app fvars are bound in the application's scope
    - m_inner fvars are bound between the lambda's scope and application's scope (exclusive)    *)
Definition ready_body_fvar_diff_scope (m_inner m_app m : nat) (P : proc) : proc :=
    (* Weaken the scope : [m + m_free] -> [m_app + m_inner + m + m_free] *)
  let P1 := rename_rvar_proc (weaken_ren m (m_app + m_inner)) P in
    (* Move the m bindings to end of new local scope : 
          [m_app + m_inner + m + m_free] -> [m_app + m + m_inner + m_free] *)
  rename_fvar_proc (ren_commute_str m_app m_inner m 0) P1.


(* Readies a lambda body for insertion into the application's scope
    - Et is the context of the application site
    - t is the lambda's term
    - r_arg is the argument
   In same_scope, the lambda definition is expected to be in the
      application scope (which is the hole scope). 
   In diff_scope, the lambda definition is expected to be free from Et. *)

Definition ready_body_same_scope (Et : EC_term) (t : term) (r_arg : nat) : proc :=
  match t with bag m n P =>
    (* Do rvar renaming *)
    let n_app := bound_rvars_at_hole_scope Et in
    let P' := ready_body_rvar n_app n r_arg P in
    (* Do fvar renaming *)
    let m_app := bound_fvars_at_hole_scope Et in
    ready_body_fvar_same_scope m_app m P'
  end.

Definition ready_body_diff_scope (Et : EC_term) (t : term) (r_arg : nat) : proc :=
  match t with bag m n P =>
    (* Do rvar renaming *)
    let n_app := bound_rvars_at_hole_scope Et in
    let P' := ready_body_rvar n_app n r_arg P in
    (* Do fvar renaming *)
    let m_app := bound_fvars_at_hole_scope Et in
    let m_inner := bound_fvars_before_hole_scope Et in
    ready_body_fvar_diff_scope m_inner m_app m P'
  end.

Definition shift_hs_by_term_vars (t : term) (Et : EC_term) : EC_term :=
  let Et' := add_fvars_hole_scope (get_fvars t) Et in
  add_rvars_hole_scope (get_rvars t + 1) Et'.








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













































(* Small Step *)
              
Inductive prim_step : term -> term -> Prop :=
| step_par_nul :    (*  Et <=[ P | nul ]  -->  Et <=[ P ]  *)
  forall Et P,
    prim_step
      (Et <=[ par P nul ])
      (Et <=[ P ])

| step_emp_cut :    (*  Et <=[ r <- () | r <- () ]  -->  Et <=[ nul ]  *)
  forall Et r,
    prim_step
      (Et <=[ par (def r emp) (def r emp) ])
      (Et <=[ nul ])

| step_tup_cut :    (*  Et <=[ r <- (r1, r2) | r <- (r1', r2') ]  *)
  forall Et r r1 r2 r1' r2',    (*  -->  ET{r1=r1',r2=r2'} <=[ nul ]  *)
    prim_step
      (Et <=[ par (def r (tup r1 r2)) (def r (tup r1' r2')) ])
      (Et <=[ par (req r1 r1') (req r2 r2') ])
      
| step_app_same_scope :    (*  Et <=[ rf <- lam r'. t | rf <- ?f | f r ]  *)
  forall Et t f rf r,    (*  -->  Et <=[ '' | '' | fresh_body(t){r=r'} ]  *)
      (* Get the freshened and applied body *)
    let new_body := ready_body_same_scope Et t r in
      (* Shift the vars in the application's scope *)
    let Et_shifted := shift_hs_by_term_vars t Et in
    prim_step
      (Et         <=[ (par (app f r)
                      (par (def rf (lam t))
                           (def rf (bng f)))) ])
      (Et_shifted <=[ (par (new_body)
                      (par (def rf (lam t))
                           (def rf (bng f)))) ])
      
| step_app_diff_scope :    (*  Et' <=[ rf <- lam r'. t | rf <- ?f | Et <=[ f r ] ]  *)
  forall Et Et' t f rf rl r,    (*  -->  Et' <=[ '' | '' | Et <=[ fresh_body(t){r=r'} ] ]  *)
      (* Ensure the fvars in the definition and application scopes agree *)
    let f' := f + (bound_fvars_to_hole Et) in
      (* Get the freshened and applied body *)
    let new_body := ready_body_diff_scope Et t r in
      (* Shift the vars in the application's scope *)
    let Et_shifted := shift_hs_by_term_vars t Et in
    prim_step
      (Et' <=[ (par (def rl (lam (Et         <=[ app f' r ])))
               (par (def rf (lam t))
                    (def rf (bng f)))) ])
      (Et' <=[ (par (def rl (lam (Et_shifted <=[ new_body ])))
               (par (def rf (lam t))
                    (def rf (bng f)))) ])

| step_req :    (*  Et <=[ r1 = r2 ]  -->  (rename_at_hole_scope Et r1 r2) <=[ nul ]  *)
  forall Et r1 r2,
    let n := bound_rvars_at_hole_scope Et in
    r1 < n \/ r2 < n ->
    prim_step
      (Et <=[ req r1 r2 ])
      ((rename_at_hole_scope n r1 r2 Et) <=[ nul ])

(* No motivating reason to have right now *)
(* | step_remove_function :
  forall Et t f rf,
    can_remove_function f Et = true ->
    prim_step
    (Et <=[ (par (def rf (lam t))
                (def rf (bng f))) ])
    (Et <=[ nul ]) *)
.


Inductive step : term -> term -> Prop :=
| step_equiv : forall t1 t1' t2' t2,
    t1 ≈t t1' ->
    prim_step t1' t2' ->
    t2' ≈t t2 ->
    step t1 t2
.















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
    let Et_shifted := shift_hs_by_term_vars t Et in
    wf_term m n (Et         <=[ (par (app f r)
                                (par (def rf (lam t))
                                     (def rf (bng f)))) ]) ->
    wf_term m n (Et_shifted <=[ (par (new_body)
                                (par (def rf (lam t))
                                     (def rf (bng f)))) ]).
Proof.
  intros. destr_inv_fill_wf H.
  inversion H1; inversion WFP1; existT_eq; subst; 
      clear H1 WFP1; rewrite_ctxt_equivs.
  rewrite sum_zero_l in H2.
  destruct t; simpl in *.
  inversion WFP2; inversion WFP1; inversion WFP0; 
      inversion WFO; inversion WFO0; inversion WFT; 
      existT_eq; subst; rewrite_ctxt_equivs; 
      rewrite sum_zero_l, sum_zero_r in *;
      unfold one in H2 at 3 4; unfold one in WFP2 at 2 3; 
          rewrite delta_sum in *; simpl in *;
      clear WFP1 WFP0 WFO WFO0 WFT G0 D0 G1 D1 G2 D2 G3 D3.

  destruct (hole_scope Et) eqn:HS.
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

  remember (ready_var r n1 n0) as r_new.
  apply fill_wf_pres_term with 
      (m_hol := m1 + m0 + m_free)
      (n_hol := n1 + (n0 + 1) + n_free)
      (G_hol := @ctxt_app _ (m1 + m0) m_free ((m1 [f ↦ 1]) ⊗ G8) (zero m_free))
      (D_hol := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥
                (@ctxt_app _ (n1 + (n0 + 1)) n_free
                    (n1 [rf ↦ 2] ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free))).
  (* Split wf of the new body and the function *)
  2: apply wf_par with
      (G1 := @ctxt_app _ (m1 + m0) m_free (zero m1 ⊗ G8) (zero m_free))
      (D1 := (n1 + (n0 + 1) + n_free) [r_new ↦ 1] ⨥
                (@ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free)))
      (G2 := (@ctxt_app _ (m1 + m_free) m0 ((m1 [f ↦ 1]) ⊗ zero m_free) (zero m0)))
      (D2 := (@ctxt_app _ (n1 + n_free) (n0 + 1) ((n1 + n_free) [rf ↦ 2]) (zero (n0 + 1)))).
  (* Function definition and naming are well-formed (from assumption) *)
  3: replace (m1 + m0 + m_free) with (m1 + m_free + m0) by lia;
        replace (n1 + (n0 + 1) + n_free) with (n1 + n_free + (n0 + 1)) by lia;
        eapply wf_weaken_free_vars; eauto.
  (* G = G1 + G2 *)
  3: unfold one; rewrite sum_commutative;
        rewrite delta_app_zero_r; auto;
        now replace ((m1 + m0 + m_free) [f ↦ 1]) with ((m1 + m_free + m0) [f ↦ 1])
            by (now replace (m1 + m_free + m0) with (m1 + m0 + m_free) by lia).
  (* D = D1 + D2 *)
  3: assert (rf < n1) by (
          replace n1 with (bound_rvars_at_hole_scope Et) by
              (unfold bound_rvars_at_hole_scope, apply_at_hole_scope; now rewrite HS);
          eapply rvar_bound_hs; eauto;
          eapply max_rvar_hole_EC_wf in H2; eauto;
          unfold one in *; rewrite sum_correct, delta_id, delta_neq in *; auto;
              destruct (Nat.eq_dec r rf); auto; subst; rewrite delta_id in *; lia
      );
      rewrite <- (delta_app_zero_r _ _ rf); auto;
      replace (@ctxt_app _ (n1 + n_free) (n0 + 1) (n1 [rf ↦ 2] ⊗ zero n_free) (zero (n0 + 1)))
          with (@ctxt_app _ (n1 + n0 + 1) n_free (((n1 [rf ↦ 2]) ⊗ (zero n0)) ⊗ zero 1) (zero n_free)) by
              (repeat rewrite delta_app_zero_r; try lia;
              now replace (n1 + n0 + 1 + n_free) with (n1 + n_free + (n0 + 1)) by lia);
      rewrite <- sum_assoc;
      replace ((@ctxt_app _ (n1 + (n0 + 1)) n_free (zero n1 ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free))
                  ⨥ (((n1 [rf ↦ 2] ⊗ zero n0) ⊗ zero 1) ⊗ zero n_free)) 
          with (@ctxt_app _ (n1 + (n0 + 1)) n_free (n1 [rf ↦ 2] ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free)) by
              (repeat rewrite ctxt_app_assoc; repeat rewrite Nat.add_assoc;
              repeat rewrite lctxt_sum_app_dist, sum_zero_r;
              now rewrite sum_zero_l);
      now repeat rewrite Nat.add_assoc.

  - unfold Et_shifted; clear Et_shifted new_body.
    unfold shift_hs_by_term_vars; simpl.

    assert (H := H2); apply wf_hs_split_G_hol in H;
        destruct H as [G_bound ?].
    2: unfold bound_fvars_at_hole_scope, apply_at_hole_scope;
        now rewrite HS.
    rewrite H in *; clear H.

    do 2 (try eapply mutate_hole_scope_wf); eauto.
    + destruct (hole_scope Et); rewrite HS; clear HS.
      apply add_fvars_wf_hs_fun; eauto.
    + assert (exists EP0,
        hole_scope (add_fvars_hole_scope m0 Et) = Ebag (m1 + m0) n1 EP0).
      {
        unfold add_fvars_hole_scope. 
        rewrite hole_scope_mutate_hole_scope, HS.
        1: cbn; eauto.
        intros; destruct Et0; simpl.
        generalize dependent EP0.
        EP_ind_unsafe IH EP0; auto.
      }

      destruct H; rewrite H.
      (* repeat rewrite Nat.add_assoc. *)
      unfold ready_var in Heqr_new; destruct (lt_dec r n1).
      * rewrite Nat.add_0_r in Heqr_new; subst.
        replace ((n1 + (n0 + 1) + n_free) [r ↦ 1] ⨥ ((n1 [rf ↦ 2] ⊗ (D8 ⊗ flat_ctxt 2 1)) ⊗ zero n_free))
            with (@ctxt_app _ (n1 + (n0 + 1)) n_free ((n1 [r ↦ 1] ⨥ n1 [rf ↦ 2]) ⊗ (D8 ⊗ flat_ctxt 2 1)) (zero n_free)) by
                (repeat rewrite <- delta_app_zero_r; try lia; 
                repeat rewrite lctxt_sum_app_dist;
                now repeat rewrite sum_zero_l).


      unfold wf_hs_fun; intros.
     
      remember add_rvars_wf_hs_fun; clear Heqw.
      unfold wf_hs_fun in w.


      (* assert (H1 := H0); apply wf_hs_var_bounds_eq in H1;
          destruct H1; subst; simpl in *; auto. *)
      (* replace (m1 + m2 + m0) with (m1 + m0 + m2) by lia.
      inversion H0; existT_eq; subst. *)

      apply w; clear w.
      admit. auto.
      rewrite H in H1. apply H1.

      
    * admit.
      (* apply add_rvars_wf_hs_fun. *)
  - unfold new_body; clear Et_shifted new_body.
    (* assert (wf_term m_hol 1 (bag m0 n0 P)) by
        (inversion WFP2; inversion WFP1; now inversion WFO). *)
    unfold ready_body_fvar_same_scope, ready_body_rvar; simpl.
    (* destruct rem_hole_rvar_EC_wf; clear H.
    eapply H0. *)
    econstructor.
    3: now rewrite sum_zero_l.
    (* 3: reflexivity. *)
    + econstructor; eauto; try reflexivity; try lia.
      apply wf_hs_vars_correct in H2; lia.
    + admit.
      (* destruct rename_fvar_pres_wf.
      destruct H0. clear H H1.
      rewrite (Nat.add_comm m0).
      apply H0. *)
    +


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
  - admit.
  - admit.
  - eapply wf_prim_step_req; eauto.
Admitted.
































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


































































