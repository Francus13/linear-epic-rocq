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



(* Extending Renamings and Contexts ---------------------------------------------------------- *)

Ltac lia_destruct :=
  repeat match goal with
  | [ H: context[lt_dec ?R1 ?R2] |- _ ] => destruct (lt_dec R1 R2); try lia
  end;
  repeat match goal with
  | [ H: context[Nat.eq_dec ?R1 ?R2] |- _ ] => destruct (Nat.eq_dec R1 R2); subst; try lia
  end.

Ltac lia_goal :=
  repeat match goal with
  | [ |- context[lt_dec ?R1 ?R2] ] => destruct (lt_dec R1 R2); try lia
  | [ |- context[Nat.eq_dec ?R1 ?R2] ] => destruct (Nat.eq_dec R1 R2); try lia
  end.



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
Proof.
  unfold wf_ren, rename_var; intros; split.
  all: destruct (lt_dec x n); destruct (lt_dec y n); 
        destruct (Nat.eq_dec x0 x); destruct (Nat.eq_dec x0 y); lia.
Qed.

Lemma rename_var_correct :
  forall n_scope n x y,
    x < n \/ y < n ->
    rename_var n_scope n x y x = rename_var n_scope n x y y.
Proof.
  intros. unfold rename_var.
  destruct (lt_dec x n); destruct (lt_dec y n);
      destruct (Nat.eq_dec x x); destruct (Nat.eq_dec y x);
      destruct (Nat.eq_dec x y); destruct (Nat.eq_dec y y);
      lia.
Qed.

Lemma rename_var_correct_y :
  forall n_scope n x y,
    x < n ->
    rename_var n_scope n x y y = y.
Proof.
  intros. unfold rename_var.
  destruct (lt_dec x n); try lia.
  destruct (Nat.eq_dec y x); auto.
Qed.

Lemma rename_var_correct_x :
  forall n_scope n x y,
    ~ (x < n) ->
    rename_var n_scope n x y x = x.
Proof.
  intros. unfold rename_var.
  destruct (lt_dec x n); try lia.
  destruct (lt_dec y n); destruct (Nat.eq_dec x y); auto.
Qed.

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



Lemma add_fvars_wf_hs_fun :
  forall m_new Et m_hol n_hol G_hol D_hol,
    wf_hs_fun (add_fvars m_new) (hole_scope Et)
        m_hol n_hol G_hol D_hol
        (m_hol + m_new) n_hol (G_hol ⊗ zero m_new) D_hol.
Proof.

Admitted.

Lemma add_rvars_wf_hs_fun :
  forall n_new Et m_hol n_hol G_hol D_hol,
    wf_hs_fun (add_rvars n_new) (hole_scope Et)
        m_hol n_hol G_hol D_hol
        m_hol (n_hol + n_new) G_hol (D_hol ⊗ zero n_new).
Proof.

Admitted.



(* Renames rvars in a lambda body for its application
    - n rvars are bound in the lambda body
    - n_app rvars are bound in the application's scope
    - r_arg is the application's rvar argument   *)
Definition ready_body_rvar (n_app n r_arg : nat) (P : proc) : proc :=
    (* Weaken the scope : [n + 1] -> [n_app + n + 1] *)
  let P1 := rename_rvar_proc (weaken_ren (n + 1) n_app) P in
    (* Equate the single free rvar (i.e. the parameter) with the argument r_arg *)
  let n_total := n + 1 + n_app in
  par (req (n + n_app) r_arg) P1.

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












(* Useful tactics for preservation *)

Ltac destr_inv_fill_wf H := apply inv_fill_wf in H;
  destruct H as (m_hol & n_hol & G_hol & D_hol & H1 & H2).

Ltac rewrite_ctxt_equivs :=
repeat match goal with
| H : ?C1 ≡[ ?n ] ?C2 |- _ => rewrite H in *; clear H
end.



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
  inversion WFP2; inversion WFP1; inversion WFO; inversion WFT; 
      existT_eq; subst; rewrite_ctxt_equivs; rewrite sum_zero_l, sum_zero_r in *;
      clear WFP1 WFP0 WFO WFT HN' G0 D0 G1 D1 G2 D2.
  eapply fill_wf_pres_term with 
      (m_hol := m_hol + m0) (n_hol := n_hol + (n0 + 1))
      (G_hol := G3 ⊗ G6) 
      (D_hol := (n_hol + (n0 + 1)) [r ↦ 1] ⨥
                (n_hol + (n0 + 1)) [(n0 + bound_rvars_at_hole_scope Et) ↦ 2] ⨥
                ((one n_hol rf ⨥ D3) ⊗ D6 ⊗ zero 1)).
  2: eapply wf_par with
      (G1 := (zero m_hol ⊗ G6))
      (D1 := ((n_hol + (n0 + 1)) [r ↦ 1] ⨥
              (n_hol + (n0 + 1)) [n0 + bound_rvars_at_hole_scope Et ↦ 2]) ⨥
              (zero n_hol ⊗ D6 ⊗ zero 1)).
  3: apply wf_weaken_free_vars; eauto.
  3: now rewrite lctxt_sum_app_dist, sum_zero_l, sum_zero_r.
  (* FRAN: How to make this next rewrite cleaner? *)
  3: rewrite <- (sum_assoc ((n_hol + (n0 + 1)) [r ↦ 1] ⨥ 
                            (n_hol + (n0 + 1)) [n0 + bound_rvars_at_hole_scope Et ↦ 2])). 
  3: rewrite <- (ctxt_app_assoc (zero n_hol)).
  3: now rewrite lctxt_sum_app_dist, sum_zero_l, sum_zero_r, ctxt_app_assoc.
  (* 3: now rewrite sum_zero_l.
  3: reflexivity. *)

  - unfold Et_shifted; clear Et_shifted new_body.
    unfold shift_hs_by_term_vars; simpl.
    do 2 (try eapply mutate_hole_scope_wf); eauto.
    * apply add_fvars_wf_hs_fun.
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


































































