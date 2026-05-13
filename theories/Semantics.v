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

(* z{y/x} *)
Definition rename_var n (x:var) (y:var) : ren n n :=
  fun z => if Nat.eq_dec z x then y else z.

Lemma rename_var_wf :
  forall n x y,
    x < n -> y < n ->
    wf_ren (rename_var n x y).
Proof.
  unfold wf_ren, rename_var; intros; split.
  all: destruct (Nat.eq_dec x0 x); lia.
Qed.




(* Helper functions for tuple cuts *)
                  
(* Gives a "collapsed" renaming that only renames r1 to r2 *)
Definition rename_if_neq n (r1 r2 : nat) : ren n n :=
  if Nat.eq_dec r1 r2 then
    ren_id n
  else
    rename_var n r1 r2.

(* Gives a "collapsed" renaming that only renames r1 to r1' and r2 to r2'. 
    Used for stepping the cut (r <- (r1, r2) | r <- (r1', r2')) *)
Definition cut_renaming n (r1 r2 r1' r2':nat) : ren n n :=
  (* First, check if two variables in either pair are equal *)
  if Nat.eq_dec r1 r2 then
    rename_if_neq n r1' r2'
  else if Nat.eq_dec r1' r2' then
    rename_var n r1 r2
  (* Second, check if a variable is equal to its
      non-corresponding variable in the other pair *)
  else if Nat.eq_dec r1 r2' then
    rename_if_neq n r1' r2
  else if Nat.eq_dec r1' r2 then
    rename_var n r1 r2'
  (* Third, check if a variable is equal to its
      corresponding variable in the other pair *)
  else if Nat.eq_dec r1 r1' then
    rename_if_neq n r2 r2'
  else if Nat.eq_dec r2 r2' then
    rename_var n r1 r1'
  (* Now we know there are no equalities between the variables *)
  else
    @ren_compose n n nat (rename_var n r1 r1') (rename_var n r2 r2').


Lemma rename_if_neq_wf :
  forall n r1 r2,
    r1 < n -> r2 < n ->
    wf_ren (rename_if_neq n r1 r2).
Proof.
  unfold rename_if_neq; intros.
  destruct (Nat.eq_dec r1 r2).
  - apply wf_ren_id.
  - apply rename_var_wf; auto.
Qed.

Lemma cut_renaming_wf : 
  forall n r1 r2 r1' r2',
    r1 < n -> r2 < n -> r1' < n -> r2' < n ->
    wf_ren (cut_renaming n r1 r2 r1' r2').
Proof.
  intros; unfold cut_renaming.
  destruct (Nat.eq_dec r1 r2); destruct (Nat.eq_dec r1' r2');
      destruct (Nat.eq_dec r1 r2'); destruct (Nat.eq_dec r1' r2);
      destruct (Nat.eq_dec r1 r1'); destruct (Nat.eq_dec r2 r2');
      auto using wf_ren_compose, rename_var_wf, rename_if_neq_wf.
Qed.


(* TODO: Need to have the semantics track number of rvars in scope *)
(* Gives the number of rvars in scope at the hole *)
Definition scoped_rvars_at_hole : EC_term -> nat := 
  case_hole_scope_at_top 
    (get_rvars_Et) 
    (fun Et => 1 + (get_rvars_Et Et)).

Definition tuple_cut_hole_scope Et r1 r2 r1' r2' := 
  let ren := cut_renaming (scoped_rvars_at_hole Et) r1 r2 r1' r2' in
  mutate_under_hole_scope (rename_rvar_EC_proc ren) Et.



(* Helper functions for function application *)

(* Adds new bound fvars to the end of the top scope, shifting all free fvars *)
Definition add_fvars m_new Et : EC_term :=
  let Et_new := match Et with Ebag m n EP => Ebag (m + m_new) n EP end in
  rename_fvar_EC_term (weaken_ren 0 m_new) Et_new.

(* Adds new bound fvars to the hole scope, shifting all its free fvars *)
Definition add_fvars_hole_scope m_new : EC_term -> EC_term :=
  mutate_hole_scope (add_fvars m_new).


(* Renames rvars in a lambda body for its application
    - n rvars are bound in the lambda body
    - n_app rvars are bound in the application's scope
    - r_arg is the application's rvar argument   *)
Definition ready_body_rvar (n_app n r_arg : nat) (P : proc) : proc :=
    (* Weaken the scope : [n + 1] -> [n_app + n + 1] *)
  let P1 := rename_rvar_proc (weaken_ren (n + 1) n_app) P in
    (* Replace the single free rvar (i.e. the parameter) with the argument r_arg *)
  let n_total := n + 1 + n_app in
  rename_rvar_proc (rename_var n_total (n + n_app) r_arg) P1.

(* Renames fvars in a lambda body for an application,
   for when the lambda and application are in the same scope
          (the two cases require different treatments of the fvars 
           bound in the scope containing the lambda)
    - m fvars are bound in the lambda body
    - m_app fvars are bound in the application/lambda's scope   *)
Definition ready_body_fvar_same_scope (m_app m : nat) (P : proc) : proc :=
    (* Move the m bindings to end of new local scope : 
        [m + m_app + m_free] -> [m_app + m + m_free] *)
  rename_rvar_proc (ren_commute_str 0 m m_app 0) P.

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
  rename_rvar_proc (ren_commute_str m_app m_inner m 0) P1.


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
    let n_app := apply_at_hole_scope get_rvars_Et Et in
    let P' := ready_body_rvar n_app n r_arg P in
    (* Do fvar renaming *)
    let m_app := apply_at_hole_scope get_fvars_Et Et in
    ready_body_fvar_same_scope m_app m P'
  end.

Definition ready_body_diff_scope (Et : EC_term) (t : term) (r_arg : nat) : proc :=
  match t with bag m n P =>
    (* Do rvar renaming *)
    let n_app := apply_at_hole_scope get_rvars_Et Et in
    let P' := ready_body_rvar n_app n r_arg P in
    (* Do fvar renaming *)
    let m_app := apply_at_hole_scope get_fvars_Et Et in
    let m_inner := bound_fvars_before_hole_scope Et in
    ready_body_fvar_diff_scope m_inner m_app m P'
  end.



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
      ((tuple_cut_hole_scope Et r1 r2 r1' r2') <=[ nul ])
      
| step_app_same_scope :    (*  Et <=[ rf <- lam r'. t | rf <- ?f | f r ]  *)
  forall Et t f rf r,    (*  -->  Et <=[ '' | '' | fresh_body(t){r=r'} ]  *)
      (* Get the freshened and applied body *)
    let new_body := ready_body_same_scope Et t r in
      (* Shift the fvars in the application's scope *)
    let Et_shifted := add_fvars_hole_scope (get_fvars t) Et in
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
      (* Shift the fvars in the application's scope *)
    let Et_shifted := add_fvars_hole_scope (get_fvars t) Et in
    prim_step
    (Et' <=[ (par (def rl (lam (Et         <=[ app f' r ])))
             (par (def rf (lam t))
                  (def rf (bng f)))) ])
    (Et' <=[ (par (def rl (lam (Et_shifted <=[ new_body ])))
             (par (def rf (lam t))
                  (def rf (bng f)))) ])

| step_remove_function :
  forall Et t f rf,
    can_remove_function f Et = true ->
    prim_step
    (Et <=[ (par (def rf (lam t))
                (def rf (bng f))) ])
    (Et <=[ nul ])
.


Inductive step : term -> term -> Prop :=
| step_equiv : forall t1 t1' t2' t2,
    t1 ≈t t1' ->
    prim_step t1' t2' ->
    t2' ≈t t2 ->
    step t1 t2
.





(* Preservation of functions for prim_step *)

Ltac destr_inv_fill_wf H := apply inv_fill_wf in H;
  destruct H as (m_hol & n_hol & G_hol & D_hol & H1 & H2).

Ltac rewrite_ctxt_equivs :=
repeat match goal with
| H : ?C1 ≡[ ?n ] ?C2 |- _ => rewrite H in *; clear H
end.



(* Removing a resource requirement from the hole (changing 2 uses to 0 uses) 
   preserves EC well-formedness *)
Lemma rem_hole_rvar_EC_wf : 
  (forall (m n m_hol n_hol:nat) (G_hol : lctxt m_hol) (D_hol : lctxt n_hol)
        (Et : EC_term),
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall (r : rvar) (D_hol' : lctxt n_hol),
      D_hol ≡[n_hol] D_hol' ⨥ n_hol[r ↦ 2] ->
      r < n_hol ->
      D_hol' r = 0 ->
    wf_EC_term m n m_hol n_hol G_hol D_hol' Et)
  /\  
  (forall (m n m_hol n_hol:nat) (G : lctxt m) (D : lctxt n)
        (G_hol : lctxt m_hol) (D_hol : lctxt n_hol) (EP : EC_proc), 
    wf_EC_proc m n m_hol n_hol G D G_hol D_hol EP ->
    forall (r : rvar) (D_hol' : lctxt n_hol),
      D_hol ≡[n_hol] D_hol' ⨥ n_hol[r ↦ 2] ->
      r < n_hol ->
      D_hol' r = 0 ->
    (wf_EC_proc m n m_hol n_hol G D G_hol D_hol' EP)
    \/
    (n = n_hol /\ 
    exists (D' : lctxt n),
      D ≡[n] D' ⨥ n[r ↦ 2] /\
    wf_EC_proc m n m_hol n_hol G D' G_hol D_hol' EP)).
Proof.
  apply wf_EC_ind; intros.
  (* Ebag *)
  - destruct (H r D_hol' H0 H1 H2); clear H. 
    + econstructor; eauto.
    + destruct H3 as (H3 & D' & H4 & H5); subst.
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
      * rewrite <- HD4. rewrite HD1 in H5.
        destruct HD2; destruct H; clear H.
        -- rewrite <- H0, sum_zero_r. assumption.
        -- destruct (Nat.eq_dec n' 0); subst.
           ++ simpl in *. rewrite Nat.add_0_r in *. 
           rewrite (ctxt_app_l D1 (D2 ⨥ D2r)).
           rewrite (ctxt_app_l D1 D2) in H5. assumption.
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
  - left. constructor; auto. eapply H; eauto.
  (* Epar *)
  - destruct (H r D_hol'); auto.
    + left. econstructor; eauto.
    + right. destruct H3 as (H3 & D' & H4 & H5).
      split; auto. exists (D' ⨥ D2); repeat split.
      * rewrite <- sum_assoc, (sum_commutative D2), sum_assoc. 
        rewrite HD; rewrite H4. reflexivity.
      * econstructor; eauto; reflexivity.
Qed.



(* Doing a tuple cut preserves well-formedness *)
Lemma tuple_cut_ren_EC_wf : 
  forall (m n m_hol n_hol:nat) (G_hol : lctxt m_hol) (D_hol : lctxt n_hol)
        (Et : EC_term),
    wf_EC_term m n m_hol n_hol G_hol D_hol Et ->
    forall r1 r2 r1' r2',
      r1 < n_hol -> r2 < n_hol -> r1' < n_hol -> r2' < n_hol -> 
    wf_EC_term m n m_hol n_hol G_hol D_hol 
        (tuple_cut_hole_scope Et r1 r2 r1' r2').
Proof.
  intros. inversion H; existT_eq; subst.
  unfold tuple_cut_hole_scope, mutate_under_hole_scope.
  unfold scoped_rvars_at_hole, case_hole_scope_at_top, hole_scope. 
  destruct (inv_split_hole_scope (Ebag m0 n0 EP)); dest_conj_disj_exist.
  all: rewrite H4.
  - apply inv_split_hole_scope_Ehol_hs in H4. rewrite H4. simpl.
    eapply hole_scope_at_top_wf_simpl_proc in H4; eauto.
    destruct H4; subst.
    remember (cut_renaming n0 r1 r2 r1' r2') as R. (* For clarity *)
    eapply wf_Ebag with (D := lctxt_rename R D); eauto.
    2: rewrite <- (lctxt_rename_id (flat_ctxt 1 n)).
    2: rewrite <- lctxt_rename_app; auto using wf_ren_id.
    assert (wf_ren R). {subst; apply cut_renaming_wf; auto. }
    + admit.
    + rewrite <- (lctxt_rename_id (flat_ctxt 1 n)).
      rewrite <- lctxt_rename_app; auto using wf_ren_id.

    eapply rename_rvar_pres_wf_EC_hs.
    admit. (* Need the cut renaming to preserve wf *)
  - assert (H5 := H4); assert (H6 := H4). 
    (* Get hole scope <> top scope *)
    apply inv_split_hole_scope_Edeflam in H4. rewrite H4.
    destruct x1. simpl.
    (* Get x wf and EP0 wf *)
    eapply split_hole_scope_pres in H5; 
    try solve [econstructor; eauto]; dest_conj_disj_exist.
    inversion H7; existT_eq; subst.
    (* Just need filler wf and fillee wf *)
    eapply EC_fill_wf_pres_term; eauto.
    constructor; auto; try reflexivity.
    econstructor; eauto.
    (* Need to know n_hol = n1 + 1 *)
    apply split_hole_scope_gives_hole_scope in H6.
    assert (n_hol = n1 + 1). {
      eapply hole_scope_at_top_wf_simpl; eauto.
    } subst.
    admit. (* Need the cut renaming to preserve wf *)
Qed.












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
    wf_term m n ((tuple_cut_hole_scope Et r1 r2 r1' r2') <=[ nul ]).
Proof.
  intros. destr_inv_fill_wf H.
  inversion H1; inversion WFP1; inversion WFP2; inversion WFO; 
    inversion WFO0; existT_eq; subst; rewrite_ctxt_equivs; 
    clear H1 WFP1 WFP2 WFO WFO0.
  repeat rewrite sum_zero_r in *. 
  unfold one in H2.
  assert (forall c1 c2, ((n_hol [r ↦ 1] ⨥ c1) ⨥ (n_hol [r ↦ 1] ⨥ c2))
                ≡[n_hol]  n_hol [r ↦ 2] ⨥ c1 ⨥ c2) as R.
    { unfold delta, sum, ctxt_eq; intros. lia_goal. }
  rewrite R in H2; clear R.
  assert (((n_hol [r1 ↦ 1] ⨥ n_hol [r2 ↦ 1]) 
         ⨥ (n_hol [r1' ↦ 1] ⨥ n_hol [r2' ↦ 1])) r = 0) as Z.
    { eapply max_rvar_hole_EC_wf in H2. 
      2: exact HR0.
      unfold delta, sum in *.
      destruct (lt_dec r n_hol); destruct (Nat.eq_dec r r); lia. }
Admitted.
  (* eapply rem_hole_rvar_EC_wf in H2; try exact Z; auto.
  - eapply fill_wf_pres_term; eauto. constructor; reflexivity.
  - unfold delta, sum, ctxt_eq; intros; lia.



Qed. *)


Lemma wf_prim_step :
  forall m n t t',
    wf_term m n t ->
    prim_step t t' ->
    wf_term m n t'.
Proof.
  intros. inversion H0; subst; clear H0.
   auto using wf_prim_step_nul.
Admitted.












































































































