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

Local Open Scope program_scope.
Local Open Scope bool_scope.

(* Cuts *)

(*
Lemma wf_cut_oper :
  forall m n x c o (G : lctxt m) (Dx : lctxt x) (Dn : lctxt n),
    wf_oper m (x + 1 + n) G (Dx ⊗ 1[0 ↦ c] ⊗ Dn) o ->
    wf_oper m (x + n) G (Dx ⊗ Dn) (cut_rvar_oper n x o).
Proof.
  intros.
  inversion H; existT_eq; subst.
  - simpl.
*)

(* Fixpoint cuts n (l:list (nat * nat)) : ren (length l + n) n := *)
(*   match l with *)
(*   | [] => ren_id n *)
(*   | (x,y)::l => *)
(*       let f := cuts n l in *)
(*       let x' := f x in *)
(*       let y' := f y in *)
(*           match Nat.compare x' y' with *)
(*           | Lt => ren_compose f (retract n x' y') *)
(*           | Eq => ren_compose f (cut n x') *)
(*           | Gt => ren_compose f (retract n y' x') *)
(*       end *)
(*   end. *)



(* Rvar Context Well-Formedness and Rvar-Closed Context Equivalence ---------------------- *)

(* An rvar context is well-formed if it only binds variables to 0, 1, or 2 uses*)
(* Definition rvar_ctxt_wf n (D : lctxt n) :=
  forall x, x < n -> D x <= 2.


(* Well-formed processes and operands have well-formd rvar contexts *)
Lemma tpo_rc_wf :
  (forall m n t,
    wf_term m n t ->
    True)
  /\
  (forall m n G D P,
    wf_proc m n G D P ->
    rvar_ctxt_wf n D)
  /\
  (forall m n G D o,
    wf_oper m n G D o ->
    rvar_ctxt_wf n D).
  apply wf_tpo_ind; intros. 
  (* All cases are trivial *)
  - auto.
  -
Qed.  *)


(* Two rvar contexts are "rvar-closed equivalent" if their bindings are equal mod 2 *)
(* Definition rvar_closed_eq n (D1 D2 : lctxt n) :=
  forall x, x < n -> D1 x = D2 x \/ (D1 x = 0 /\ D2 x = 2) \/ (D1 x = 2 /\ D2 x = 0).

Infix "≡[ n ]rc" := (rvar_closed_eq n) (at level 70).

#[global] Instance refl_ctxt_eq : forall n, Reflexive (@rvar_closed_eq n).
Proof.
  intros. repeat red.
  intros. left; auto.
Qed.

#[global] Instance sym_ctxt_eq : forall n, Symmetric (@rvar_closed_eq n).
Proof.
  intros. repeat red.
  intros. destruct (H x0); auto. right; destruct H1; destruct H1; auto.
Qed.

#[global] Instance trans_ctxt_eq : forall n, Transitive (@rvar_closed_eq n).
Proof.
  intros. repeat red.
  intros. destruct (H x0); destruct (H0 x0); try rewrite H2 in *; try rewrite H3 in *; auto.
  destruct H2; destruct H2; destruct H3; destruct H3; rewrite H2, H5; auto.
Qed.

#[global] Instance Proper_ctxt_eq {n} : 
  Proper ((@rvar_closed_eq n) ==> (@rvar_closed_eq n) ==> iff) (@rvar_closed_eq n).
Proof.
  repeat red.
  intros.
  split; intros.
  - eapply transitivity. symmetry. apply H. eapply transitivity. apply H1. apply H0.
  - eapply transitivity. apply H. eapply transitivity. apply H1. symmetry. apply H0.
Qed. *)

(* 
(* Rvar-closed equivalence on rvar contexts preserves well-formedness *)
Lemma rceq_wf :
  (forall m n t,
    wf_term m n t ->
    True)
  /\
  (forall m n G D P,
    wf_proc m n G D P ->
      forall D',
        D ≡[n]rc D' ->
      wf_proc m n G D' P)
  /\
  (forall m n G D o,
    wf_oper m n G D o ->
      forall D',
        D ≡[n]rc D' ->
      wf_oper m n G D' o).
Proof.
  apply wf_tpo_ind; intros. 
  (* All cases are trivial *)
  - auto.
  - econstructor. auto.
Qed.   *)




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



(* BELOW: SPECIFIC TO LINEAR OPAL *)

(* Takes a process that typechecks in G' ⊗ G
    and moves it to G' ⊗ zero m'' ⊗ G *)
Definition weaken_f m m' m'' :=
  rename_fvar_proc (weaken_tail_ren m m' m'').

(* "removes" variable x from the scope, 
    where n is the number of variables > x *)
Definition strengthen n (x:var) : ren (x + 1 + n) (x + n) :=
  fun y => if lt_dec y x then y else (y - 1).
Definition strengthen_rvar_oper n x o : oper := rename_rvar_oper (strengthen n x) o.
Definition strengthen_rvar_proc n x P : proc := rename_rvar_proc (strengthen n x) P.

(* "retracts" a variable y into x:
   Makes sense when x < y
    - "merges" x and y to be just "x"
    - first rename y to x
        y + 1 + n  ~> y + 1 + n
    - then cut out y
        y + 1 + n ~>  y + n
   Here, n is the number of variables in the original scope that are > y. *)
Definition retract n x y : ren (y + 1 + n) (y + n) :=
  @ren_compose (y + 1 + n) (y + 1 + n) _ (rename_var y x) (strengthen n y).
Definition retract_rvar_proc n x y P := rename_rvar_proc (retract n x y) P.






(* Operational Semantics --------------------------------------------------- *)



(* Helper functions for tuple cuts *)
                  
(* Gives a "collapsed" renaming that only renames r1 to r2 *)
Definition rename_if_neq n (r1 r2 : nat) : ren n n :=
  if Nat.eq_dec r1 r2 then
    ren_id n
  else
    rename_var r1 r2.

(* Gives a "collapsed" renaming that only renames r1 to r1' and r2 to r2'. 
    Used for stepping the cut (r <- (r1, r2) | r <- (r1', r2')) *)
Definition cut_renaming n (r1 r2 r1' r2':nat) : ren n n :=
  (* First, check if two variables in either pair are equal *)
  if Nat.eq_dec r1 r2 then
    rename_if_neq n r1' r2'
  else if Nat.eq_dec r1' r2' then
    rename_var r1 r2
  (* Second, check if a variable is equal to its
      non-corresponding variable in the other pair *)
  else if Nat.eq_dec r1 r2' then
    rename_if_neq n r1' r2
  else if Nat.eq_dec r1' r2 then
    rename_var r1 r2'
  (* Third, check if a variable is equal to its
      corresponding variable in the other pair *)
  else if Nat.eq_dec r1 r1' then
    rename_if_neq n r2 r2'
  else if Nat.eq_dec r2 r2' then
    rename_var r1 r1'
  (* Now we know there are no equalities between the variables *)
  else
    @ren_compose n n nat (rename_var r1 r1') (rename_var r2 r2').

(* Gives the number of rvars in scope at the hole *)
Definition scoped_rvars_at_hole : EC_term -> nat := 
  case_hole_scope_at_top 
    (get_rvars_Et) 
    ((add 1) ∘ get_rvars_Et).

Definition tuple_cut_hole_scope Et r1 r2 r1' r2' := 
  let ren := cut_renaming (scoped_rvars_at_hole Et) r1 r2 r1' r2' in
  mutate_hole_scope (rename_rvar_EC_term ren) Et.



(* Helper functions for function application *)

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
  bound_fvars_to_hole (bubble_hole_scope_up Et).

  
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
  @rename_rvar_proc n_total n_total (rename_var (n + n_app) r_arg) P1.

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





(* Preservation of functions for prim_step *)

Ltac drill_wf H := apply drill_term_wf_pres in H;
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
      * intros. unfold ctxt_eq in HD3; specialize HD3 with x. rewrite lctxt_sum in HD3. 
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
  (* Epar *)
  - destruct (H r D_hol'); auto.
    + left. econstructor; eauto.
    + right. destruct H3 as (H3 & D' & H4 & H5).
      split; auto. exists (D' ⨥ D2); repeat split.
      * rewrite <- sum_assoc, (sum_commutative D2), sum_assoc. 
        rewrite HD; rewrite H4. reflexivity.
      * econstructor; eauto; reflexivity.
  (* Elamdef *)
  - left. constructor; auto. eapply H; eauto.
Qed.


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
  unfold tuple_cut_hole_scope, mutate_hole_scope; simpl. 
  destruct (split_hole_scope (Ebag m0 n0 EP)) as (Et_outer & EP_hs) eqn:shsEQ.
  induction EP_hs.
  - unfold scoped_rvars_at_hole, case_hole_scope_at_top.
      apply split_hole_scope_Ehol in shsEQ.
      TODO.
Qed.












(* Preservation of prim_step and step *)

Lemma wf_prim_step_nul :
  forall m n Et P,
    wf_term m n (Et <=[ par P nul ]) ->
    wf_term m n (Et <=[ P ]).
Proof.
  intros. drill_wf H. eapply fill_EC_wf_pres_term; eauto.
  inversion H1; inversion WFP2; existT_eq; subst; rewrite_ctxt_equivs.
  repeat rewrite sum_zero_r; auto.
Qed.

Lemma wf_prim_step_emp :
  forall m n Et r,
    wf_term m n (Et <=[ par (def r emp) (def r emp) ]) ->
    wf_term m n (Et <=[ nul ]).
Proof.
  intros. drill_wf H.
  inversion H1; inversion WFP1; inversion WFP2; inversion WFO; 
    inversion WFO0; existT_eq; subst; rewrite_ctxt_equivs; 
    clear H1 WFP1 WFP2 WFO WFO0.
  repeat rewrite sum_zero_r in H2.
  unfold one in H2; rewrite delta_sum in H2; simpl in H2.
  assert ((zero n_hol) r = 0) as Z by auto.
  eapply rem_hole_rvar_EC_wf in H2; try exact Z; auto.
  - eapply fill_EC_wf_pres_term; eauto. constructor; reflexivity.
  - rewrite sum_zero_l; reflexivity.
Qed.


Lemma wf_prim_step_tup :
  forall m n Et r r1 r2 r1' r2',
    wf_term m n (Et <=[ par (def r (tup r1 r2)) (def r (tup r1' r2')) ]) ->
    wf_term m n ((tuple_cut_hole_scope Et r1 r2 r1' r2') <=[ nul ]).
Proof.
  intros. drill_wf H.
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
  - eapply fill_EC_wf_pres_term; eauto. constructor; reflexivity.
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


Inductive  step : nat -> nat -> term -> term -> Prop :=
| step_equiv : forall m n t1 t1' t2' t2,
    t1 ≈t t1' ->
    prim_step m n t1' t2' ->
    t2' ≈t t2 ->
    step m n t1 t2.












Import ListNotations.
Example ex_P0 : proc :=
  (par (def 3 (tup 2 2)))
     (def 1 (tup 4 4)).

Example ex_P : proc :=
  par (def 0 (tup 1 2))
    (par (def 0 (tup 3 4))
       ex_P0).

Eval compute in retract_rvar_proc 1 1 3 ex_P0.

Lemma wf_prim_step_nul :
  forall m m' n n' P,
    wf_term m n (bag m' n' (par P nul)) ->
    wf_term m n (bag m' n' P).
Proof.
  intros.
  inversion H; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  
  rewrite HG0 in HG; clear HG0.
  rewrite HD0 in HD; clear HD0.
  rewrite sum_zero_r in HG.
  rewrite sum_zero_r in HD.
  rewrite <- HG in WFP1; clear HG.
  rewrite <- HD in WFP1; clear HD.

  eapply wf_bag; auto.
Qed.

Lemma wf_prim_step_emp :
  forall m m' n n' r P (G : lctxt m),
    wf_term m n G (zero n) (bag m' n' (par P (par (def r emp) (def r emp)))) ->
    wf_term m n G (zero n) (bag m' n' P).
Proof.
  intros.
  inversion H; subst. existT_eq; subst; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP3; existT_eq; subst; clear WFP3.
  inversion WFO; existT_eq; subst; clear WFO.
  inversion WFO0; existT_eq; subst; clear WFO0.
  
  rewrite HG1 in HG0; clear HG1.
  rewrite HG2 in HG0; clear HG2.
  rewrite sum_zero_r in HG0.
  rewrite HG0 in HG; clear HG0.
  rewrite sum_zero_r in HG.
  rewrite <- HG in WFP1; clear HG.
  rewrite HD4 in HD2; clear HD4.
  rewrite sum_zero_r in HD2.
  rewrite HD2 in HD0; clear HD2.
  rewrite HD3 in HD1; clear HD3.
  rewrite sum_zero_r in HD1.
  rewrite HD1 in HD0; clear HD1.
  unfold one in HD0.
  rewrite delta_sum in HD0. simpl in HD0.
  rewrite HD0 in HD; clear HD0.
  apply sum_app_inv_ctxt in HD.
  destruct HD as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
  assert (DB1 ≡[n] zero n). { apply sum_zero_inv_l_eq in EQ4. assumption. } 
  assert (DB2 ≡[n] zero n). { apply sum_zero_inv_r_eq in EQ4. assumption. }
  clear EQ4.
  rewrite H in EQ1; clear H.
  rewrite H0 in EQ2; clear H0.
  rewrite EQ1 in WFP1.
  eapply wf_bag.
  3 : { apply WFP1.  }
  auto.
  apply app_delta_zero_inv_ctxt in EQ2; auto.
  rewrite <- EQ2 in EQ3; clear EQ2.
  intros x HX.
  specialize (UD' x HX).
  destruct (Nat.eq_dec x r).
  - subst.
    specialize (EQ3 _ HX).
    unfold sum in EQ3.
    rewrite delta_id in EQ3; auto.
    lia.
  - specialize (EQ3 _ HX).
    unfold sum in EQ3.
    rewrite delta_neq in EQ3; auto.
    lia.
Qed.    
                     
Lemma ctxt_eq_imp :
  forall n X (c : ctxt n X) (d : ctxt n X) (P : X -> Prop),
    c ≡[n] d ->
    forall x, x < n -> P (c x) -> P (d x).
Proof.
  unfold ctxt_eq.
  intros.
  rewrite <- H; auto.
Qed.  

Lemma ctxt_app_c_zero_inv : forall n' n (c : lctxt n') r r1 r1' r2 r2',
    r < n' + n ->
    r1 < n' + n ->
    r1' < n' + n ->
    r2 < n' + n ->
    r2' < n' + n ->
 c ⊗ zero n
   ≡[ n' + n] (n' + n) [r ↦ 2] ⨥ (one (n' + n) r1 ⨥ (one (n' + n) r1' ⨥ (one (n' + n) r2 ⨥ one (n' + n) r2')))
 ->
   (r < n') /\ (r1 < n') /\ (r1' < n') /\ (r2 < n') /\ (r2' < n').
Proof.
  unfold ctxt_app, zero, one, delta, sum, ctxt_eq.
  intros.
  repeat match goal with
         | [ H: context[lt_dec ?R1 ?R2] |- _ ] => destruct (lt_dec R1 R2); try lia
         end.
  apply H4 in H.
  apply H4 in H0.
  apply H4 in H1.
  apply H4 in H2.
  apply H4 in H3.
  clear H4.
  repeat split;
  repeat match goal with
         | [ H: context[Nat.eq_dec ?R1 ?R1] |- _ ] => destruct (Nat.eq_dec R1 R1); subst; try lia
    end.
  - destruct (lt_dec r n'); try lia.
  - destruct (lt_dec r1 n'); try lia.
  - destruct (lt_dec r1' n'); try lia.
  - destruct (lt_dec r2 n'); try lia.
  - destruct (lt_dec r2' n'); try lia.    
Qed.  

Lemma zero_delta_0 :
  forall n x, zero n ⨥ n[x ↦ 0] ≡[n] zero n.
  intros.
  unfold zero, delta, sum, ctxt_eq.
  intros.
  destruct (lt_dec x n); try lia.
  destruct (Nat.eq_dec x x0); try lia.
Qed.  


Lemma wf_oper_rename_rvar :
  forall m n G D o,
    wf_oper m n G D o ->
    forall D1 D2  r r' cr cr'
      (HR: r < n)
      (HR' : r' < n)
      (HDR : D1 r = 0)
      (HDR' : D1 r' = 0)
      (HNEQ : r <> r')
      (HD1 : D ≡[n] D1 ⨥ (n[r ↦ cr]) ⨥ (n[r' ↦ cr']))
      (HD2 : D2 ≡[n] D1 ⨥ (n[r' ↦ cr + cr'])),
      wf_oper m n G D2 (@rename_rvar_oper n n(rename_var r r') o).
Proof.
  intros.
  inversion H; existT_eq; subst; simpl.
  - rewrite HD in HD1.
    rewrite <- sum_assoc in HD1.
    symmetry in HD1.
    specialize (sum_zero_inv_l_eq _ _ _ HD1).
    intros.
    specialize (sum_zero_inv_r_eq _ _ _ HD1).
    intros.
    assert (cr = 0 /\ cr' = 0). {
      pose proof (H1 _ HR) as HA.
      pose proof (H1 _ HR') as HB.
      unfold sum, delta, zero in HA, HB.
      lia_destruct.
    }
    destruct H2; subst.
    rewrite H0 in HD2.
    rewrite zero_delta_0 in HD2.
    apply wf_emp; auto.
  - unfold rename_var.
    rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    destruct (Nat.eq_dec r1 r); destruct (Nat.eq_dec r2 r); subst.
    + assert (D2 ≡[n] (one n r') ⨥ (one n r')). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2. clear HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r') ⨥ (one n r2)). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r1) ⨥ (one n r')). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r1) ⨥ (one n r2)). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
  - rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    assert (D2 ≡[n] zero n). { 
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        unfold ctxt_eq, one, delta, sum, zero in *.
        lia_destruct.
    }
    apply wf_bng; auto.
  - rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    assert (D2 ≡[n] zero n). { 
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        unfold ctxt_eq, one, delta, sum, zero in *.
        lia_destruct.
    }
    apply wf_lam; auto.
    erewrite rename_rvar_id_term.
    apply WFT.
    eapply wf_ws_term; eauto.
Qed.


Lemma lctxt_subtract : forall n c r,
    r < n ->
    c r > 0 ->
    exists d, c ≡[n] (one n r) ⨥ d.
Proof.
  intros.
  exists (fun x => if Nat.eq_dec r x then (c r - 1) else c x).
  unfold ctxt_eq.
  intros.
  unfold one, delta, sum.
  destruct (lt_dec r n); try lia.
  destruct (Nat.eq_dec r x); subst; try lia.
Qed.

Lemma sum_inv_l : forall n (c d1 d2 : lctxt n),
    c ⨥ d1 ≡[n] c ⨥ d2 ->
    d1 ≡[n] d2.
Proof.
  unfold ctxt_eq, sum.
  intros.
  specialize (H _ H0).
  lia.
Qed.  

Lemma lctxt_sum_inv_two :
  forall n
   (D1 : lctxt n)
   (r r' cr cr' : nat)
   (HR : r < n)
   (HR' : r' < n)
   (HDR : D1 r = 0)
   (HDR' : D1 r' = 0)
   (HNEQ : r <> r')
   (D0 D3 : lctxt n)
   (HD1 : D0 ⨥ D3 ≡[ n] (D1 ⨥ n [r ↦ cr]) ⨥ n [r' ↦ cr']),
    exists D0' D3',
    D1 ≡[n] D0' ⨥ D3' /\
      (D0 ≡[n] D0' ⨥ n[r ↦ D0 r] ⨥ n[r' ↦ D0 r']) /\
      (D3 ≡[n] D3' ⨥ n[r ↦ D3 r] ⨥ n[r' ↦ D3 r']) /\
      (D0 r + D3 r = cr) /\ (D0 r' + D3 r' = cr') /\
      (D0' r = 0) /\ (D0' r' = 0) /\ (D3' r = 0) /\ (D3' r' = 0).
Proof.
  intros.
  exists (fun x => if Nat.eq_dec x r then 0 else if Nat.eq_dec x r' then 0 else  D1 x - D3 x).
  exists (fun x => if Nat.eq_dec x r then 0 else if Nat.eq_dec x r' then 0 else  D1 x - D0 x).
  split.
  - unfold ctxt_eq.
    intros.
    pose proof (HD1 _ HR).
    pose proof (HD1 _ HR').
    pose proof (HD1 _ H).
    clear HD1.
    unfold sum, delta in *.
    destruct (Nat.eq_dec x r); try lia_destruct; try lia.
    destruct (Nat.eq_dec x r'); lia_destruct; try lia.
  - split.
    +  unfold ctxt_eq.
       intros.
       pose proof (HD1 _ HR).
       pose proof (HD1 _ HR').
       pose proof (HD1 _ H).
       clear HD1.
       unfold sum, delta in *.
       destruct (Nat.eq_dec x r); try lia_destruct; try lia.
       destruct (Nat.eq_dec x r'); try lia.
    + split.
      * unfold ctxt_eq.
        intros.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H).
        clear HD1.
        unfold sum, delta in *.
        destruct (Nat.eq_dec x r); try lia_destruct; try lia.
        destruct (Nat.eq_dec x r'); try lia.
      * pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        clear HD1.
        unfold sum, delta in *.
        destruct (Nat.eq_dec r r); try lia_destruct; try lia.
Qed.

Lemma wf_proc_rename_rvar :
  forall m n G D P,
    wf_proc m n G D P ->
    forall D1 D2  r r' cr cr'
      (HR: r < n)
      (HR' : r' < n)
      (HDR : D1 r = 0)
      (HDR' : D1 r' = 0)
      (HNEQ : r <> r')
      (HD1 : D ≡[n] D1 ⨥ (n[r ↦ cr]) ⨥ (n[r' ↦ cr']))
      (HD2 : D2 ≡[n] D1 ⨥ (n[r' ↦ cr + cr'])),
      wf_proc m n G D2 (@rename_rvar_proc n n(rename_var r r') P).
Proof.
  intros m n G D P. revert m n G D.
  induction P; intros; inversion H; existT_eq; subst; simpl.
  - unfold rename_var at 1.
    destruct (Nat.eq_dec r r0); subst.
    + rewrite HD in HD1.
      assert (D' ≡[n] (D1 ⨥ n[r0 ↦ (cr - 1)] ⨥ n[r' ↦ cr'])). {
        unfold ctxt_eq, sum, delta. intros.
        pose proof (HD1 _ H0).
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        unfold ctxt_eq, sum, one, delta in H1, H2, H3.
        lia_destruct.
      }
      assert (cr > 0). {
        specialize (HD1 _ HR).
        unfold ctxt_eq, sum, one, delta in HD1.
        lia_destruct.
      }
      assert (D2 ≡[n] (one n r') ⨥ (D1 ⨥ n[r' ↦ (cr - 1) + cr'])). {
        unfold ctxt_eq, sum, one, delta. intros.
        pose proof (HD2 _ H2).
        pose proof (HD2 _ HR).
        pose proof (HD2 _ HR').
        unfold ctxt_eq, sum, one, delta in H3, H4, H5.
        lia_destruct.
      } 
      eapply wf_def; eauto.
      eapply wf_oper_rename_rvar; eauto.
      reflexivity.
    + rewrite HD in HD1.
      destruct (Nat.eq_dec r r'); subst; auto.
      * assert (D' ≡[n] (D1 ⨥ n[r0 ↦ cr] ⨥ n[r' ↦ (cr' - 1)])). {
          unfold ctxt_eq, sum, delta. intros.
          pose proof (HD1 _ H0).
          pose proof (HD1 _ HR).
          pose proof (HD1 _ HR').
          unfold ctxt_eq, sum, one, delta in H1, H2, H3.
          lia_destruct.
        }
        assert (cr' > 0). {
          specialize (HD1 _ HR').
          unfold ctxt_eq, sum, one, delta in HD1.
          lia_destruct.
        }
        assert (D2 ≡[n] (one n r') ⨥ (D1 ⨥ n[r' ↦ cr + (cr' - 1)])). {
          unfold ctxt_eq, sum, one, delta. intros.
          pose proof (HD2 _ H2).
          pose proof (HD2 _ HR).
          pose proof (HD2 _ HR').
          unfold ctxt_eq, sum, one, delta in H3, H4, H5.
          lia_destruct.
        } 
        eapply wf_def; eauto.
        eapply wf_oper_rename_rvar; eauto.
        reflexivity.
      * assert (D1 r > 0). {
          pose proof (HD1 _ HR0).
          unfold ctxt_eq, sum, one, delta in H0.
          lia_destruct.
        }
        pose proof (lctxt_subtract _ _ _ HR0 H0).
        destruct H1 as (D1' & HD1').
        rewrite HD1' in HD2.
        repeat rewrite <- sum_assoc in HD2.
        rewrite HD1' in HD1.
        repeat rewrite <- sum_assoc in HD1.
        apply sum_inv_l in HD1.
        rewrite  sum_assoc in HD1.
        eapply wf_def; eauto.
        eapply wf_oper_rename_rvar with (D:=D')(D1:=D1'); eauto; try reflexivity.
        -- specialize (HD1' _ HR).
           unfold one, delta, sum in HD1'.
           lia_destruct.
        -- specialize (HD1' _ HR').
           unfold one, delta, sum in HD1'.
           lia_destruct.
  - unfold rename_var.
    rewrite HD in HD1; clear HD.
    destruct (Nat.eq_dec r r0); subst.
    + assert (D2 ≡[n] (one n r')). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
    + destruct (Nat.eq_dec r r'); subst.
      * assert (D2 ≡[n] (one n r')). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
      * assert (D2 ≡[n] (one n r)). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
  - rewrite HD in HD1.
    apply lctxt_sum_inv_two in HD1; auto.
    destruct HD1 as (D0' & D3' & EQ1 & EQ2 & EQ3 & HS1 & HS2 & HS3 & HS4 & HS5 & HS6).
    rewrite EQ2 in WFP1.
    rewrite EQ3 in WFP2.
    rewrite EQ1 in HD2.

    assert (D2 ≡[n] (D0' ⨥ n[r' ↦ D0 r + D0 r']) ⨥ (D3' ⨥ n[r' ↦ D3 r + D3 r'])). {
      repeat rewrite <- sum_assoc.
      rewrite (@sum_assoc _ n [r' ↦ D0 r + D0 r']).
      rewrite (@sum_commutative _ _ D3').
      repeat rewrite <- sum_assoc.
      rewrite delta_sum.
      assert ((D0 r + D0 r' + (D3 r + D3 r')) = cr + cr') by lia.
      rewrite H0.
      rewrite HD2.
      repeat rewrite <- sum_assoc.
      reflexivity.
    }
    rewrite H0.
    eapply wf_par with (G1 := G1)(G2 :=G2); auto.
    3 : { reflexivity. }
    + eapply IHP1; auto.
      apply WFP1.
      4 : { reflexivity. }
      auto.
      auto.
      reflexivity.
    + eapply IHP2; auto.
      apply WFP2.
      4 : { reflexivity. }
      auto.
      auto.
      reflexivity.
Qed.

Lemma ctxt_app_assoc_zero :
  forall (j k l : nat) 
         (J : lctxt j)
         (K : lctxt k),
  (@ctxt_app _ (j + k) l (@ctxt_app _ j k J K) (zero l)) =
  (@ctxt_app _ j (k + l)  J (@ctxt_app _ k l K (zero l))).
Proof. 
  intros. 
  unfold ctxt_app. 
  apply functional_extensionality. 
  intros x.
  destruct (lt_dec x (j + k)); try lia.
  destruct (lt_dec x j); try lia.
  destruct (lt_dec (x - j) k); try lia.
  destruct (lt_dec x j); try lia.
  destruct (lt_dec (x - j) k); try lia.
  unfold zero; lia.
Qed.

Lemma ctxt_app_zero_zero :
  forall (n m : nat),
  (@ctxt_app _ n m (zero n) (zero m)) ≡[n + m]
  (zero (n + m)).
Proof.
  intros.
  unfold zero, ctxt_app.
  intros x Hx. 
  destruct (lt_dec x n); try lia.
Qed.

Lemma wf_app_zero :
  (forall (m n : nat)
      (G : lctxt m)
      (D : lctxt n)
      (t : term), 
      wf_term m n G D t ->
      forall (m' n' : nat),
        wf_term (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) t)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (P : proc), 
        wf_proc m n G D P ->
        forall (m' n' : nat),
          wf_proc (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) P)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (o : oper), 
        wf_oper m n G D o ->
        forall (m' n' : nat),
          wf_oper (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) o).
Proof.
apply wf_tpo_ind; intros.
- eapply wf_bag with (G':= G') (D' := D').
  assumption. assumption.
  assert ((@ctxt_app _ m' (m + m'0) G' (G ⊗ (zero m'0))) = 
          (@ctxt_app _ (m' + m) m'0 (G' ⊗ G) (zero m'0))).
  { symmetry; apply ctxt_app_assoc_zero. }
  rewrite H0; clear H0.
  assert ((@ctxt_app _ n' (n + n'0) D' (D ⊗ (zero n'0))) = 
          (@ctxt_app _ (n' + n) n'0 (D' ⊗ D) (zero n'0))).
  { symmetry; apply ctxt_app_assoc_zero. }
  rewrite H0; clear H0.
  specialize (H m'0 n'0).
  replace (m' + (m + m'0)) with (m' + m + m'0) by lia.
  replace (n' + (n + n'0)) with (n' + n + n'0) by lia.
  assumption.
- rewrite HD. 
  assert ((@ctxt_app _ n n' (one n r ⨥ D') (zero n')) = 
          ((@ctxt_app _ n n' (one n r) (zero n')) ⨥ (@ctxt_app _ n n' D' (zero n')))).
  { assert ((zero n') = (zero n') ⨥ (zero n')) by (symmetry; apply sum_zero_l). 
    rewrite H0 at 1.
    symmetry; apply lctxt_sum_app_dist. }
  rewrite H0; clear H0. 
  eapply wf_def; eauto; try lia.
  unfold ctxt_app, sum, one, zero, delta.
  intros x Hx. destruction.
- eapply wf_app; try lia. 
  rewrite HG. unfold zero, ctxt_app.
  intros x Hx. destruct (lt_dec x m); try lia.
  rewrite HD. unfold one, zero, ctxt_app, delta.
  intros x Hx. destruction.
- rewrite HG, HD. 
  assert ((@ctxt_app _ m m' (G1 ⨥ G2) (zero m')) = 
          (@ctxt_app _ m m' G1 (zero m')) ⨥ (@ctxt_app _ m m' G2 (zero m'))).
  symmetry; apply lctxt_sum_app_dist. rewrite H1; clear H1.
  assert ((@ctxt_app _ n n' (D1 ⨥ D2) (zero n')) = 
          (@ctxt_app _ n n' D1 (zero n')) ⨥ (@ctxt_app _ n n' D2 (zero n'))).
  symmetry; apply lctxt_sum_app_dist. rewrite H1; clear H1.
  eapply wf_par with (G1 := (@ctxt_app _ m m' G1 (zero m')))
                     (G2 := (@ctxt_app _ m m' G2 (zero m'))) 
                     (D1 := (@ctxt_app _ n n' D1 (zero n')))
                     (D2 := (@ctxt_app _ n n' D2 (zero n'))).
  specialize (H m' n'); try assumption.
  specialize (H0 m' n'); try assumption.
  apply refl_ctxt_eq. apply refl_ctxt_eq.
- rewrite HG, HD. apply wf_emp. 
  apply ctxt_app_zero_zero.
  unfold zero, ctxt_app. intros x Hx. destruct (lt_dec x n); try lia.
- rewrite HG, HD. apply wf_tup; try lia.
  apply ctxt_app_zero_zero.
  assert ((@ctxt_app _ n n' (one n r1 ⨥ one n r2) (zero n')) = 
          ((@ctxt_app _ n n' (one n r1) (zero n')) ⨥ (@ctxt_app _ n n' (one n r2) (zero n'))))
  by (symmetry; apply lctxt_sum_app_dist). rewrite H; clear H.
  unfold zero, ctxt_app, one, sum, delta. 
  intros x Hx. destruction.
- rewrite HG, HD. apply wf_bng; try lia.
  unfold one, ctxt_app, zero, delta.
  intros x Hx. destruction.  
  unfold zero, ctxt_app. 
  intros x Hx. destruction.
- rewrite HG, HD. apply wf_lam. 
  apply ctxt_app_zero_zero.
  apply ctxt_app_zero_zero.
  specialize (H m' 0).
  assert ((@ctxt_app _ 1 0 (1 [0 ↦ 1]) (zero 0) = 1 [0 ↦ 1])).
  unfold delta, ctxt_app, zero. apply functional_extensionality.
  intros x. destruction.
  rewrite H0 in H; clear H0. simpl in H.
  assert ((zero m ⊗ zero m') ≡[m + m'] (zero (m + m'))) by (apply ctxt_app_zero_zero).
  rewrite H0 in H; clear H0; try assumption.
Qed.

Lemma wf_proc_app_zero :
  (forall (m n:nat)
        (G : lctxt m)
        (D : lctxt n)
        (P : proc), 
          wf_proc m n G D P ->
          forall (m' n' : nat),
            wf_proc (m + m') (n + n') 
            (@ctxt_app _ m m' G (zero m'))
            (@ctxt_app _ n n' D (zero n')) P).
Proof.
  apply wf_app_zero.
Qed.

(* This version of renaming takes a variable in context

  G0 ⊗ (G1 ⊗ G2) ⊗ G3
  m0 + (m1 + m2) + m3

  and renames it into the context

  G0 ⊗ (G2 ⊗ G1) ⊗ G3
  m0 + (m2 + m1) + m3

*)
Definition ren_commute_str m0 m1 m2 m3:  ren (m0 + (m1 + m2) + m3) (m0 + (m2 + m1) + m3) :=
  fun x =>
    if (lt_dec x m0) then x 
    else if (lt_dec x (m0 + m1)) then (x + m2)
         else if (lt_dec x (m0 + m1 + m2)) then (x - m1)
                  else x.

Lemma ren_shift_ren_commute_str : forall m' m0 m1 m2 m3,
    ren_shift m' (ren_commute_str m0 m1 m2 m3) = ren_commute_str (m' + m0) m1 m2 m3.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  unfold ren_shift, ren_commute_str, ctxt_app, ren_id.
  lia_goal.
Qed.  


Lemma ctxt_zero_app_inv_l :
  forall n m (G1 : lctxt n) (G2 : lctxt m),
    zero (n+m) ≡[n + m] G1 ⊗ G2 ->
    zero n ≡[n] G1.
Proof.
  intros.
  unfold zero, ctxt_eq, ctxt_app in *.
  intros x HX.
  assert (x < n + m) by lia.
  specialize (H x H0).
  lia_destruct.
Qed.  

Lemma ctxt_zero_app_inv_r :
  forall n m (G1 : lctxt n) (G2 : lctxt m),
    zero (n+m) ≡[n + m] G1 ⊗ G2 ->
    zero m ≡[m] G2.
Proof.
  intros.
  unfold zero, ctxt_eq, ctxt_app in *.
  intros x HX.
  assert (x + n < n + m) by lia.
  specialize (H (x+n) H0).
  lia_destruct.
  assert (x + n - n = x) by lia.
  rewrite H1 in H.
  assumption.
Qed.

Lemma ctxt_one_eq_app_zero :
  forall n m x (D : lctxt m)
    (Hx : x < n)
    (H : one (n + m) x ≡[n + m] (one n x) ⊗ D),
    D ≡[m] zero m.
Proof. 
  intros.
  assert (one (n + m) x ≡[n + m] (one n x) ⊗ (zero m)).
  { unfold ctxt_eq, ctxt_app, one, zero, delta in *.
    intros y Hy.
    specialize (H y Hy).
    destruction; try lia. }
  rewrite H in H0.
  apply ctxt_app_inv_r_eq in H0.
  assumption.
Qed.

Lemma ctxt_one_eq_app_zero_inv :
  forall n m x (D : lctxt m)
    (Hx : ~ x < n)
    (Hx' : x < n + m)
    (H : one (n + m) x ≡[n + m] (zero n) ⊗ D ),
    D ≡[m] (one m (x - n)).
Proof. 
  intros. 
  unfold ctxt_eq, ctxt_app, one, zero, delta in *.
  intros y Hy.
  destruct (lt_dec x (n + m)); try lia.
  apply H in Hx'.
  lia_destruct.
  lia_goal.
  - rewrite e0 in Hx'. lia.
  - assert ((y + n) < n + m) by lia.
    apply H in H0.
    lia_destruct.
    replace (y + n - n) with y in H0 by lia.
    lia.
Qed.

Lemma ctxt_one_eq_app_zero_inv_l :
  forall n m x (D : lctxt n)
    (Hx : x < n)
    (H : one (n + m) x ≡[n + m] D ⊗ (zero m)),
    D ≡[n] (one n x).
Proof. 
  intros. 
  unfold ctxt_eq, ctxt_app, one, zero, delta in *.
  intros y Hy.
  destruct (lt_dec x (n + m)); try lia.
  apply H in l.
  assert (y < n + m) by lia.
  apply H in H0.
  lia_destruct.
Qed.

Lemma ctxt_one_eq_zero_app :
  forall n m x (D : lctxt n)
    (Hx : ~ x < n)
    (Hx' : x < n + m)
    (H : D ≡[m] (one m (x - n))),
    one (n + m) x ≡[n + m] (zero n) ⊗ D.
Proof.
  intros.
  rewrite H.
  unfold ctxt_eq, ctxt_app, one, zero, delta.
  intros.
  lia_goal.
Qed.  
  

Lemma ren_commute_str_one :
  forall m0 m1 m2 m3 (G0 : lctxt m0) (G1 : lctxt m1) (G2 : lctxt m2) (G3 : lctxt m3) (f : nat)
    (HF : f < m0 + (m1 + m2) + m3)
    (HG : one (m0 + (m1 + m2) + m3) f ≡[m0 + (m1 + m2) + m3] G0 ⊗ (G1 ⊗ G2) ⊗ G3),
    one (m0 + (m2 + m1) + m3) (ren_commute_str m0 m1 m2 m3 f) ≡[m0 + (m2 + m1) + m3] G0 ⊗ (G2 ⊗ G1) ⊗ G3.
Proof.
  intros. 
  unfold ren_commute_str; destruction.

  - assert (G0 ≡[m0] (one m0 f)).
    { unfold zero, one, delta, ctxt_eq, ctxt_app in *.
      intros x HX.
      specialize (HG x).
      assert (x < m0 + (m1 + m2) + m3) by lia; apply HG in H.
      destruct (lt_dec f m0); try lia.
      destruct (Nat.eq_dec f x); try lia.
      try lia_destruct. lia_destruct. }
    rewrite H in *; clear H.
    assert ((G1 ⊗ G2) ⊗ G3 ≡[(m1 + m2) + m3] (zero ((m1 + m2) + m3))).
    { rewrite <- ctxt_app_assoc in HG.
      apply ctxt_one_eq_app_zero with (n := m0) (x := f); auto.
      rewrite Nat.add_assoc.
      try assumption. }
    symmetry in H.
    assert (H' : zero (m1 + m2) ≡[m1 + m2] G1 ⊗ G2). { eapply ctxt_zero_app_inv_l. apply H. }
    assert (H'' : zero m3 ≡[m3] G3). { eapply ctxt_zero_app_inv_r. apply H. } 
    apply ctxt_zero_app_inv_l in H'.
    apply ctxt_zero_app_inv_l in H.
    apply ctxt_zero_app_inv_r in H.
    assert ((@ctxt_app _ m2 m1 G2 G1) ≡[m2 + m1] (zero (m2 + m1))).
    { unfold zero, ctxt_app, ctxt_eq.
      intros x Hx. 
      destruct (lt_dec x m2); try lia.
      symmetry in H; rewrite H; unfold zero; lia.
      symmetry in H'; rewrite H'; unfold zero; lia. }
    rewrite <- H''.
    rewrite H0.
    rewrite <- ctxt_app_assoc.
    unfold one, delta, ctxt_eq, ctxt_app, zero.
    intros x Hx. destruction.

  - assert (G0 ≡[m0] (zero m0)). 
    { unfold zero, one, delta, ctxt_eq, ctxt_app in *.
      intros x Hx.
      specialize (HG x).
      assert (x < m0 + (m1 + m2) + m3) by lia; apply HG in H.
      destruct (lt_dec f m0); try lia.
      destruct (Nat.eq_dec f x); try lia.
      try lia_destruct. }
    rewrite H in *; clear H.
    rewrite <- ctxt_app_assoc in HG.
    rewrite <- Nat.add_assoc in HG.
    apply ctxt_one_eq_app_zero_inv with (n := m0) (x := f) in HG; try lia.
    rewrite <- ctxt_app_assoc in HG.
    assert (G1 ≡[m1] (one m1 (f - m0))).
    { unfold ctxt_eq, one, delta, ctxt_app in *. 
      intros x Hx.
      specialize (HG x).
      assert (x < (m1 + m2 + m3)) by lia; apply HG in H.
      destruction.
      lia_destruct. lia_destruct. }
    rewrite <- Nat.add_assoc in HG.
    rewrite H in HG.
    symmetry in HG; apply ctxt_one_eq_app_zero in HG; try lia.
    symmetry in HG.
    assert (zero m2 ≡[m2] G2). { eapply ctxt_zero_app_inv_l; eauto. }
    assert (zero m3 ≡[m3] G3). { eapply ctxt_zero_app_inv_r; eauto. }
    rewrite <- H0. rewrite <- H1.
    rewrite H.
    unfold one, delta, ctxt_eq, zero, ctxt_app.
    intros x Hx; destruction.

  - assert (G0 ≡[m0] (zero m0)). 
    { unfold zero, one, delta, ctxt_eq, ctxt_app in *.
      intros x Hx.
      specialize (HG x).
      assert (x < m0 + (m1 + m2) + m3) by lia; apply HG in H.
      destruct (lt_dec f m0); try lia.
      destruct (Nat.eq_dec f x); try lia.
      try lia_destruct. }
    rewrite H in *; clear H.
    rewrite <- ctxt_app_assoc in HG.
    rewrite <- Nat.add_assoc in HG.
    apply ctxt_one_eq_app_zero_inv with (n := m0) (x := f) in HG; try lia.

    assert (G1 ≡[m1] (zero m1)).
    { unfold ctxt_eq, one, delta, ctxt_app in *. 
      intros x Hx.
      specialize (HG x).
      assert (x < (m1 + m2 + m3)) by lia; apply HG in H.
      lia_destruct; unfold zero; assumption. }
    rewrite H in HG.
    rewrite <- Nat.add_assoc in HG.
    rewrite <- ctxt_app_assoc in HG.
    symmetry in HG; apply ctxt_one_eq_app_zero_inv in HG; try lia.
    rewrite H.
    
    assert (G3 ≡[m3] zero m3).
    { unfold ctxt_eq, one, delta, ctxt_app in *. 
      intros x Hx.
      assert ((x + m2) < (m2 + m3)) by lia; apply HG in H0.
      destruct (lt_dec (f - m0 - m1) (m2 + m3)); try lia.
      lia_destruct; unfold zero.
      replace (x + m2 - m2) with x in H0 by lia.
      assumption. }
    rewrite H0.
    rewrite H0 in HG.
    symmetry in HG.
    apply ctxt_one_eq_app_zero_inv_l in HG; try lia.
    rewrite HG.
    unfold one, delta, ctxt_eq, zero, ctxt_app.
    intros x Hx; destruction.
  - assert (G0 ≡[m0] (zero m0)). 
    { unfold zero, one, delta, ctxt_eq, ctxt_app in *.
      intros x Hx.
      specialize (HG x).
      assert (x < m0 + (m1 + m2) + m3) by lia; apply HG in H.
      destruct (lt_dec f m0); try lia.
      destruct (Nat.eq_dec f x); try lia.
      try lia_destruct. }
    rewrite H in *; clear H.
    rewrite <- ctxt_app_assoc in HG.
    rewrite <- Nat.add_assoc in HG.
    apply ctxt_one_eq_app_zero_inv with (n := m0) (x := f) in HG; try lia.
    
    assert (G1 ≡[m1] (zero m1)).
    { unfold ctxt_eq, one, delta, ctxt_app in *. 
      intros x Hx.
      specialize (HG x).
      assert (x < (m1 + m2 + m3)) by lia; apply HG in H.
      lia_destruct; unfold zero; assumption. }
    rewrite H in HG.
    rewrite <- Nat.add_assoc in HG.
    rewrite <- ctxt_app_assoc in HG.
    symmetry in HG; apply ctxt_one_eq_app_zero_inv in HG; try lia.
    rewrite H.
    
    assert (G2 ≡[m2] zero m2).
    { unfold ctxt_eq, one, delta, ctxt_app in *. 
      intros x Hx.
      assert (x < (m2 + m3)) by lia; apply HG in H0.
      destruct (lt_dec (f - m0 - m1) (m2 + m3)); try lia.
      lia_destruct; unfold zero.
      assumption. }
    rewrite H0.
    rewrite H0 in HG.
    symmetry in HG.
    apply ctxt_one_eq_app_zero_inv in HG; try lia.
    rewrite HG.
    unfold one, delta, ctxt_eq, zero, ctxt_app.
    intros x Hx; destruction.
Qed.
    

Lemma wf_rename_fvar_ren_commute_wpo :
  (forall m n (G : lctxt m) (D : lctxt n) (t : term),
    wf_term m n G D t ->
    forall m0 m1 m2 m3 (G0 : lctxt m0) (G1 : lctxt m1) (G2 : lctxt m2) (G3 : lctxt m3)
    (HM : m = m0 + (m1 + m2) + m3)
    (HG : G ≡[m] (@ctxt_app _ m0 (m1 + m2) G0 (@ctxt_app _ (m1 + m2) m3 (G1 ⊗ G2) G3))),
    wf_term (m0 + (m2 + m1) + m3) n (G0 ⊗ (G2 ⊗ G1) ⊗ G3) D
    (rename_fvar_term (ren_commute_str m0 m1 m2 m3) t)) /\
  (forall m n (G : lctxt m) (D : lctxt n) (P : proc),
    wf_proc m n G D P ->
    forall m0 m1 m2 m3 (G0 : lctxt m0) (G1 : lctxt m1) (G2 : lctxt m2) (G3 : lctxt m3)
    (HM : m = m0 + (m1 + m2) + m3)
    (HG : G ≡[m] (@ctxt_app _ m0 (m1 + m2) G0 (@ctxt_app _ (m1 + m2) m3 (G1 ⊗ G2) G3))),
      wf_proc (m0 + (m2 + m1) + m3) n (G0 ⊗ (G2 ⊗ G1) ⊗ G3) D
    (rename_fvar_proc (ren_commute_str m0 m1 m2 m3) P)) /\ 
  (forall m n (G : lctxt m) (D : lctxt n) (o : oper),
    wf_oper m n G D o ->
    forall m0 m1 m2 m3 (G0 : lctxt m0) (G1 : lctxt m1) (G2 : lctxt m2) (G3 : lctxt m3)
      (HM : m = m0 + (m1 + m2) + m3)
      (HG : G ≡[m] (@ctxt_app _ m0 (m1 + m2) G0 (@ctxt_app _ (m1 + m2) m3 (G1 ⊗ G2) G3))),
      wf_oper (m0 + (m2 + m1) + m3) n (G0 ⊗ (G2 ⊗ G1) ⊗ G3) D
    (rename_fvar_oper (ren_commute_str m0 m1 m2 m3) o)).
Proof.
apply wf_tpo_ind; intros; simpl.
- eapply wf_bag with (G' := G') (D' := D'); try assumption.
  specialize (H (m' + m0) m1 m2 m3 (@ctxt_app _ m' m0 G' G0) G1 G2 G3).
  assert (m' + m = m' + m0 + (m1 + m2) + m3) by lia. 
  apply H in H0.
  2 : { rewrite HG. repeat rewrite <- ctxt_app_assoc. reflexivity. } 
  rewrite ren_shift_ren_commute_str.
  repeat rewrite <- Nat.add_assoc in H0.
  repeat rewrite <- ctxt_app_assoc in H0.
  repeat rewrite <- Nat.add_assoc.  
  repeat rewrite <- ctxt_app_assoc.
  apply H0.

- eapply wf_def with (D' := D'); auto.
  
- eapply wf_app; auto.
  + unfold ren_commute_str.
    lia_goal.
  + rewrite HG in HG0.
    rewrite HM in HG0.
    repeat rewrite <- Nat.add_assoc in HG0.
    repeat rewrite <- ctxt_app_assoc in HG0.
    assert (zero m0 ≡[m0] G0). { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0).
                                 auto. }
    specialize (ctxt_zero_app_inv_r _ _ _ _ HG0).
    intros HX.
    assert (zero m1 ≡[m1] G1). { specialize (ctxt_zero_app_inv_l _ _ _ _ HX).
                                 auto. }
    specialize (ctxt_zero_app_inv_r _ _ _ _ HX).
    intros HY.
    assert (zero m2 ≡[m2] G2). { specialize (ctxt_zero_app_inv_l _ _ _ _ HY).
                                 auto. }
    specialize (ctxt_zero_app_inv_r _ _ _ _ HY).
    intros H2.
    rewrite <- H.
    rewrite <- H0.
    rewrite <- H1.
    rewrite <- H2.
    repeat rewrite ctxt_app_zero_zero.
    reflexivity.
    
- rewrite HG in HG0.
  symmetry in HG0.
  rewrite HM in HG0.
  replace (m0 + (m1 + m2) + m3) with (m0 + ((m1 + m2) + m3)) in HG0 by lia.
  specialize (sum_app_inv_ctxt _ _ _ _ _ _ HG0).
  intros HX.
  destruct HX as (G1a & G2a & G1x & G2x & HG1 & HG2 & HGa & HGx).
  symmetry in HGx.
  apply sum_app_inv_ctxt in HGx.
  destruct HGx as (G1y & G2y & G1d & G2d & HG1' & HG2' & HGy & HGd).
  symmetry in HGy.
  apply sum_app_inv_ctxt in HGy.
  destruct HGy as (G1b & G2b & G1c & G2c & HG1'' & HG2'' & HGb & HGc).
  eapply wf_par with (D1:=D1)(D2:=D2)(G1 := (G1a ⊗ (G1c ⊗ G1b) ⊗ G1d))(G2 := (G2a ⊗ (G2c ⊗ G2b) ⊗ G2d)); auto.
  + eapply H; auto.
    subst.
    rewrite <- Nat.add_assoc.
    rewrite HG1. rewrite HG1'.  rewrite HG1''. reflexivity.
  + eapply H0; auto.
    subst.
    rewrite <- Nat.add_assoc.
    rewrite HG2. rewrite HG2'.  rewrite HG2''. reflexivity.
  + rewrite <- HGa.
    rewrite <- HGb.
    rewrite <- HGc.
    rewrite <- HGd.
    repeat rewrite lctxt_sum_app_dist.
    reflexivity.

- eapply wf_emp; auto.
  rewrite HG in HG0.
  rewrite HM in HG0.
  repeat rewrite <- Nat.add_assoc in HG0.
  repeat rewrite <- ctxt_app_assoc in HG0.
  assert (zero m0 ≡[m0] G0). { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HG0).
  intros HX.
  assert (zero m1 ≡[m1] G1). { specialize (ctxt_zero_app_inv_l _ _ _ _ HX).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HX).
  intros HY.
  assert (zero m2 ≡[m2] G2). { specialize (ctxt_zero_app_inv_l _ _ _ _ HY).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HY).
  intros H2.
  rewrite <- H.
  rewrite <- H0.
  rewrite <- H1.
  rewrite <- H2.
  repeat rewrite ctxt_app_zero_zero.
  reflexivity.

- eapply wf_tup; auto.
  rewrite HG in HG0.
  rewrite HM in HG0.
  repeat rewrite <- Nat.add_assoc in HG0.
  repeat rewrite <- ctxt_app_assoc in HG0.
  assert (zero m0 ≡[m0] G0). { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HG0).
  intros HX.
  assert (zero m1 ≡[m1] G1). { specialize (ctxt_zero_app_inv_l _ _ _ _ HX).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HX).
  intros HY.
  assert (zero m2 ≡[m2] G2). { specialize (ctxt_zero_app_inv_l _ _ _ _ HY).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HY).
  intros H2.
  rewrite <- H.
  rewrite <- H0.
  rewrite <- H1.
  rewrite <- H2.
  repeat rewrite ctxt_app_zero_zero.
  reflexivity.
  
- eapply wf_bng; auto.
  + unfold ren_commute_str.
    lia_goal.
  + rewrite HG in HG0.
    rewrite HM in HG0.
    symmetry.
    apply ren_commute_str_one; auto. lia.
    rewrite <- ctxt_app_assoc.
    assumption.
    
- rewrite HG in HG0.
  rewrite HM in HG0.
  repeat rewrite <- Nat.add_assoc in HG0.
  repeat rewrite <- ctxt_app_assoc in HG0.
  assert (zero m0 ≡[m0] G0). { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HG0).
  intros HX.
  assert (zero m1 ≡[m1] G1). { specialize (ctxt_zero_app_inv_l _ _ _ _ HX).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HX).
  intros HY.
  assert (zero m2 ≡[m2] G2). { specialize (ctxt_zero_app_inv_l _ _ _ _ HY).
                               auto. }
  specialize (ctxt_zero_app_inv_r _ _ _ _ HY).
  intros H3.
  rewrite <- H0.
  rewrite <- H1.
  rewrite <- H2.
  rewrite <- H3.
  eapply wf_lam; auto.
  + repeat rewrite ctxt_app_zero_zero.
    reflexivity.
  + assert (zero (m0 + (m2 + m1) + m3) ≡[m0 + (m2 + m1) + m3] G0 ⊗ (G2 ⊗ G1) ⊗ G3).
    { rewrite <- H1. rewrite <- H0. rewrite <- H2. rewrite <- H3.
      repeat rewrite ctxt_app_zero_zero.
      reflexivity. }
    rewrite H4.
    eapply H; auto.
    rewrite HM.
    repeat rewrite Nat.add_assoc in HG0.
    repeat rewrite Nat.add_assoc.
    repeat rewrite <- ctxt_app_assoc.
    assumption.
Qed.    

Lemma wf_rename_fvar_ren_commute_proc :
forall m n (G : lctxt m) (D : lctxt n) (P : proc),
  wf_proc m n G D P ->
    forall m0 m1 m2 m3 (G0 : lctxt m0) (G1 : lctxt m1) (G2 : lctxt m2) (G3 : lctxt m3)
    (HM : m = m0 + (m1 + m2) + m3)
    (HG : G ≡[m] (@ctxt_app _ m0 (m1 + m2) G0 (@ctxt_app _ (m1 + m2) m3 (G1 ⊗ G2) G3))),
      wf_proc (m0 + (m2 + m1) + m3) n (G0 ⊗ (G2 ⊗ G1) ⊗ G3) D
    (rename_fvar_proc (ren_commute_str m0 m1 m2 m3) P).
Proof.
  apply wf_rename_fvar_ren_commute_wpo.
Qed.

Lemma wf_weaken_f_wpo :
  (forall m0 n (G0 : lctxt m0) (D : lctxt n) (t : term),
    wf_term m0 n G0 D t ->
    forall m m' m'' (G : lctxt m) (G' : lctxt m') 
    (HM : m0 = m' + m)
    (HG : G0 ≡[m0] (@ctxt_app _ m' m G' G)),
    wf_term (m' + m'' + m) n (G' ⊗ zero m'' ⊗ G) D
      (rename_fvar_term (weaken_tail_ren m m' m'') t))
  /\
    
    (forall m0 n (G0 : lctxt m0) (D : lctxt n) (P : proc),
        wf_proc m0 n G0 D P ->
        forall m m' m'' (G : lctxt m) (G' : lctxt m') 
          (HM : m0 = m' + m)
          (HG : G0 ≡[m0] (@ctxt_app _ m' m G' G)),
          wf_proc (m' + m'' + m) n (G' ⊗ zero m'' ⊗ G) D
            (rename_fvar_proc (weaken_tail_ren m m' m'') P))
  /\
    (forall m0 n (G0 : lctxt m0) (D : lctxt n) (o : oper),
        wf_oper m0 n G0 D o ->
        forall m m' m'' (G : lctxt m) (G' : lctxt m') 
          (HM : m0 = m' + m)
          (HG : G0 ≡[m0] (@ctxt_app _ m' m G' G)),
          wf_oper (m' + m'' + m) n (G' ⊗ zero m'' ⊗ G) D
            (rename_fvar_oper (weaken_tail_ren m m' m'') o)).
Proof.
apply wf_tpo_ind; intros; simpl.
- eapply wf_bag with (G' := G') (D' := D'); try assumption.
  specialize (H m0 (m' + m'0) m'' G0 (@ctxt_app _ m' m'0 G' G'0)).
  assert (m' + m = m' + m'0 + m0) by lia. 
  apply H in H0.
  rewrite ren_shift_weaken_commute.
  repeat rewrite <- Nat.add_assoc in H0.
  repeat rewrite <- ctxt_app_assoc in H0.
  repeat rewrite <- Nat.add_assoc.  
  repeat rewrite <- ctxt_app_assoc.
  apply H0.
   
  rewrite HG.
  replace (m' + m) with (m' + (m'0 + m0)) by lia.
  repeat rewrite <- ctxt_app_assoc. 
  reflexivity.

- eapply wf_def with (D' := D'); auto.

- eapply wf_app; auto.
  + unfold weaken_tail_ren.
    lia_goal.
  + rewrite HG in HG0.
    rewrite HM in HG0.
    assert (zero m0 ≡[m0] G0). 
    { specialize (ctxt_zero_app_inv_r _ _ _ _ HG0); auto. }
    specialize (ctxt_zero_app_inv_r _ _ _ _ HG0).
    assert (zero m' ≡[m'] G'). 
    { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0); auto. }
    rewrite <- H.
    rewrite <- H0.
    repeat rewrite ctxt_app_zero_zero.
    reflexivity.
    
- rewrite HG in HG0.
  symmetry in HG0.
  rewrite HM in HG0.
  specialize (sum_app_inv_ctxt _ _ _ _ _ _ HG0).
  intros HX.
  destruct HX as (G1a & G2a & G1x & G2x & HG1 & HG2 & HGa & HGx).
  symmetry in HGx.
  eapply wf_par with (D1:=D1) (D2:=D2)
                     (G1 := (@ctxt_app _ (m' + m'') m0 (G1a ⊗ (zero m'')) G1x))
                     (G2 := (@ctxt_app _ (m' + m'') m0 (G2a ⊗ (zero m'')) G2x)); 
  try assumption.
  + specialize (H m0 m' m'' G1x G1a).
    symmetry in HM; rewrite HM in HG1.
    symmetry in HM; apply H in HM.
    all : assumption.
  + specialize (H0 m0 m' m'' G2x G2a).
    symmetry in HM; rewrite HM in HG2.
    symmetry in HM; apply H0 in HM.
    all : assumption.
  + symmetry in HGa; rewrite HGa.
    replace (zero m'') with ((zero m'') ⨥ (zero m'')).
    rewrite <- lctxt_sum_app_dist.
    replace ((zero m'') ⨥ (zero m'')) with (zero m'').
    rewrite HGx.
    rewrite <- lctxt_sum_app_dist.
    reflexivity.
    all : (unfold zero, sum; apply functional_extensionality; reflexivity).

- eapply wf_emp; auto.
  rewrite HG in HG0.
  rewrite HM in HG0.
  assert (zero m0 ≡[m0] G0). 
  { specialize (ctxt_zero_app_inv_r _ _ _ _ HG0); auto. }
  assert (zero m' ≡[m'] G'). 
  { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0); auto. }
  rewrite <- H.
  rewrite <- H0.
  repeat rewrite ctxt_app_zero_zero.
  reflexivity.

- eapply wf_tup; auto.
  rewrite HG in HG0.
  rewrite HM in HG0.
  assert (zero m0 ≡[m0] G0). 
  { specialize (ctxt_zero_app_inv_r _ _ _ _ HG0); auto. }
  assert (zero m' ≡[m'] G'). 
  { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0); auto. }
  rewrite <- H.
  rewrite <- H0.
  repeat rewrite ctxt_app_zero_zero.
  reflexivity.
  
- eapply wf_bng; auto.
  + unfold weaken_tail_ren.
    lia_goal.
  + rewrite HG in HG0.
    rewrite HM in HG0.
    symmetry.
    unfold weaken_tail_ren.
    destruct (lt_dec f m').
    * unfold one, delta, ctxt_eq, ctxt_app, zero in *;
      intros x Hx; destruction.
      all : try (specialize (HG0 x);
                 assert (x < m' + m0) by lia; apply HG0 in H;
                 lia_destruct).
      specialize (HG0 (x - m''));
      assert (x - m'' < m' + m0) by lia; apply HG0 in H;
      lia_destruct.
      replace (x - (m' + m'')) with (x - m'' - m') by lia;
      assumption.
    * unfold one, delta, ctxt_eq, ctxt_app, zero in *;
      intros x Hx; destruction.
      all : try (specialize (HG0 x);
                 assert (x < m' + m0) by lia; apply HG0 in H;
                 lia_destruct).
      all : try (specialize (HG0 (x - m''));
                 assert (x - m'' < m' + m0) by lia; apply HG0 in H;
                 lia_destruct;
                 replace (x - (m' + m'')) with (x - m'' - m') by lia;
                 assumption). 
    
- rewrite HG in HG0.
  rewrite HM in HG0.
  assert (zero m0 ≡[m0] G0). 
  { specialize (ctxt_zero_app_inv_r _ _ _ _ HG0); auto. }
  assert (zero m' ≡[m'] G').
  { specialize (ctxt_zero_app_inv_l _ _ _ _ HG0); auto. }
  rewrite <- H0.
  rewrite <- H1.
  eapply wf_lam; auto.
  + repeat rewrite ctxt_app_zero_zero.
    reflexivity.
  + assert (zero (m' + m'' + m0) ≡[m' + m'' + m0] ((G' ⊗ (zero m'')) ⊗ G0)).
    { rewrite <- H1. rewrite <- H0. 
      repeat rewrite ctxt_app_zero_zero.
      reflexivity. }
    rewrite H2.
    eapply H; auto.
    rewrite HM.
    assumption.
Qed.    

Lemma weak_rvar_oper :
  forall m n0 (G : lctxt m) (D0 : lctxt n0) (o:oper),
    wf_oper m n0 G D0 o ->
    forall n n' n'' (D : lctxt n) (D' : lctxt n')
      (HN : n0 = n' + n)
      (HD0 : D0 ≡[n0] (@ctxt_app _ n' n D' D)),
      wf_oper m (n' + n'' + n) G (D' ⊗ zero n'' ⊗ D) (rename_rvar_oper (weaken_tail_ren n n' n'') o).
Proof.
  intros; induction o.
  all : (unfold weaken_tail_ren, rename_rvar_oper; simpl).
  - inversion H; existT_eq; subst. 
    apply wf_emp; auto. 
    unfold ctxt_app, zero, ctxt_eq in *.
    intros x Hx; destruction.
    + specialize (HD0 x).
      specialize (HD x).
      assert (x < n' + n) by lia.
      assert (x < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      lia_destruct.
    + specialize (HD0 (x - n'')).
      specialize (HD (x - n'')).
      assert (x - n'' < n' + n) by lia.
      assert (x - n'' < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      destruct (lt_dec (x - n'') n') in H0.
      * contradict n0; lia.
      * rewrite H0 in H1.
        replace (x - (n' + n'')) with (x - n'' - n') by lia.
        assumption.
  - inversion H; existT_eq; subst. 
    apply wf_tup; auto.
    1, 2 : (destruction; lia).
    unfold ctxt_app, zero, ctxt_eq, one, delta, sum in *.
    intros x Hx; destruction.
    all : (try lia_destruct).
    all : (try (specialize (HD0 x); specialize (HD x); 
                assert (l' : x < n' + n) by lia;
                assert (l'' : x < n' + n) by lia;
                apply HD0 in l'; apply HD in l'';
                lia_destruct)).
    all : (try (specialize (HD0 (x - n'')); specialize (HD (x - n'')); 
                assert (l' : (x -  n'') < n' + n) by lia;
                assert (l'' : (x - n'') < n' + n) by lia;
                apply HD0 in l'; apply HD in l'';
                lia_destruct;
                rewrite l' in l'';
                replace (x - (n' + n'')) with (x - n'' - n') by lia;
                assumption)).
    all : (try (specialize (HD0 (x - n'')); specialize (HD (x - n''));
                assert (l' : (x -  n'') < n' + n) by lia;
                assert (l'' : (x - n'') < n' + n) by lia;
                apply HD0 in l'; apply HD in l'';
                lia_destruct;
                rewrite l'' in l';
                replace (r2 + n'' - (n' + n'')) with (r2 + n'' - n'' - n') by lia;
                symmetry; assumption)).
  - inversion H; existT_eq; subst. 
    apply wf_bng; auto.
    unfold ctxt_app, zero, ctxt_eq in *.
    intros x Hx; destruction.
    + specialize (HD0 x).
      specialize (HD x).
      assert (x < n' + n) by lia.
      assert (x < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      lia_destruct.
    + specialize (HD0 (x - n'')).
      specialize (HD (x - n'')).
      assert (x - n'' < n' + n) by lia.
      assert (x - n'' < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      destruct (lt_dec (x - n'') n') in H0.
      * contradict n0; lia.
      * rewrite H0 in H1.
        replace (x - (n' + n'')) with (x - n'' - n') by lia.
        assumption.
  - inversion H; existT_eq; subst.
    apply wf_lam; auto.
    unfold ctxt_app, zero, ctxt_eq in *.
    intros x Hx; destruction.
    + specialize (HD0 x).
      specialize (HD x).
      assert (x < n' + n) by lia.
      assert (x < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      lia_destruct.
    + specialize (HD0 (x - n'')).
      specialize (HD (x - n'')).
      assert (x - n'' < n' + n) by lia.
      assert (x - n'' < n' + n) by lia.
      apply HD0 in H0; apply HD in H1.
      destruct (lt_dec (x - n'') n') in H0.
      * contradict n0; lia.
      * rewrite H0 in H1.
        replace (x - (n' + n'')) with (x - n'' - n') by lia.
        assumption.
    + erewrite rename_rvar_id_term.
      apply WFT.
      eapply wf_ws_term; eauto.
Qed.

Lemma app_zero_0 : 
  forall n (G : lctxt n),
  G ≡[n] (@ctxt_app _ n 0 G (zero 0)).
Proof. 
  intros.
  unfold ctxt_app, zero; intros x Hx; destruct (lt_dec x n).
  reflexivity. 
  try lia.
Qed. 

Lemma app_zero_0_l : 
  forall n (G : lctxt n),
  G ≡[n] (@ctxt_app _ 0 n (zero 0) G).
Proof. 
  intros.
  unfold ctxt_app, zero; intros x Hx.
  destruct (lt_dec x 0).
  lia. 
  replace (x - 0) with x by lia; lia.
Qed. 

Lemma ctxt_app_split : forall m n (G : lctxt (m + n)),
  exists (G1 : lctxt m) (G2 : lctxt n),
    G ≡[m + n] G1 ⊗ G2.
Proof.
  intros.
  exists (ctxt_trim m n G).
  exists (ctxt_retract m n G).
  rewrite (ctxt_app_trim_retract m n _ G) at 1.
  reflexivity.
Qed.  

Lemma one_app_zero : 
  forall n n' r,
    r < n' + n -> 
    (r < n' /\ ((one (n' + n) r) ≡[ n' + n] (one n' r) ⊗ (zero n)))
    \/ ((~ r < n') /\ ((one (n' + n) r) ≡[ n' + n] (zero n') ⊗ (one n (r - n')))).
Proof. 
  intros.
  destruct (lt_dec r n').
  + left. 
    unfold one, delta, ctxt_eq, ctxt_app.
    split; try assumption. 
    intros x Hx; destruction.
    unfold zero; try lia.
  + right.
    unfold one, delta, ctxt_eq, ctxt_app.
    split; try lia. 
    intros x Hx; destruction.
    unfold zero; try lia.
Qed.
  

Lemma weak_rvar_proc :
  forall m n0 (G : lctxt m) (D0 : lctxt n0) (P : proc),
    wf_proc m n0 G D0 P ->
    forall n n' n'' (D : lctxt n) (D' : lctxt n')
      (HN : n0 = n' + n)
      (HD0 : D0 ≡[n0] (@ctxt_app _ n' n D' D)),
      wf_proc m (n' + n'' + n) G (@ctxt_app _ (n' + n'') n (@ctxt_app _ n' n'' D' (zero n'')) D)
                (rename_rvar_proc (weaken_tail_ren n n' n'') P).
Proof.
  intros m n0 G D0 P.
  revert m n0 G D0.
  induction P. 

  - intros m n0 G D0 HP n n' n'' D D'.
    intros Hn0 HD0.
    simpl; inversion HP; existT_eq; subst.
    specialize (ctxt_app_split n' n D'0) as [D'01 [D'02 HEQD'0]].
    specialize (one_app_zero n n' r) as H1r. 
    assert (Hr : r < n' + n) by (apply HR).
    apply H1r in Hr; clear H1r; destruct Hr as [Hr | Hr'].

    + destruct Hr as [Hr Hr1].
      rewrite Hr1 in HD; rewrite HEQD'0 in HD.
      rewrite -> lctxt_sum_app_dist in HD.
      eapply wf_def with (D := (@ctxt_app _ (n' + n'') n (D' ⊗ zero n'') D))
                         (D' := (@ctxt_app _ (n' + n'') n (D'01 ⊗ (zero n'')) D'02)).
      3 : { eapply weak_rvar_oper with (n0 := n' + n) (D0 := D'0).
            all : (try assumption).
            reflexivity. }
      all : (unfold weaken_tail_ren; destruct (lt_dec r n'); try lia).
      assert (one (n' + n'' + n) r ≡[ n' + n'' + n] 
              (@ctxt_app _ (n' + n'') n ((one n' r) ⊗ (zero n'')) (zero n))).
      { unfold one, delta, ctxt_eq, ctxt_app, zero.
        intros x Hx.
        destruction; try lia. }
      rewrite H; clear H.
      repeat (rewrite -> lctxt_sum_app_dist).
      rewrite HD0 in HD.
      specialize (ctxt_app_inv_l_eq n' n D' (one n' r ⨥ D'01) D (zero n ⨥ D'02)) as HD1.
      specialize (ctxt_app_inv_r_eq n' n D' (one n' r ⨥ D'01) D (zero n ⨥ D'02)) as HD1'.
      assert (HD2 : (@ctxt_app _ n' n D' D) ≡[ n' + n] 
                    (@ctxt_app _ n' n (one n' r ⨥ D'01) (zero n ⨥ D'02))) by apply HD.
      apply HD1 in HD; clear HD1; apply HD1' in HD2; clear HD1'.
      rewrite HD; rewrite HD2.
      reflexivity.

    + destruct Hr' as [Hr' Hr'1].
      rewrite Hr'1 in HD; rewrite HEQD'0 in HD.
      rewrite -> lctxt_sum_app_dist in HD.
      eapply wf_def with (D := (@ctxt_app _ (n' + n'') n (D' ⊗ zero n'') D))
                         (D' := (@ctxt_app _ (n' + n'') n (D'01 ⊗ (zero n'')) D'02)).
      3 : { eapply weak_rvar_oper with (n0 := n' + n) (D0 := D'0).
            all : (try assumption).
            reflexivity. }
      all : (unfold weaken_tail_ren; destruct (lt_dec r n'); try lia).
      assert (one (n' + n'' + n) (r + n'') ≡[ n' + n'' + n] 
                  (@ctxt_app _ (n' + n'') n ((zero n') ⊗ (zero n'')) (one n (r - n')))).
      { unfold one, delta, ctxt_eq, ctxt_app, zero.
        intros x Hx.
        destruction; try lia. }
      rewrite H; clear H.
      repeat (rewrite -> lctxt_sum_app_dist).
      rewrite HD0 in HD.
      specialize (ctxt_app_inv_l_eq n' n D' (zero n' ⨥ D'01) D (one n (r - n') ⨥ D'02)) as HD1.
      specialize (ctxt_app_inv_r_eq n' n D' (zero n' ⨥ D'01) D (one n (r - n') ⨥ D'02)) as HD1'.
      assert (HD2 : (@ctxt_app _ n' n D' D) ≡[ n' + n]  (zero n' ⨥ D'01) ⊗ (one n (r - n') ⨥ D'02)) by apply HD.
      apply HD1 in HD; clear HD1; apply HD1' in HD2; clear HD1'.
      rewrite HD; rewrite HD2.
      reflexivity.

  - intros m n0 G D0 HP n n' n'' D D'.
    intros Hn0 HD0.
    simpl; inversion HP; existT_eq; subst.
    eapply wf_app with (D := (@ctxt_app _ (n' + n'') n (D' ⊗ zero n'') D)); try assumption.
    unfold weaken_tail_ren; destruct (lt_dec r n'); try lia.
    specialize (one_app_zero n n' r) as Hr1. 
    assert (r < n' + n) by lia; apply Hr1 in H; clear Hr1.
    unfold weaken_tail_ren; destruct (lt_dec r n'); try lia.
    destruct H as [Hr1 | Hr1']. destruct Hr1 as [Hr1 Hr1'].
    assert (one (n' + n'' + n) r ≡[ n' + n'' + n] 
            (@ctxt_app _ (n' + n'') n ((one n' r) ⊗ (zero n'')) (zero n))).
    { unfold one, delta, ctxt_eq, ctxt_app, zero.
      intros x Hx.
      destruction; try lia. }
    rewrite H; clear H. 
    rewrite Hr1' in HD; rewrite HD0 in HD.
    specialize (ctxt_app_inv_l_eq n' n D' (one n' r) D (zero n)) as HD1.
    specialize (ctxt_app_inv_r_eq n' n D' (one n' r) D (zero n)) as HD1'.
    assert (HD2 : (@ctxt_app _ n' n D' D) ≡[ n' + n] (one n' r) ⊗ (zero n)) by (apply HD).
    apply HD1 in HD; clear HD1; apply HD1' in HD2; clear HD1'.
    rewrite HD; rewrite HD2.
    reflexivity.
    destruct Hr1' as [contra Hr]; try lia.
    destruct H as [H' | H]; try lia.
    destruct H as [n0' H]. 
    rewrite H in HD; rewrite HD0 in HD.
    assert (one (n' + n'' + n) (r + n'') ≡[ n' + n'' + n] 
                  (@ctxt_app _ (n' + n'') n ((zero n') ⊗ (zero n'')) (one n (r - n')))).
    { unfold one, delta, ctxt_eq, ctxt_app, zero.
      intros x Hx.
      destruction; try lia. }
    rewrite H0; clear H0.
    specialize (ctxt_app_inv_l_eq n' n D' (zero n') D (one n (r - n'))) as HD1.
    specialize (ctxt_app_inv_r_eq n' n D' (zero n') D (one n (r - n'))) as HD1'.
    assert (HD2 : (@ctxt_app _ n' n D' D) ≡[ n' + n]  (zero n') ⊗ (one n (r - n'))) by apply HD.
    apply HD1 in HD; clear HD1; apply HD1' in HD2; clear HD1'.
    rewrite HD; rewrite HD2.
    reflexivity.

  - intros m n0 G D0 HP n n' n'' D D' Hn0 HD0.
    inversion HP; existT_eq; subst.
    specialize (sum_app_inv_ctxt n' n D1 D2 D' D) as H.
    rewrite HD0 in HD.
    assert (H' : (@ctxt_app _ n' n D' D) ≡[ n' + n] D1 ⨥ D2) by (apply HD).
    apply H in H'; clear H.
    destruct H' as (Da1 & Da2 & Db1 & Db2 & HD1 & HD2 & HDa & HDb).
    specialize (IHP1 m (n' + n) G1 D1). 
    eapply IHP1 with (n := n) (n' := n') (n'' := n'') (D' := Da1) (D := Db1) in WFP1; 
    try assumption; try reflexivity.
    specialize (IHP2 m (n' + n) G2 D2). 
    eapply IHP2 with (n := n) (n' := n') (n'' := n'') (D' := Da2) (D := Db2) in WFP2; 
    try assumption; try reflexivity.
    eapply wf_par with (G1 := G1) (G2 := G2)
                       (D1 := (@ctxt_app _ (n' + n'') n (Da1 ⊗ (zero n'')) Db1))
                       (D2 := (@ctxt_app _ (n' + n'') n (Da2 ⊗ (zero n'')) Db2));
    try assumption.
    repeat (rewrite -> lctxt_sum_app_dist).
    rewrite -> sum_zero_r.
    rewrite HDa; rewrite HDb.
    reflexivity. 
Qed.

Lemma zeros_commute :
  forall n m,
    (@ctxt_app _ n m (zero n) (zero m)) = (@ctxt_app _ m n (zero m) (zero n)).
Proof.
  intros.
  unfold zero, ctxt_app. 
  apply functional_extensionality.
  intros x; destruction.
Qed.

Lemma split_one : 
  forall n' n r',
  r' < n' -> 
  (one (n' + n) r') ≡[ n' + n] (@ctxt_app _ n' n (one n' r') (zero n)).
Proof.
  intros.
  unfold one, delta, ctxt_eq, ctxt_app, zero.
  intros x Hx; destruction.
Qed.

Definition freshen_body m m' m'' (n:nat) n' n'' (r':nat) (Q:proc) :=
  let Q0 := rename_fvar_proc (ren_commute_str 0 m'' m' m) Q in
  let Q1 := rename_rvar_proc (weaken_tail_ren (n'' + 1) 0 n') Q0 in
  let Q2 := @rename_rvar_proc (n' + (n'' + 1) + n) (n' + (n'' + 1) + n) (rename_var (n' + n'') r') Q1 in
  Q2.


Lemma wf_freshen_ren_comm :
forall m m' m'' n'' (G'0 : lctxt m'') (D'1 : lctxt n'') (Q : proc),
  (wf_proc (m'' + (m' + m)) (n'' + 1) (@ctxt_app _ m'' (m' + m) G'0 (zero (m' + m))) 
           (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1])) Q) -> 
    (wf_proc (m' + m'' + m) (n'' + 1) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) 
                (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1])) 
                (rename_fvar_proc (ren_commute_str 0 m'' m' m) Q)).
Proof.
  intros. 
  replace (m' + m'' + m) with (0 + (m' + m'') + m) by lia.
  assert ((@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) ≡[(m' + m'') + m]
          (@ctxt_app _ 0 ((m' + m'') + m) (zero 0) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)))).
  apply app_zero_0_l with (n := (m' + m'') + m).
  rewrite H0; clear H0.
  rewrite -> ctxt_app_assoc.
  apply wf_rename_fvar_ren_commute_proc with (m := m'' + (m' + m)) (n := n'' + 1)
                                             (G := (@ctxt_app _ m'' (m' + m) G'0 (zero (m' + m)))).
  try assumption.
  try lia.
  unfold ctxt_app, zero, ctxt_eq; intros x Hx; destruction.
  replace (x - 0) with x by lia; reflexivity.
Qed.

Lemma wf_freshen_weaken :
forall m m' m'' n' n'' (G'0 : lctxt m'') (D'1 : lctxt n'') (Q : proc),
  (wf_proc (m' + m'' + m) (n'' + 1) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) 
                (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1])) 
                (rename_fvar_proc (ren_commute_str 0 m'' m' m) Q)) -> 
    wf_proc (m' + m'' + m) (n' + (n'' + 1)) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m))
            (@ctxt_app _ n' (n'' + 1) (zero n') ((D'1 ⊗ (1 [0 ↦ 1]))))
            ((rename_rvar_proc (weaken_tail_ren (n'' + 1) 0 n')
              (rename_fvar_proc (ren_commute_str 0 m'' m' m) Q))).
Proof.
  intros.
  apply weak_rvar_proc with (m := m' + m'' + m) (n0 := n'' + 1) 
                            (G := (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)))
                            (D0 := (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1]))) 
                            (P := (rename_fvar_proc (ren_commute_str 0 m'' m' m) Q))
                            (n := (n'' + 1)) (n' := 0) (n'' := n') 
                            (D' :=(zero 0)) 
                            (D := (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1]))).
  try assumption.
  try lia.
  unfold ctxt_app, zero, one, delta, ctxt_eq; intros x Hx; destruction.
  replace (x - 0) with x by lia; reflexivity.
Qed.

Lemma wf_freshen_rename_var :
forall m m' m'' n n' n'' (G'0 : lctxt m'') (D'1 : lctxt n'') (Q2 : proc) (r' : rvar) 
  (Hr' : r' < n'),
  wf_proc (m' + m'' + m) (n' + (n'' + 1)) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m))
          (@ctxt_app _ n' (n'' + 1) (zero n') ((D'1 ⊗ (1 [0 ↦ 1]))))
          Q2 ->
  wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) 
           (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) (one n' r') (@ctxt_app _ n'' 1 D'1 (zero 1))) (zero n)) 
           (@rename_rvar_proc (n' + (n'' + 1) + n) (n' + (n'' + 1) + n) (rename_var (n' + n'') r') Q2).
Proof.
  intros.
  specialize (wf_proc_app_zero (m' + m'' + m) (n' + (n'' + 1)) 
                               (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m))
                               (@ctxt_app _ n' (n'' + 1) (zero n') (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1])))
                               Q2) as H'.
  apply H' with (m' := 0) (n' := n) in H; clear H'.
  replace (m' + m'' + m + 0) with (m' + m'' + m) in H by lia.
  rewrite <- app_zero_0 with (n := m' + m'' + m) in H.
  apply wf_proc_rename_rvar with (m := (m' + m'' + m)) (n := n' + (n'' + 1) + n)
                                 (G := (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)))
                                 (D := (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) (zero n') (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1]))) (zero n)))
                                 (P := Q2)
                                 (D1 := (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) (zero n') (@ctxt_app _ n'' 1 D'1 (zero 1))) (zero n)))
                                 (r := n' + n'') (r' := r') (cr := 1) (cr' := 0).
  try assumption. 
  all : try lia.
  1, 2 : (unfold zero, ctxt_app; destruction).
  1, 2 : (unfold zero, ctxt_app, one, delta, ctxt_eq, sum; intros x Hx; destruction).   
Qed.

Lemma wf_freshen : 
forall m m' m'' n n' n'' (G'0 : lctxt m'') (D'1 : lctxt n'') (Q : proc) (r' : rvar),
  (wf_proc (m'' + (m' + m)) (n'' + 1) (@ctxt_app _ m'' (m' + m) G'0 (zero (m' + m))) 
           (@ctxt_app _ n'' 1 D'1 (1 [0 ↦ 1])) Q) -> 
    r' < n' ->
    (wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) 
                (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) (one n' r') (@ctxt_app _ n'' 1 D'1 (zero 1))) (zero n)) 
                (freshen_body m m' m'' n n' n'' r' Q)).
Proof.
  intros.
  unfold freshen_body.
  apply wf_freshen_ren_comm in H.
  apply wf_freshen_weaken with (n' := n') in H.
  apply wf_freshen_rename_var with (n := n) (r' := r') in H.
  all : assumption.
Qed.

Lemma wf_prim_step_app :
forall (m m' m'' n n' n'' : nat) (G : lctxt m) (r : rvar) (r' : var) (f : fvar) (P Q : proc),
  wf_term m n G (zero n)  
    (bag m' n'
       (par
          (par P
             (par
                (def r (lam (bag m'' n'' Q)))
                (def r (bng f))))
          (app f r'))) ->
  wf_term m n G (zero n)
    (bag (m' + m'') (n' + (n'' + 1))
       (par
          (weaken_f m m' m''
          (par P
             (par
                (def r (lam (bag m'' n'' Q)))
                (def r (bng f)))))
          (freshen_body m m' m'' n n' n'' r' Q))).
Proof.
  intros.
  inversion H; existT_eq; subst. clear H.
  inversion WFP; existT_eq; subst. clear WFP.
  inversion WFP1; existT_eq; subst. clear WFP1.
  inversion WFP3; existT_eq; subst. clear WFP3.

  (* First, prove the weakened part correct *)
  specialize (ctxt_app_split m' m G0) as [G01 [G02 HEQG0]].
  assert (wf_proc (m' + m'' + m) (n' + n) (G01 ⊗ (zero m'') ⊗ G02) D0 (weaken_f m m' m'' P)) as HWEAKP.
  { eapply wf_weaken_f_wpo; eauto. }
  
  specialize (ctxt_app_split m' m G4) as [G41 [G42 HEQG4]].
  assert (wf_proc (m' + m'' + m) (n' + n) (G41 ⊗ (zero m'') ⊗ G42) D4 (weaken_f m m' m'' (def r (lam (bag m'' n'' Q))))) as HWEAKLAM.
  { eapply wf_weaken_f_wpo; eauto. } 

  specialize (ctxt_app_split m' m G5) as [G51 [G52 HEQG5]].
  assert (wf_proc (m' + m'' + m) (n' + n) (G51 ⊗ (zero m'') ⊗ G52) D5 (weaken_f m m' m'' (def r (bng f)))) as HWEAKBNG.
  { eapply wf_weaken_f_wpo; eauto. }

  (* Rearrange linear contexts *)
  (* D0, D3, D2 *)
  specialize (ctxt_app_split n' n D0) as [D01 [D02 HEQD0]].
  specialize (ctxt_app_split n' n D3) as [D31 [D32 HEQD3]].
  assert (HEQD3' : D3 ≡[ n' + n] (@ctxt_app _ n' n D31 D32)) by (apply HEQD3).
  specialize (ctxt_app_split n' n D2) as [D21 [D22 HEQD2]].
  rewrite HD0 in HD; rewrite HEQD0 in HD.
  rewrite HEQD3 in HD; rewrite HEQD2 in HD.
  repeat rewrite -> lctxt_sum_app_dist in HD.
  assert (HD' : (@ctxt_app _ n' n D' (zero n)) ≡[ n' + n] 
                (@ctxt_app _ n' n ((D01 ⨥ D31) ⨥ D21) ((D02 ⨥ D32) ⨥ D22))) by (apply HD).
  specialize (ctxt_app_inv_r_eq n' n D' ((D01 ⨥ D31) ⨥ D21) (zero n) ((D02 ⨥ D32) ⨥ D22)) as H0.
  apply H0 in HD; symmetry in HD.
  assert ((D02 ⨥ D32) ⨥ D22 ≡[ n] zero n) by apply HD.
  specialize (sum_zero_inv_r_eq n (D02 ⨥ D32) D22) as HD22; apply HD22 in HD; clear HD22.
  specialize (sum_zero_inv_l_eq n (D02 ⨥ D32) D22) as H0232; apply H0232 in H; clear H0232.
  assert (D02 ⨥ D32 ≡[ n] zero n) by (apply H).
  specialize (sum_zero_inv_r_eq n D02 D32) as H32; apply H32 in H; clear H32.
  specialize (sum_zero_inv_l_eq n D02 D32) as H02; apply H02 in H1; clear H02.

  (* D4, D5 *)
  specialize (ctxt_app_split n' n D4) as [D41 [D42 HEQD4]].
  specialize (ctxt_app_split n' n D5) as [D51 [D52 HEQD5]].
  rewrite HD1 in HEQD3; rewrite H in HEQD3; rewrite HEQD4 in HEQD3; rewrite HEQD5 in HEQD3.
  rewrite -> lctxt_sum_app_dist in HEQD3.
  specialize (ctxt_app_inv_r_eq n' n (D41 ⨥ D51) D31 (D42 ⨥ D52) (zero n)) as H'.
  apply H' in HEQD3; clear H'.
  assert (HD42 : D42 ≡[ n] zero n) by (apply sum_zero_inv_l_eq in HEQD3; assumption).
  assert (HD52 : D52 ≡[ n] zero n) by (apply sum_zero_inv_r_eq in HEQD3; assumption).

  (* wf_proc P *)
  assert (wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G01 (zero m'')) G02) 
                  (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) D01 (zero (n'' + 1))) D02) 
                  (weaken_f m m' m'' P)) as HP.
  { rewrite H1.
    assert ((@ctxt_app _ (n' + (n'' + 1)) n (D01 ⊗ (zero (n'' + 1))) (zero n)) ≡[(n' + (n'' + 1)) + n]
            (@ctxt_app _ n' (n + (n'' + 1)) D01 ((zero n) ⊗ (zero (n'' + 1))))).
    { rewrite <- ctxt_app_assoc.
      rewrite -> zeros_commute with (n := n'' + 1) (m := n).
      reflexivity. }
    rewrite H2.
    rewrite -> ctxt_app_assoc with (c := D01) (d := (zero n)) (e := (zero (n'' + 1))).
    rewrite HEQD0 in HWEAKP; rewrite H1 in HWEAKP.
    replace (n' + (n'' + 1) + n) with ((n' + n) + (n'' + 1)) by lia.
    specialize (wf_proc_app_zero (m' + m'' + m) (n' + n)
                                 (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G01 (zero m'')) G02)
                                 (@ctxt_app _ n' n D01 (zero n)) (weaken_f m m' m'' P)) as HP.
    apply HP with (m' := 0) (n' := n'' + 1) in HWEAKP; clear HP.
    assert ((@ctxt_app _ (m' + m'' + m) 0 (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G01 (zero m'')) G02) (zero 0)) 
            ≡[m' + m'' + m + 0] (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G01 (zero m'')) G02)).
    symmetry; replace (m' + m'' + m + 0) with (m' + m'' + m) by lia; apply app_zero_0.
    rewrite H3 in HWEAKP. 
    replace (m' + m'' + m + 0) with (m' + m'' + m) in HWEAKP by lia; try assumption. }
  
  (* wf_proc lam *)
  assert (wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G41 (zero m'')) G42) 
                (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) D41 (zero (n'' + 1))) D42) 
                (weaken_f m m' m'' (def r (lam (bag m'' n'' Q))))) as HLAM.
  { rewrite HD42. 
    assert ((@ctxt_app _ (n' + (n'' + 1)) n (D41 ⊗ (zero (n'' + 1))) (zero n)) ≡[(n' + (n'' + 1)) + n]
            (@ctxt_app _ n' (n + (n'' + 1)) D41 ((zero n) ⊗ (zero (n'' + 1))))).
    { rewrite <- ctxt_app_assoc.
      rewrite -> zeros_commute with (n := n'' + 1) (m := n).
      reflexivity. }
    rewrite H2.
    rewrite -> ctxt_app_assoc with (c := D41) (d := (zero n)) (e := (zero (n'' + 1))).
    rewrite HEQD4 in HWEAKLAM; rewrite HD42 in HWEAKLAM.
    replace (n' + (n'' + 1) + n) with ((n' + n) + (n'' + 1)) by lia.
    specialize (wf_proc_app_zero (m' + m'' + m) (n' + n)
                                (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G41 (zero m'')) G42)
                                (@ctxt_app _ n' n D41 (zero n)) (weaken_f m m' m'' (def r (lam (bag m'' n'' Q))))) as HLAM.
    apply HLAM with (m' := 0) (n' := n'' + 1) in HWEAKLAM; clear HLAM.
    assert ((@ctxt_app _ (m' + m'' + m) 0 (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G41 (zero m'')) G42) (zero 0)) 
            ≡[m' + m'' + m + 0] (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G41 (zero m'')) G42)).
    symmetry; replace (m' + m'' + m + 0) with (m' + m'' + m) by lia; apply app_zero_0.
    rewrite H3 in HWEAKLAM. 
    replace (m' + m'' + m + 0) with (m' + m'' + m) in HWEAKLAM by lia; try assumption. }
  
  (* wf_proc bng *)
  assert (wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G51 (zero m'')) G52) 
                (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) D51 (zero (n'' + 1))) D52) 
                (weaken_f m m' m'' (def r (bng f)))) as HBNG.
  { rewrite HD52. 
    assert ((@ctxt_app _ (n' + (n'' + 1)) n (D51 ⊗ (zero (n'' + 1))) (zero n)) ≡[(n' + (n'' + 1)) + n]
            (@ctxt_app _ n' (n + (n'' + 1)) D51 ((zero n) ⊗ (zero (n'' + 1))))).
    { rewrite <- ctxt_app_assoc.
      rewrite -> zeros_commute with (n := n'' + 1) (m := n).
      reflexivity. }
    rewrite H2.
    rewrite -> ctxt_app_assoc with (c := D51) (d := (zero n)) (e := (zero (n'' + 1))).
    rewrite HEQD5 in HWEAKBNG; rewrite HD52 in HWEAKBNG.
    replace (n' + (n'' + 1) + n) with ((n' + n) + (n'' + 1)) by lia.
    specialize (wf_proc_app_zero (m' + m'' + m) (n' + n)
                                (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G51 (zero m'')) G52)
                                (@ctxt_app _ n' n D51 (zero n)) (weaken_f m m' m'' (def r (bng f)))) as HBNG.
    apply HBNG with (m' := 0) (n' := n'' + 1) in HWEAKBNG; clear HBNG.
    assert ((@ctxt_app _ (m' + m'' + m) 0 (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G51 (zero m'')) G52) (zero 0)) 
            ≡[m' + m'' + m + 0] (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' G51 (zero m'')) G52)).
    symmetry; replace (m' + m'' + m + 0) with (m' + m'' + m) by lia; apply app_zero_0.
    rewrite H3 in HWEAKBNG. 
    replace (m' + m'' + m + 0) with (m' + m'' + m) in HWEAKBNG by lia; try assumption. }
  
  (* Deal with the freshened body of Q *)
  inversion WFP1; existT_eq; subst. clear WFP1.
  inversion WFO; existT_eq; subst. clear WFO.
  inversion WFT; existT_eq; subst. clear WFT.
  inversion WFP2; existT_eq; subst. clear WFP2.

  (* Show assumption for wf_freshen lemma. *)
  assert (r' < n').
  { apply H0 in HD'; clear H0. 
    rewrite H1 in HD'; rewrite H in HD'.
    rewrite -> sum_zero_l in HD'; symmetry in HD'.
    rewrite HD' in HEQD2; rewrite HEQD2 in HD4.
    unfold ctxt_app, zero, ctxt_eq, one, delta in HD4; specialize (HD4 r').
    assert (HR0' : r' < n' + n) by (apply HR0).
    apply HD4 in HR0; clear HD4.
    destruct (Nat.eq_dec r' r') in HR0; try lia.
    destruct (lt_dec r' (n' + n)) in HR0; try lia.
    destruct (lt_dec r' n') in HR0; try lia. }

  (* Apply wf_freshen lemma. *)
  assert (wf_proc (m' + m'' + m) ((n' + (n'' + 1)) + n) (@ctxt_app _ (m' + m'') m (@ctxt_app _ m' m'' (zero m') G'0) (zero m)) 
                (@ctxt_app _ (n' + (n'' + 1)) n (@ctxt_app _ n' (n'' + 1) (one n' r') (@ctxt_app _ n'' 1 D'1 (zero 1))) (zero n)) 
                (freshen_body m m' m'' n n' n'' r' Q)).
  { unfold freshen_body.
    apply wf_freshen; try assumption. }

  (* Apply HP, HLAM, HBNG, H3 using wf_bag, wf_par. *)
  eapply wf_bag with (G' := (@ctxt_app _ m' m'' G' G'0)) (D' := (@ctxt_app _ n' (n'' + 1) D' (D'1 ⊗ (zero 1)))).
    
    (* Unrestricted context *)
    + intros x Hx; unfold ctxt_app; destruct (lt_dec x m').
      specialize (UG' x); apply UG' in l; try assumption.
      assert (Hxm' : x - m' < m'') by lia; specialize (UG'0 (x - m')); apply UG'0 in Hxm'; try assumption.

    (* Linear context *)
    + intros x Hx; unfold ctxt_app, zero; destruct (lt_dec x n').
      specialize (UD' x); apply UD' in l; try assumption.
      destruct (lt_dec (x - n') n''). 
      specialize (UD'0 (x - n')); apply UD'0 in l; try assumption. 
      assert (0 = 0) by lia; try lia.
      
    (* Apply wf_par *)
    + eapply wf_par with (G1 := (@ctxt_app _ (m' + m'') m ((G01 ⊗ zero m'') ⨥ (G41 ⊗ zero m'') ⨥ (G51 ⊗ zero m''))
                                (G02 ⨥ G42 ⨥ G52)))
                         (G2 := (@ctxt_app _ (m' + m'') m (zero m' ⊗ G'0) (zero m)))
                         (D1 := (@ctxt_app _ (n' + (n'' + 1)) n 
                                  ((D01 ⊗ zero (n'' + 1)) ⨥ (D41 ⊗ zero (n'' + 1)) ⨥ (D51 ⊗ zero (n'' + 1)))
                                  (D02 ⨥ D42 ⨥ D52)))
                         (D2 := (@ctxt_app _ (n' + (n'' + 1)) n (one n' r' ⊗ (D'1 ⊗ zero 1)) (zero n))).
      (* Use H3 *)
      2 : assumption.

      (* Unrestricted contexts *)
      2 : { repeat rewrite -> lctxt_sum_app_dist. repeat rewrite -> sum_zero_r. rewrite -> sum_zero_l.
            rewrite HG0 in HG; rewrite HG1 in HG; rewrite HEQG0 in HG; rewrite HEQG4 in HG; rewrite HEQG5 in HG.
            rewrite HG3 in HG; rewrite -> sum_zero_r in HG; repeat rewrite -> lctxt_sum_app_dist in HG.
            assert (HG' : (@ctxt_app _ m' m G' G) ≡[ m' + m] 
                          (@ctxt_app _ m' m (G01 ⨥ (G41 ⨥ G51)) (G02 ⨥ (G42 ⨥ G52)))) by (apply HG).
            specialize (ctxt_app_inv_r_eq m' m G' (G01 ⨥ (G41 ⨥ G51)) G (G02 ⨥ (G42 ⨥ G52))) as HGeq.
            specialize (ctxt_app_inv_l_eq m' m G' (G01 ⨥ (G41 ⨥ G51)) G (G02 ⨥ (G42 ⨥ G52))) as HG'eq.
            apply HGeq in HG; apply HG'eq in HG'; clear HGeq; clear HG'eq.
            rewrite HG'; rewrite HG; repeat rewrite -> sum_assoc; reflexivity. }

      (* Linear contexts *)
      2 : { repeat rewrite -> lctxt_sum_app_dist. repeat rewrite -> sum_zero_r. rewrite -> sum_zero_l.
            rewrite HEQD4 in HD1; rewrite HEQD5 in HD1; rewrite -> lctxt_sum_app_dist in HD1; rewrite HEQD3 in HD1.
            rewrite HEQD3' in HD1.
            assert (HD1' : (@ctxt_app _ n' n D31 D32) ≡[ n' + n] 
                           (@ctxt_app _ n' n (D41 ⨥ D51) (zero n))) by (apply HD1).
            specialize (ctxt_app_inv_r_eq n' n D31 (D41 ⨥ D51) D32 (zero n)) as HD3eq.
            specialize (ctxt_app_inv_l_eq n' n D31 (D41 ⨥ D51) D32 (zero n)) as HD3'eq.
            apply HD3eq in HD1; clear HD3eq; apply HD3'eq in HD1'; clear HD3'eq.
            rewrite HD1 in HD'; rewrite HD1' in HD'; rewrite H1 in HD'.
            rewrite HEQD2 in HD4. rewrite -> split_one in HD4.
            assert (HD4' : (@ctxt_app _ n' n D21 D22) ≡[ n' + n] 
                           (@ctxt_app _ n' n (one n' r') (zero n))) by (apply HD4).
            specialize (ctxt_app_inv_r_eq n' n D21 (one n' r') D22 (zero n)) as HD4eq.
            specialize (ctxt_app_inv_l_eq n' n D21 (one n' r') D22 (zero n)) as HD4'eq.
            apply HD4eq in HD4; clear HD4eq; apply HD4'eq in HD4'; clear HD4'eq.
            rewrite HD4 in HD'; rewrite HD4' in HD'.
            specialize (ctxt_app_inv_l_eq n' n D' ((D01 ⨥ (D41 ⨥ D51)) ⨥ one n' r') (zero n) 
                                                  ((zero n ⨥ zero n) ⨥ zero n)) as HD''.
            apply HD'' in HD'; clear HD''; rewrite HD'.
            rewrite H1; rewrite HD42; rewrite HD52; repeat rewrite -> sum_zero_r.
            repeat rewrite <- sum_assoc; reflexivity. try assumption. }

      (* Apply wf_par *)
      simpl. eapply wf_par with (G1 := (@ctxt_app _ (m' + m'') m (G01 ⊗ (zero m'')) G02))
                                (G2 := (@ctxt_app _ (m' + m'') m (G41 ⊗ (zero m'')) G42) ⨥ 
                                       (@ctxt_app _ (m' + m'') m (G51 ⊗ (zero m'')) G52))
                                (D1 := (@ctxt_app _ (n' + (n'' + 1)) n (D01 ⊗ (zero (n'' + 1))) D02))
                                (D2 := (@ctxt_app _ (n' + (n'' + 1)) n (D41 ⊗ (zero (n'' + 1))) D42) ⨥ 
                                       (@ctxt_app _ (n' + (n'' + 1)) n (D51 ⊗ (zero (n'' + 1))) D52)).
      (* Use HP *)
      assumption.

      (* Unrestricted and linear contexts *)
      2, 3 : (repeat rewrite -> lctxt_sum_app_dist; repeat rewrite -> sum_assoc; reflexivity).
      
      (* Apply wf_par *)
      eapply wf_par with (G1 := (@ctxt_app _ (m' + m'') m (G41 ⊗ (zero m'')) G42))
                         (G2 := (@ctxt_app _ (m' + m'') m (G51 ⊗ (zero m'')) G52))
                         (D1 := (@ctxt_app _ (n' + (n'' + 1)) n (D41 ⊗ (zero (n'' + 1))) D42))
                         (D2 := (@ctxt_app _ (n' + (n'' + 1)) n (D51 ⊗ (zero (n'' + 1))) D52));
      (* Use HLAM and HBNG *)
      try assumption. 
      (* Unrestricted and linear contexts *)
      all : try reflexivity.
Qed.

(*
P |
r <- (r1, r2)
r <- (r1', r2')
*) 

Definition cut_renaming n (r1 r2 r1' r2':nat) : ren n n :=
  if Nat.eq_dec r1 r1' then
    if Nat.eq_dec r2 r2' then
      ren_id n
    else
      rename_var r2 r2'
  else
    if Nat.eq_dec r2 r2' then
      rename_var r1 r1'
    else
      if Nat.eq_dec r1 r2 then
        if Nat.eq_dec r1' r2' then
          ren_id n
        else
          rename_var r1' r2'
      else
        if Nat.eq_dec r1' r2' then
          rename_var r1 r2
        else
          if Nat.eq_dec r1 r2' then
            if Nat.eq_dec r1' r2 then
              ren_id n
            else
              rename_var r1' r2
          else
            if Nat.eq_dec r1' r2 then
              rename_var r1 r2'
            else
              @ren_compose n n nat (rename_var r1 r1') (rename_var r2 r2').
 

Lemma wf_prim_step_tup :
  forall m m' n n' r r1 r2 r1' r2' P (G : lctxt m),
    wf_term m n G (zero n) (bag m' n' (par P (par (def r (tup r1 r2)) (def r (tup r1' r2'))))) ->
    wf_term m n G (zero n) (bag m' n' (rename_rvar_proc (cut_renaming (n' + n) r1 r2 r1' r2') P)).
Proof.
  (* UNCOMMENT FOR COMPLETE CHECKING *)
  (*
  intros.
  inversion H; existT_eq; subst; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP3; existT_eq; subst; clear WFP3.
  inversion WFO; existT_eq; subst; clear WFO.
  inversion WFO0; existT_eq; subst; clear WFO0.
  rewrite HG1 in HG0; clear HG1.
  rewrite HG2 in HG0; clear HG2.
  rewrite sum_zero_r in HG0.
  rewrite HG0 in HG; clear HG0.
  rewrite sum_zero_r in HG.
  rewrite HD1 in HD0; clear HD1.
  rewrite HD2 in HD0; clear HD2.
  rewrite <- sum_assoc in HD0.
  rewrite (@sum_assoc _ D'0) in HD0.
  rewrite (@sum_commutative _ D'0) in HD0.
  do 2 rewrite sum_assoc in HD0.
  unfold one in HD0.
  rewrite delta_sum in HD0. simpl in HD0.
  apply sum_app_inv_ctxt in HD.
  destruct HD as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
  rewrite EQ2 in HD0.
  assert (DB1 ≡[n] zero n). { apply sum_zero_inv_l_eq in EQ4. assumption. }
  assert (DB2 ≡[n] zero n). { apply sum_zero_inv_r_eq in EQ4. assumption. }
  clear EQ4.
  rewrite H in EQ1; clear H.
  rewrite H0 in EQ2, HD0; clear H0.

  rewrite HD3 in HD0; clear HD3.
  rewrite HD4 in HD0; clear HD4.

  repeat rewrite <- sum_assoc in HD0.
  rewrite (@sum_assoc _ (one (n' + n) r2)) in HD0.
  rewrite (@sum_commutative _ (one (n' + n) r2)) in HD0.
  rewrite <- sum_assoc in HD0.

   
  assert (   (r < n') /\ (r1 < n') /\ (r1' < n') /\ (r2 < n') /\ (r2' < n')).
  { eapply ctxt_app_c_zero_inv; eauto. }
  destruct H as (HR0' & HR1' & HR2' & HR3' & HR4').

  
  symmetry in EQ3.
  assert (forall x, x < n' -> (DA1 ⨥ DA2) x = 2 \/ (DA1 ⨥ DA2) x = 0).
  { intros. eapply (@ctxt_eq_imp _ nat _ _ (fun z => z = 2 \/ z = 0) EQ3); eauto. }

  
  rewrite <- HG in WFP1. clear HG.
  rewrite EQ1 in WFP1.  clear EQ1. 

  assert (
      DA2 ≡[n']
        n' [r ↦ 2] ⨥ (one n' r1 ⨥ (one n' r1' ⨥ (one n' r2 ⨥ one n' r2')))).
  { unfold ctxt_eq.  intros x HX.
    assert (x < n' + n) by lia.
    specialize (HD0 x H0).
    unfold ctxt_app, sum, one, delta, zero in HD0.
    unfold sum, one, delta.
    destruct (lt_dec x n'); try lia.
    rewrite HD0.
    clear HD0.
    lia_goal.
  } 

  assert ( r <> r1 /\ r <> r1' /\ r <> r2 /\ r <> r2' ) as HNEQ.
  { pose proof (H _ HR0').
    pose proof (H _ HR1').
    pose proof (H _ HR2').
    pose proof (H _ HR3').
    pose proof (H _ HR4').
    pose proof (H0 _ HR0').
    pose proof (H0 _ HR1').
    pose proof (H0 _ HR2').
    pose proof (H0 _ HR3').
    pose proof (H0 _ HR4').
    clear EQ2 EQ3 HD0 HD0 H H0.
    unfold one, delta, sum in *.
    lctxt_solve.
  } 

  unfold cut_renaming.

  destruct (Nat.eq_dec r1 r1'); subst.
  - destruct (Nat.eq_dec r2 r2'); subst.
    * apply wf_bag with (G' := G')(D' := DA1); auto.
      -- intros.
         specialize (H _ H1).
         specialize (H0 _ H1).
         unfold sum, one, delta in H, H0.
         lia_destruct.
      -- rewrite rename_rvar_id_proc with (m := (m'+m)).
         assumption.
         eapply tpo_wf_ws; eauto.
    * assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r1' then 0 else
                         if Nat.eq_dec z r2 then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r2 ↦ 1])
                ⨥ ((n' + n)[r2' ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        unfold ctxt_app, zero, sum, one, delta.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR3').
        pose proof (H _ HR4').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR3').
        pose proof (H0 _ HR4').
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lia_goal.
      }
      apply wf_bag with (G':=G')(D':=
                                   ((fun z : var =>
                                       if lt_dec z n' then
                                         if Nat.eq_dec z r then 0 else
                                           if Nat.eq_dec z r1' then 0 else
                                             if Nat.eq_dec z r2 then 0 else
                                               if Nat.eq_dec z r2' then 0 else DA1 z
                                       else 0)
                                      ⨥ (n' + n) [r2' ↦ 1+1])
                        ).
      -- auto.
      -- unfold sum, delta.
         intros.
         lia_goal.
         specialize (H _ H2).
         specialize (H0 _ H2).
         assert (x < (n' + n)) by lia.
         specialize (H1 _ H3).
         unfold sum, one, delta in H, H0, H1.
         lctxt_solve.
      -- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
         unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
         lctxt_solve.
  - destruct (Nat.eq_dec r2 r2'); subst.
    + assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r1 then 0 else
                         if Nat.eq_dec z r1' then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1 ↦ 1])
                ⨥ ((n' + n)[r1' ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR2').        
        pose proof (H _ HR3').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR2').        
        pose proof (H0 _ HR3').
        unfold ctxt_app, zero, sum, one, delta.
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
      }
      apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r1' then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r1' ↦ 2]).
      -- auto.
      -- unfold sum, delta.
         intros.
         lia_goal.
         specialize (H _ H2).
         specialize (H0 _ H2).
         assert (x < (n' + n)) by lia.
         specialize (H1 _ H3).
         unfold sum, one, delta in H, H0, H1.
         lctxt_solve.
      -- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
         unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
         lctxt_solve.
    + destruct (Nat.eq_dec r1 r2); subst.
      * destruct (Nat.eq_dec r1' r2'); subst.
        -- apply wf_bag with (G' := G')(D' := DA1); auto.
           ++ intros.
              specialize (H _ H1).
              specialize (H0 _ H1).
              unfold sum, one, delta in H, H0.
              lia_destruct.
           ++ rewrite rename_rvar_id_proc with (m := (m'+m)).
              assumption.
              eapply tpo_wf_ws; eauto.
        -- assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r2 then 0 else
                         if Nat.eq_dec z r1' then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1' ↦ 1])
                ⨥ ((n' + n)[r2' ↦ 1])
             ).
           
           { unfold ctxt_eq.
             intros.
             pose proof (H _ HR0').
             pose proof (H _ HR1').
             pose proof (H _ HR2').        
             pose proof (H _ HR4').
             pose proof (HD0 _ H1).
             pose proof (H0 _ HR0').
             pose proof (H0 _ HR1').
             pose proof (H0 _ HR2').        
             pose proof (H0 _ HR4').
             unfold ctxt_app, zero, sum, one, delta.
             destruct (lt_dec x n').
             - pose proof (H0 _ l).
               pose proof (H _ l).
               clear H H0 HD0.
               clear WFP1 EQ2 EQ3.
               unfold ctxt_app, zero, sum, one, delta in *.
               lctxt_solve.
             - clear H H0 HD0.
               clear WFP1 EQ2 EQ3.
               unfold ctxt_app, zero, sum, one, delta in *.
               lctxt_solve.
           }
           apply wf_bag with (G':=G')(D':=
                                        (fun z =>
                                           if lt_dec z n' then
                                             if Nat.eq_dec z r then 0 else
                                               if Nat.eq_dec z r2 then 0 else
                                                 if Nat.eq_dec z r1' then 0 else
                                                   if Nat.eq_dec z r2' then 0 else
                                                     DA1 z
                                           else 0)
                                          ⨥ (n' + n)[r2' ↦ 2]).
           ++ auto.
           ++ unfold sum, delta.
              intros.
              lia_goal.
              specialize (H _ H2).
              specialize (H0 _ H2).
              assert (x < (n' + n)) by lia.
              specialize (H1 _ H3).
              unfold sum, one, delta in H, H0, H1.
              lctxt_solve.
           ++ eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
              unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
              lctxt_solve.
      * destruct (Nat.eq_dec r1' r2'); subst.
        -- assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r2 then 0 else
                         if Nat.eq_dec z r1 then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1 ↦ 1])
                ⨥ ((n' + n)[r2 ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR2').        
        pose proof (H _ HR4').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR2').        
        pose proof (H0 _ HR4').
        unfold ctxt_app, zero, sum, one, delta.
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
      }
      apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r2 then 0 else
                                            if Nat.eq_dec z r1 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2 ↦ 2]).
           ++ auto.
           ++ unfold sum, delta.
              intros.
              lia_goal.
              specialize (H _ H2).
              specialize (H0 _ H2).
              assert (x < (n' + n)) by lia.
              specialize (H1 _ H3).
              unfold sum, one, delta in H, H0, H1.
              lctxt_solve.
           ++ eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
              unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
              lctxt_solve.
        -- destruct (Nat.eq_dec r1 r2'); subst.
           ++ destruct (Nat.eq_dec r1' r2); subst.
              ** apply wf_bag with (G' := G')(D' := DA1); auto.
                 --- intros.
                     specialize (H _ H1).
                     specialize (H0 _ H1).
                     unfold sum, one, delta in H, H0.
                     lia_destruct.
                 --- rewrite rename_rvar_id_proc with (m := (m'+m)).
                     assumption.
                     eapply tpo_wf_ws; eauto.
              ** assert (DA1 ⊗ zero n ≡[n' + n]
                           (fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r2 then 0 else
                                    if Nat.eq_dec z r1' then 0 else
                                      if Nat.eq_dec z r2' then 0 else
                                        DA1 z
                              else 0)
                           ⨥ ((n' + n)[r1' ↦ 1])
                           ⨥ ((n' + n)[r2 ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').        
                   pose proof (H _ HR3').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').        
                   pose proof (H0 _ HR3').
                   unfold ctxt_app, zero, sum, one, delta.
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 }
                 apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r2 then 0 else
                                            if Nat.eq_dec z r1' then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2 ↦ 2]).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     lia_goal.
                     specialize (H _ H2).
                     specialize (H0 _ H2).
                     assert (x < (n' + n)) by lia.
                     specialize (H1 _ H3).
                     unfold sum, one, delta in H, H0, H1.
                     lctxt_solve.
                 --- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
                     unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
                     lctxt_solve.
           ++ destruct (Nat.eq_dec r1' r2); subst.
              ** assert (DA1 ⊗ zero n ≡[n' + n]
                           (fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r1 then 0 else
                                    if Nat.eq_dec z r2 then 0 else
                                      if Nat.eq_dec z r2' then 0 else
                                        DA1 z
                              else 0)
                           ⨥ ((n' + n)[r1 ↦ 1])
                           ⨥ ((n' + n)[r2' ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').        
                   pose proof (H _ HR4').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').        
                   pose proof (H0 _ HR4').
                   unfold ctxt_app, zero, sum, one, delta.
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 }
                 apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r2 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2' ↦ 2]).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     lia_goal.
                     specialize (H _ H2).
                     specialize (H0 _ H2).
                     assert (x < (n' + n)) by lia.
                     specialize (H1 _ H3).
                     unfold sum, one, delta in H, H0, H1.
                     lctxt_solve.
                 --- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
                     unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
                     lctxt_solve.
              ** rewrite <- rename_rvar_proc_compose.

                 assert (DA1 ⊗ zero n ≡[n' + n]
                           ((fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r1 then 0 else
                                    if Nat.eq_dec z r1' then 0 else 
                                      if Nat.eq_dec z r2 then 0 else
                                        if Nat.eq_dec z r2' then 0 else
                                          DA1 z
                              else 0)
                              ⨥ ((n' + n)[r2 ↦ 1])
                              ⨥ ((n' + n)[r2' ↦ 1])
                           )
                           ⨥ ((n' + n)[r1 ↦ 1])
                           ⨥ ((n' + n)[r1' ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   
                   unfold ctxt_app, zero, sum, one, delta.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').
                   pose proof (H _ HR3').
                   pose proof (H _ HR4').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').
                   pose proof (H0 _ HR3').                   
                   pose proof (H0 _ HR4').
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 } 

                 
                 assert (wf_proc (m' + m) (n' + n) (G' ⊗ G)
                           ((((fun z =>
                                if lt_dec z n' then
                                  if Nat.eq_dec z r then 0 else
                                    if Nat.eq_dec z r1 then 0 else
                                      if Nat.eq_dec z r1' then 0 else 
                                        if Nat.eq_dec z r2 then 0 else
                                          if Nat.eq_dec z r2' then 0 else
                                            DA1 z
                                else 0)
                               ⨥ ((n' + n)[r2 ↦ 1])
                               ⨥ ((n' + n)[r2' ↦ 1])
                             )
                               ⨥ ((n' + n)[r1' ↦ 2])
                            ) ⊗ zero n)
                           (@rename_rvar_proc (n' + n) (n' + n) (rename_var r1 r1') P)).
                 { eapply wf_proc_rename_rvar with
                     (D1 := ((fun z => if lt_dec z n' then
                                      if Nat.eq_dec z r then 0 else
                                        if Nat.eq_dec z r1 then 0 else
                                          if Nat.eq_dec z r1' then 0 else 
                                            if Nat.eq_dec z r2 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                    else 0)
                               ⨥ ((n' + n)[r2 ↦ 1])
                               ⨥ ((n' + n)[r2' ↦ 1])
                     )); eauto.
                   - unfold sum, delta. lia_goal.
                   - unfold sum, delta. lia_goal.
                   - unfold ctxt_eq, ctxt_app, zero, delta, sum. intros. lctxt_solve.
                 } 
                     
                 eapply wf_bag with (G':=G')
                                    (D' := ((fun z =>
                                               if lt_dec z n' then
                                                 if Nat.eq_dec z r then 0 else
                                                   if Nat.eq_dec z r1 then 0 else
                                                     if Nat.eq_dec z r1' then 0 else 
                                                       if Nat.eq_dec z r2 then 0 else
                                                         if Nat.eq_dec z r2' then 0 else
                                                           DA1 z
                                               else 0)
                                              ⨥ ((n' + n)[r2' ↦ 2])
                                           )
                                             ⨥ ((n' + n)[r1' ↦ 2])).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     pose proof (H _ H3).
                     pose proof (H _ HR2').
                     pose proof (H _ HR4').
                     assert (x < (n' + n)) by lia.
                     pose proof (HD0 _ H7).
                     unfold ctxt_app, sum, zero, one, delta in H, H4, H5, H6, H8.
                     lia_goal.
                     clear H1 H2.
                     lia_destruct.
                 --- rewrite <- sum_assoc.
                     rewrite (@sum_commutative _ ((n' + n)[r2' ↦ 2])).
                     rewrite sum_assoc.
                     repeat rewrite <- sum_assoc in H2.
                     rewrite (@sum_commutative _ ((n' + n)[r2' ↦ 1])) in H2.
                     repeat rewrite <- sum_assoc in H2.
                     rewrite (@sum_assoc _ (n' + n) [r2 ↦ 1]) in H2.
                     rewrite (@sum_commutative _ ((n' + n)[r2 ↦ 1])) in H2.
                     repeat rewrite sum_assoc in H2.
                     
                     eapply wf_proc_rename_rvar with (cr:=1)(cr':=1)
                       (D1 := (((fun z => if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r1' then 0 else 
                                              if Nat.eq_dec z r2 then 0 else
                                                if Nat.eq_dec z r2' then 0 else
                                                  DA1 z
                                      else 0)
                                  ⨥ (n' + n)[r1' ↦ 2]))); eauto.
                     +++ unfold sum, delta.
                         intros.
                         lia_goal.
                     +++ unfold sum, delta.
                         lia_goal.
                     +++ unfold ctxt_eq, ctxt_app, sum, zero, one, delta.
                         intros.
                         clear H1 H2.
                         destruct (lt_dec x n').
                         *** pose proof (H0 _ l).
                             pose proof (H _ l).
                             unfold sum, one, delta in H1, H2.
                             lia_goal.
                         *** lia_goal.
                     +++ unfold ctxt_eq, ctxt_app, sum, zero, one, delta.
                         intros.
                         clear H1 H2.
                         destruct (lt_dec x n').
                         *** pose proof (H0 _ l).
                             pose proof (H _ l).
                             unfold sum, one, delta in H1, H2.
                             lia_goal.
                         *** lia_goal.
Qed.
   *)
Admitted.  
                   


Inductive prim_step : term -> term -> Prop :=
| step_emp_cut :
  forall m n r P,
    prim_step
      (bag m n (par P (par (def r emp) (def r emp))))
      (bag m n P)

| step_tup_cut :
  forall m' n n' r r1 r2 r1' r2' P,
    prim_step
      (bag m' n' (par P (par (def r (tup r1 r2)) (def r (tup r1' r2')))))
      (bag m' n' (rename_rvar_proc (cut_renaming (n' + n) r1 r2 r1' r2') P))
      
| step_app :
  forall m m' m'' n n' n'' r r' f P Q,
    (* (1) scope_extrude -> ren_commute_str
       (2) weaken_f after step ? *)
    let Q' := (freshen_body m m' m'' n n' n'' r' Q) in
    (* prim_step m n
      (bag m' n'
         (par P
         (par (def r (lam (bag m'' n'' Q)))
         (par (def r (bng f))
              (app f r')))))
      (bag (m' + m'') (n' + n'')
         (par P
         (par (def r (lam (bag m'' n'' Q)))
         (par (def r (bng f))
              Q')))). *)
    prim_step
    (bag m' n'
       (par
          (par P
             (par
                (def r (lam (bag m'' n'' Q)))
                (def r (bng f))))
          (app f r'))) 
    (bag (m' + m'') (n' + (n'' + 1))
       (par
          (weaken_f m m' m''
          (par P
             (par
                (def r (lam (bag m'' n'' Q)))
                (def r (bng f)))))
              Q')).


Lemma wf_prim_step :
  forall m n (G: lctxt m) t t',
    wf_term m n G (zero n) t ->
    prim_step t t' ->
    wf_term m n G (zero n) t'.
Proof.
  intros.
  inversion H0; subst; clear H0.
  - eapply wf_prim_step_emp; eauto.
  - eapply wf_prim_step_tup; eauto.
  - eapply wf_prim_step_app; eauto.
Qed.    


Inductive  step : nat -> nat -> term -> term -> Prop :=
| step_equiv : forall m n t1 t1' t2,
    t1 ≈t t1' ->
    prim_step m n t1' t2 ->
    step m n t1 t2.





(* Canonical forms -- is it needed?  ----------------------------------- *)


Inductive lt_list : list nat -> list nat -> Prop :=
| lt_nil : forall x xs, lt_list nil (x::xs)
| lt_cons : forall x y xs ys,
    x < y -> lt_list (x::xs) (y::ys)
| lt_tl : forall x xs ys,
    lt_list xs ys ->
    lt_list (x::xs) (x::ys).

Lemma lt_list_transitive : forall l1 l2 l3,
    lt_list l1 l2 -> lt_list l2 l3 -> lt_list l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0; intros.
  - inversion H.
  - inversion H0; subst.
    apply lt_nil.
    apply lt_cons. lia.
    apply lt_cons. assumption.
  - inversion H; subst.
    apply lt_nil.
    apply lt_cons. assumption.
    apply lt_tl.
    apply IHlt_list.
    assumption.
Qed.    

Lemma lt_list_lt_eq_lt_dec : forall l1 l2,
    {lt_list l1 l2} + {l1 = l2} + {lt_list l2 l1}.
Proof.
  induction l1; intros.
  - destruct l2.
    + left. right. reflexivity.
    + left. left. apply lt_nil.
  - destruct l2.
    + right. apply lt_nil.
    + specialize (lt_eq_lt_dec a n) as H.
      destruct H as [[HL | HE] | HG].
      * left. left. apply lt_cons. assumption.
      * subst.
        destruct (IHl1 l2) as [[HL | HE] | HG].
        -- left. left. apply lt_tl. assumption.
        -- subst. left. right. reflexivity.
        -- right. apply lt_tl. assumption.
      * right. apply lt_cons. assumption.
Qed.        

Unset Elimination Schemes.
Inductive lt_term : term -> term -> Prop :=
| lt_bag_m:
  forall m1 m2 n1 n2 P1 P2,
    m1 < m2 ->
    lt_term (bag m1 n1 P1) (bag m2 n2 P2)    

| lt_bag_n:
  forall m n1 n2 P1 P2,
    n1 < n2 ->
    lt_term (bag m n1 P1) (bag m n2 P2)    

| lt_bag_P:
  forall m n P1 P2,
    lt_proc P1 P2 ->
    lt_term (bag m n P1) (bag m n P2)    

with lt_proc : proc -> proc -> Prop :=
| lt_def_def_r:
  forall r1 r2 o1 o2,
    r1 < r2 ->
    lt_proc (def r1 o1) (def r2 o2)

| lt_def_def_o:
  forall r o1 o2,
    lt_oper o1 o2 ->
    lt_proc (def r o1) (def r o2)

| lt_def_app :
  forall r o f r',
    lt_proc (def r o) (app f r')

| lt_def_par :
  forall r o P1 P2,
    lt_proc (def r o) (par P1 P2)

| lt_app_app_f:
  forall f1 f2 r1 r2,
    f1 < f2 ->
    lt_proc (app f1 r1) (app f2 r2)

| lt_app_app_r:
  forall f r1 r2,
    r1 < r2 ->
    lt_proc (app f r1) (app f r2)

| lt_app_par :
  forall f r P1 P2,
    lt_proc (app f r) (par P1 P2)

| lt_par_par1 :
  forall P1 P1' P2 P2',
    lt_proc P1 P1' ->
    lt_proc (par P1 P2) (par P1' P2')

| lt_par_par2 :
  forall P P2 P2',
    lt_proc P2 P2' ->
    lt_proc (par P P2) (par P P2')

with lt_oper : oper -> oper -> Prop :=

| lt_emp_tup :
  forall r1 r2,
    lt_oper emp (tup r1 r2)

| lt_emp_bng :
  forall f,
    lt_oper emp (bng f)

| lt_emp_lam :
  forall t,
    lt_oper emp (lam t)
            
| lt_tup_tup1 :
  forall r1 r2 r1' r2',
    r1 < r1' ->
    lt_oper (tup r1 r2) (tup r1' r2')

| lt_tup_tup2 :
  forall r r2 r2',
    r2 < r2' ->
    lt_oper (tup r r2) (tup r r2')
            
| lt_tup_bng :
  forall r1 r2 f,
    lt_oper (tup r1 r2) (bng f)

| lt_tup_lam :
  forall r1 r2 t,
    lt_oper (tup r1 r2) (lam t)

| lt_bng_bng :
  forall f1 f2,
    f1 < f2 ->
    lt_oper (bng f1) (bng f2)

| lt_bng_lam :
  forall f t,
    lt_oper (bng f) (lam t)

| lt_lam_lam :
  forall t1 t2,
    lt_term t1 t2 ->
    lt_oper (lam t1) (lam t2).

Hint Constructors lt_term lt_proc lt_oper : core.



Scheme lt_term_ind := Induction for lt_term Sort Prop
    with lt_proc_ind := Induction for lt_proc Sort Prop
                        with lt_oper_ind := Induction for lt_oper Sort Prop.

Combined Scheme lt_tpo_ind from lt_term_ind, lt_proc_ind, lt_oper_ind.

Lemma lt_tpo_transitive :
  (forall t1 t2,
    lt_term t1 t2 ->
    forall t3,
      lt_term t2 t3 ->
      lt_term t1 t3)
  /\ (forall P1 P2,
        lt_proc P1 P2 ->
        forall P3,
          lt_proc P2 P3 ->
          lt_proc P1 P3)
  /\ (forall o1 o2,
        lt_oper o1 o2 ->
        forall o3,
          lt_oper o2 o3 ->
          lt_oper o1 o3).
Proof.
  apply lt_tpo_ind; intros; try inversion H; subst; eauto.
  - apply lt_bag_m. lia.
  - inversion H; subst; auto.
    apply lt_bag_n. lia.
  - inversion H0; subst; auto.
  - inversion H; subst; auto.
    apply lt_def_def_r. lia.
  - inversion H0; subst; auto.
  - apply lt_app_app_f. lia.
  - apply lt_app_app_r. lia.
  - inversion H0; subst; auto.
  - inversion H0; subst; auto.
  - apply lt_tup_tup1. lia.
  - apply lt_tup_tup2. lia.
  - apply lt_bng_bng. lia.
  - inversion H0; subst; auto.
Qed.

Lemma lt_top_lt_eq_lt_dec :
  (forall t1,
    forall t2, {lt_term t1 t2} + {t1 = t2} + {lt_term t2 t1})
  *
    ((forall P1,
       forall P2, {lt_proc P1 P2} + {P1 = P2} + {lt_proc P2 P1})
     * (forall o1,
         forall o2,  {lt_oper o1 o2} + {o1 = o2} + {lt_oper o2 o1}))%type.
Proof.
  apply tpo_rect; intros.
  - destruct t2.
    specialize (lt_eq_lt_dec m m0) as [[HL | HE] | HG].
    + left. left. auto.
    + subst.
      specialize (lt_eq_lt_dec n n0) as [[HL | HE] | HG].
      * left. left.  auto.
      * subst.
        destruct (H P0) as [[HL | HE] | HG].
        -- left. left.  auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + right.  auto.
  - destruct P2.
    specialize (lt_eq_lt_dec r r0) as [[HL | HE] | HG].
    + left. left. auto.
    + subst.
      destruct (H o0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + right. auto.
    + left. left.  auto.
    + left. left.  auto.
  - destruct P2.
    + right. auto.
    + specialize (lt_eq_lt_dec f f0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. specialize (lt_eq_lt_dec r r0) as [[HL | HE] | HG].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + left. left. auto.
  - destruct P0.
    + right. auto.
    + right. auto.
    + destruct (H P0_1) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. 
        destruct (H0 P0_2) as [[HL | HE] | HG].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
  - destruct o2.
    + left. right. reflexivity.
    + left. left. auto.
    + left. left. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + destruct (lt_eq_lt_dec r1 r0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst.
        destruct (lt_eq_lt_dec r2 r3) as [[HL' | HE'] | HG'].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + left. left. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + right. auto.
    + specialize (lt_eq_lt_dec f f0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + right. auto.
    + right. auto.
    + destruct (H t0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
Qed.        

Unset Elimination Schemes.
Inductive ForallTerm (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : term -> Prop :=
| Forall_bag:
  forall m n P,
    ForallProc PT PP PO P ->
    PT (bag m n P) ->
    ForallTerm PT PP PO (bag m n P)
with 
  ForallProc (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : proc -> Prop :=
| Forall_def : forall r o,
    PP (def r o) ->
    ForallOper PT PP PO o ->
    ForallProc PT PP PO (def r o)

| Forall_app : forall f r,
    PP (app f r) ->
    ForallProc PT PP PO (app f r)

| Forall_par : forall P1 P2,
    ForallProc PT PP PO P1 ->
    ForallProc PT PP PO P2 ->
    ForallProc PT PP PO (par P1 P2)
with
  ForallOper (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : oper -> Prop :=
| Forall_emp :
  PO emp ->
  ForallOper PT PP PO emp

| Forall_tup :
  forall r1 r2,
    PO (tup r1 r2) ->
    ForallOper PT PP PO (tup r1 r2)

| Forall_bng :
  forall f,
    PO (bng f) ->
    ForallOper PT PP PO (bng f)

| Forall_lam :
  forall t,
    PO (lam t) ->
    ForallTerm PT PP PO t ->
    ForallOper PT PP PO (lam t).

Scheme Forallterm_ind := Induction for ForallTerm Sort Prop
    with Forallproc_ind := Induction for ForallProc Sort Prop
                        with Foralloper_ind := Induction for ForallOper Sort Prop.

Combined Scheme Foralltpo_ind from Forallterm_ind, Forallproc_ind, Foralloper_ind.

Definition locally_ordered_wrt (P:proc) :=
  ForallProc (fun t => True) (fun P' => P = P' \/ lt_proc P P') (fun o => True).



Unset Elimination Schemes.
Inductive canonical_term : term -> Prop :=
| can_term :
  forall m n P,
    canonical_proc P ->
    canonical_term (bag m n P)

with canonical_proc : proc -> Prop :=
| can_def_tl :
  forall r o,
    canonical_oper o ->
    canonical_proc (def r o)

| can_app_tl :
  forall f r,
    canonical_proc (app f r)

| can_def_cons :
  forall r o P,
    canonical_oper o ->
    canonical_proc P ->
    locally_ordered_wrt (def r o) P ->
    canonical_proc (par (def r o) P)

| can_app_cons :
  forall f r P,
    canonical_proc P ->
    locally_ordered_wrt (app f r) P ->
    canonical_proc (par (app f r) P)
                   
with canonical_oper : oper -> Prop :=
| can_emp :
  canonical_oper emp
                 
| can_tup :
  forall r1 r2,
    canonical_oper (tup r1 r2)

| can_bng :
  forall f,
    canonical_oper (bng f)

| can_lam :
  forall t,
    canonical_term t ->
    canonical_oper (lam t).


