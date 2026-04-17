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

Definition proc := True.
Definition rvar := True.

Inductive EC_term :=
| Ebag (m n:nat) (EP : EC_proc)   (* nu. {f1...fm} {r1..rn} EP *)

with EC_proc :=
| Ehol
| Edeflam (r : rvar) (Et : EC_term)  (* r <- lam r'. Et *)
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



Inductive less_Epars : EC_term -> EC_term -> Prop :=
| top_Epar : 
  forall (m n : nat) (EP : EC_proc) (P : proc),
    less_Epars (Ebag m n EP) (Ebag m n (Epar EP P))
.

Lemma less_Epars_wf_helper : 
  (forall (Et : EC_term), Acc less_Epars Et) /\
  (forall (EP : EC_proc) m n, Acc less_Epars (Ebag m n EP)).
Proof. 
  apply EC_ind; intros.
  (* Ebag is immediate by IH *)
  - apply H.
  (* Ehol and Edeflam are base cases: there is no Epar to remove *)
  - constructor; intros. inversion H.
  - constructor; intros. inversion H0.
  (* Epar follows from IH *)
  - constructor; intros. inversion H0; subst. apply H.
Qed.

Lemma less_Epars_wf : well_founded less_Epars.
Proof. unfold well_founded; apply less_Epars_wf_helper. Qed.


(* Gives the number of lambda bindings encountered when traversing 
      to the hole (i.e. how many scopes deep the hole is) *)
Fixpoint hole_depth Et := hole_depth_proc (get_proc_Et Et)
with hole_depth_proc (EP : EC_proc) : nat :=
  match EP with
  | Ehol => 0
  | Edeflam _ Et => 1 + hole_depth Et
  | Epar EP' _ => hole_depth_proc EP'
  end.

Definition is_hole_scope_at_top := compose (eqb 0) hole_depth.
Definition is_hole_scope_at_top_proc := compose (eqb 0) hole_depth_proc.

(* States the hole_depth of an EC is less than another *)
Definition hole_depth_lt (Et1 Et2 : EC_term) := 
  lt (hole_depth Et1) (hole_depth Et2).

(* Every EC is accessible with hole_depth_lt.
   Used to prove well-foundedness of split_hole_scope. *)
Lemma hole_depth_lt_wf_helper : 
  (forall (Et : EC_term), Acc hole_depth_lt Et) /\
  (forall (EP : EC_proc) m n, Acc hole_depth_lt (Ebag m n EP)).
Proof. 
  apply EC_ind; intros.
  (* Ebag is immediate by IH *)
  - apply H.
  (* Ehol has depth 0 and is the base case *)
  - constructor; intros. unfold hole_depth_lt in H; simpl in H. lia.
  (* Elam adds to depth *)
  - constructor; intros.
    (* Case on whether we need a new Acc layer before IH *)
    destruct (Nat.eqb_spec (hole_depth y) (hole_depth Et)).
    + constructor; intros. apply (Acc_inv H). 
      unfold hole_depth_lt in *. rewrite <- e. apply H1.
    + apply (Acc_inv H). unfold hole_depth_lt in *. simpl in H0. lia.
  (* Epar follows from IH *)
  - constructor; intros. specialize H with m n. apply (Acc_inv H).
    unfold hole_depth_lt in *; auto.
Qed.

Definition hole_depth_lt_OR_less_Epars :=
  fun Et1 Et2 => hole_depth_lt Et1 Et2 \/ less_Epars Et1 Et2.

(* Every EC is accessible with hole_depth_lt.
   Used to prove well-foundedness of split_hole_scope. *)
Lemma hole_depth_lt_OR_less_Epars_wf_helper : 
  (forall (Et : EC_term), Acc hole_depth_lt_OR_less_Epars Et) /\
  (forall (EP : EC_proc) m n, Acc hole_depth_lt_OR_less_Epars (Ebag m n EP)).
Proof. 
  unfold hole_depth_lt_OR_less_Epars, hole_depth_lt. apply EC_ind; intros.
  (* Ebag is immediate by IH *)
  - apply H.
  (* Ehol has depth 0 and has no Epars *)
  - constructor; intros.
    simpl in H. destruct H.
    + lia.
    + inversion H.
  (* Elam adds to depth but has no Epars *)
  - constructor; intros. destruct H0.


    + (* Case on whether we need a new Acc layer before IH *)
      simpl in H0.
      destruct (Nat.eqb_spec (hole_depth y) (hole_depth Et)).
      * constructor; intros. apply (Acc_inv H).
        rewrite <- e; clear e. destruct H1; auto.
         admit.
      * apply (Acc_inv H). simpl in H0. lia.
    + inversion H0.
  (* Epar follows from IH *)
  - constructor; intros. destruct H0.
    + apply (Acc_inv (H m n)). auto.
    + inversion H0; subst. apply H.
Admitted.



Lemma hole_depth_lt_wf : well_founded hole_depth_lt.
Proof. unfold well_founded; apply hole_depth_lt_wf_helper. Qed.

Lemma hole_depth_lt_OR_less_Epars_wf : 
  well_founded (fun Et1 Et2 => hole_depth_lt Et1 Et2 \/ less_Epars Et1 Et2).
Proof. unfold well_founded; intros. Search well_founded. Print Nat.lt_wf. Admitted.






(* Given an EC, pops the top scope from the next scope containing the hole
      (if different), returning a pair whose first element is the top scope
      and second element is the EC process containing the next scope.
    1) If the hole is at the top scope, returns (EC, Ehol)
    2) If the hole is under a lambda, returns (EC_top, EC_lam) where:
        - EC_top is the EC with the lamdef replaced with a hole
        - EC_lam is the lamdef removed from the EC

  If this function takes EC and returns (EC_top, EC_next),
    1) Filling EC_top with EC_next will give EC.
    2) EC_next is either Ehol or Edeflam
    3) If EC_next is Ehol, then EC_top is EC *)

Fixpoint pop_EC_scope_proc (EP : EC_proc) : EC_proc * EC_proc :=
  match EP with
  | Ehol => (Ehol, Ehol)    (* Hole is at the top scope *)
  | Epar EP' P => let (EP1, EP2) := pop_EC_scope_proc EP' in   (* Recurse *)
                      (Epar EP1 P, EP2)
  | Edeflam _ _ => (Ehol, EP)    (* Split top and next scope *)
  end.

Definition pop_EC_scope (Et : EC_term) : EC_term * EC_proc :=
  match Et with
  | Ebag m n EP => let (EP1, EP2) := pop_EC_scope_proc EP in   (* Recurse *)
                      (Ebag m n EP1, EP2)
  end.


  

(* pop_EC_scope reduces hole_depth *)
Lemma pop_EC_scope_reduces_hole_depth :
  forall Et Et' Et0 r,
    pop_EC_scope Et = (Et0, Edeflam r Et') ->
    hole_depth_lt Et' Et.
Proof.
  intro Et; unfold hole_depth_lt. destruct Et.
  induction EP; intros; simpl in *.
  - discriminate.
  - injection H; intros. rewrite H0. apply Nat.lt_succ_diag_r.
  - destruct (pop_EC_scope_proc EP). eapply IHEP. 
    injection H; intros. rewrite H0; reflexivity.
Defined.


(* HELPER FUNCTION! ACC is the proof of accessibility for Et_cur 
    (i.e. that the hole_depth of Et_cur decreases at each call) *)
Fixpoint split_hole_scope_builder (r : rvar) (Et_acc Et_cur : EC_term) 
        (ACC : Acc hole_depth_lt Et_cur) {struct ACC} : EC_term * EC_proc :=
  (match pop_EC_scope Et_cur as y 
      return (pop_EC_scope Et_cur = y) -> EC_term * EC_proc with
  | (_, Ehol) => fun _ => (Et_acc, Edeflam r Et_cur)
  | (Et_next, Edeflam r' Et_rest) => fun HEQ =>
          let ACC_Et_rest := Acc_inv ACC 
              (pop_EC_scope_reduces_hole_depth Et_cur Et_rest Et_next r' HEQ) in
          split_hole_scope_builder r'
              Et_next Et_rest ACC_Et_rest
  | _ => fun _ => (Ebag 0 0 Ehol, Ehol) (* Cannot reach here *)
  end) eq_refl.


(* Applies pop_EC_scope until the "hole scope" is reached,
      separating the hole scope from the rest of the EC.
   Given an EC, returns a pair whose 
      first element is the EC with the hole scope replaced by a hole
      and second element is the hole scope.
   The invariants of pop_EC_scope are also held by split_hole_scope. *)
Definition split_hole_scope (Et : EC_term) : EC_term * EC_proc :=
  match pop_EC_scope Et with
  | (_, Ehol) => (Et, Ehol)
  | (Et_acc, Edeflam r Et_cur) => split_hole_scope_builder r Et_acc Et_cur (hole_depth_lt_wf Et_cur)
  | _ => (Ebag 0 0 Ehol, Ehol) (* Cannot reach here *)
  end.





Lemma inv_split_hole_scope_builder :
  forall Et_cur r Et_acc ACC,
    exists Et_outer r' Et_hs,
    split_hole_scope_builder r Et_acc Et_cur ACC = 
    (Et_outer, Edeflam r' Et_hs).
Proof.
  induction Et_cur using (well_founded_induction hole_depth_lt_wf).
  destruct Et_cur; destruct EP; intros; destruct ACC.
  - simpl. eexists; eauto.
  - apply (H Et). unfold hole_depth_lt; auto.
  - 
    unfold split_hole_scope_builder. fold split_hole_scope_builder.
    remember (Ebag m n (Epar EP P)) as x.
    destruct (pop_EC_scope x).
    admit.
Admitted.