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

From LEpic Require Import
  Contexts
  Syntax
  EvalContexts
  Semantics
  Preservation.

Import Renamings.
Import Stdlib.Relations.Relation_Operators.

Local Open Scope program_scope.
Local Open Scope bool_scope.



(* Renamings lemmas *)

Lemma wf_ren_shift :
forall m m' 
       (bf : ren m' m')
       (HWF : wf_ren bf),
  wf_ren (ren_shift m bf).
Proof.
  intros.
  unfold wf_ren in *.
  intros x; split; intros H.
  - unfold ren_shift, ctxt_app, ren_id.
    destruction.
    assert (x - m < m') by lia.
    specialize (HWF (x - m)); destruct HWF as [HWF1 HWF2].
    apply HWF1 in H0; try lia.
  - unfold ren_shift, ctxt_app, ren_id.
    destruction.
    assert (x - m >= m') by lia.
    specialize (HWF (x - m)); destruct HWF as [HWF1 HWF2].
    apply HWF2 in H0; try lia.
Qed.
    
Lemma bij_ren_shift :
forall m m' 
       (bf : ren m' m')
       (HWF : wf_ren bf)
       (HBF : bij_ren bf),
  bij_ren (ren_shift m bf).
Proof.
  intros. 
  destruct HBF as [x [Hx Hx']].
  unfold bij_ren.
  exists (ren_shift m x).
  split.
  - apply wf_ren_shift; assumption.
  - unfold ren_inverses, wf_ren in *.
    intros x0.
    specialize (Hx' (x0 - m)); destruct Hx' as [Hxbf1 Hxbf2].
    specialize (HWF (x0 - m)); specialize (Hx (x0 - m)).
    unfold ren_shift, ren_id, ctxt_app.
    split; intros; destruction.
    all: replace (m + bf (x0 - m) - m) with (bf (x0 - m)) by lia;
         replace (m + x (x0 - m) - m) with (x (x0 - m)) by lia.
    + assert (Hlt : x0 - m < m') by lia.
      destruct (Hxbf1 Hlt); lia.
    + assert (Hge : x0 - m >= m') by lia.
      destruct (Hxbf2 Hge); lia.
Defined.

Lemma bij_app_id_shift : 
  forall (n n' : nat) (br : ren n' n')
         (HWF : wf_ren br) (HBR : bij_ren br),
  (bij_app (ren_id n) br) = (ren_shift n br).
Proof.
  intros.
  unfold bij_app, ren_shift, ren_id, ctxt_app.
  apply functional_extensionality.
  intros x; destruction.
Qed.

Lemma bij_ren_inv_elt : 
  forall (m x : nat) (bf : ren m m) 
         (HWF : wf_ren bf) (HBF : bij_ren bf),
    x < m -> 
    bf (bij_inv bf HBF x) = x.
Proof.
  intros. 
  destruct HBF as [r_inv [HR HI]].
  simpl.
  destruct (HI x) as [HI1 _].
  apply HI1 in H.
  destruct H.
  auto.
Qed.

Lemma bij_bij_app : 
  forall (m n : nat) (bf : ren n n)
         (HWF : wf_ren bf) (HBF : bij_ren bf),
    bij_ren (bij_app (ren_id m) bf).
Proof. 
  intros.
  apply proj_bij_ren.
  apply (wf_bij_ren_app (ren_id m) bf).
  - apply wf_bij_ren_id.
  - exact (existT _ HWF HBF).
Defined.


(* aeq/seq lemmas *)

Import Renamings.

Lemma aeq_renaming_tpo : 
  (forall (m n : nat) (t : term),
      ws_term m n t ->
      forall  (bf : ren m m) (br : ren n n)
         (HWF : wf_ren bf) (HBF : bij_ren bf)
         (HWR : wf_ren br) (HBR : bij_ren br),
        aeq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)))
  /\
    (forall (m n : nat) (P : proc),
        ws_proc m n P ->
        forall (bf : ren m m) (br : ren n n)
          (HWF : wf_ren bf) (HBF : bij_ren bf)
          (HWR : wf_ren br) (HBR : bij_ren br),
          aeq_proc m n bf br P (rename_fvar_proc bf (rename_rvar_proc br P)))
  /\
    (forall (m n : nat) (o : oper),
        ws_oper m n o ->
        forall  (bf : ren m m) (br : ren n n)  
           (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
          aeq_oper m n bf br o (rename_fvar_oper bf (rename_rvar_oper br o))).
Proof.
  apply ws_tpo_ind; intros; simpl.
  - rewrite <- (bij_app_id_shift m' m bf HWF HBF).
    rewrite <- (bij_app_id_shift n' n br HWR HBR).
    eapply aeq_bag with (bf':=ren_id m')(br':=ren_id n');
      try apply wf_bij_ren_id.
    apply H.
    + apply wf_bij_app; auto using wf_ren_id.
    + apply bij_bij_app; auto.
    + apply wf_bij_app; auto using wf_ren_id.
    + apply bij_bij_app; auto.
  - eapply aeq_def; auto.
  - eapply aeq_app; auto.
  - eapply aeq_par; auto.
  - eapply aeq_req; auto.
  - eapply aeq_nul.
  - eapply aeq_emp; auto.
  - eapply aeq_tup; auto.
  - eapply aeq_bng; auto.
  - eapply aeq_lam; auto.
    rewrite <- (rename_rvar_id_term m 1 t WST) at 2.
    apply H; auto using wf_ren_id, bij_ren_id.
Qed.    

Lemma aeq_renaming_term :
forall (t : term),
forall (m n : nat)
  (HWS: ws_term m n t)
       (bf : ren m m) (br : ren n n)
       (HWF : wf_ren bf) (HBF : bij_ren bf)
       (HWR : wf_ren br) (HBR : bij_ren br),
        aeq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)).
Proof.
  intros. 
  apply aeq_renaming_tpo; auto.
Qed. 

Lemma aeq_renaming_proc :
forall (P : proc),
forall (m n : nat)
  (HWS: ws_proc m n P) 
       (bf : ren m m) (br : ren n n)
       (HWF : wf_ren bf) (HBF : bij_ren bf)
       (HWR : wf_ren br) (HBR : bij_ren br),
        aeq_proc m n bf br P (rename_fvar_proc bf (rename_rvar_proc br P)).
Proof.
  intros. 
  apply aeq_renaming_tpo; auto.
Qed.

Lemma aeq_renaming_oper :
forall (o : oper),
forall (m n : nat)
  (HWS: ws_oper m n o) 
       (bf : ren m m) (br : ren n n)
       (HWF : wf_ren bf) (HBF : bij_ren bf)
       (HWR : wf_ren br) (HBR : bij_ren br),
        aeq_oper m n bf br o (rename_fvar_oper bf (rename_rvar_oper br o)).
Proof.
  intros. 
  apply aeq_renaming_tpo; auto.
Qed.

Lemma tpo_seq_rename_fvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall m 
      (bf : ren m m)
      (HWF : wf_ren bf)
      (HBF : bij_ren bf),
      (rename_fvar_term bf t1) ≈t
      (rename_fvar_term bf t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall m
      (bf : ren m m)
      (HWF : wf_ren bf)
      (HBF : bij_ren bf),
      (rename_fvar_proc bf P1) ≈p
      (rename_fvar_proc bf P2)))   
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall m 
      (bf : ren m m)
      (HWF : wf_ren bf)
      (HBF : bij_ren bf),
      (rename_fvar_oper bf o1) ≈o
      (rename_fvar_oper bf o2))).
Proof.
  apply seq_tpo_ind; intros.
  - simpl. apply seq_bag. 
    specialize (H (m + m0) (ren_shift m bf)).
    assert (wf_ren (ren_shift m bf)) by (apply wf_ren_shift; assumption).
    assert (bij_ren (ren_shift m bf)) by (apply bij_ren_shift; assumption).
    specialize (H H0 X). assumption.
  - reflexivity.
  - specialize (H m bf HWF HBF). 
    symmetry; assumption.
  - specialize (H m bf HWF HBF). 
    specialize (H0 m bf HWF HBF). 
    specialize (Transitive_seq_proc (rename_fvar_proc bf P1) (rename_fvar_proc bf P2) (rename_fvar_proc bf P3));
    auto.
  - apply seq_par_comm.
  - apply seq_par_assoc1.
  - apply seq_par_assoc2.
  - simpl.
    specialize (H m bf HWF HBF). 
    specialize (H0 m bf HWF HBF).     
    apply seq_par_cong; try assumption.
  - simpl.
    specialize (H m bf HWF HBF).
    apply seq_def; assumption.
  - simpl. apply seq_req_comm.
  - reflexivity.
  - simpl. 
    specialize (H m bf HWF HBF).
    apply seq_lam; assumption.
Qed.

Lemma seq_rename_fvar_term : 
forall t1 t2,
  t1 ≈t t2 ->
  (forall m
    (bf : ren m m)
    (HWF : wf_ren bf)
    (HBF : bij_ren bf),
    (rename_fvar_term bf t1) ≈t
    (rename_fvar_term bf t2)).
Proof.
  apply tpo_seq_rename_fvar.
Qed.


Lemma tpo_seq_rename_rvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall n
      (br : ren n n)
      (HWR : wf_ren br)
      (HBR : bij_ren br),
      (rename_rvar_term br t1) ≈t
      (rename_rvar_term br t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall n
      (br : ren n n)
      (HWR : wf_ren br)
      (HBR : bij_ren br),
      (rename_rvar_proc br P1) ≈p
      (rename_rvar_proc br P2))) 
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall n
      (br : ren n n)
      (HWR : wf_ren br)
      (HBR : bij_ren br),
      (rename_rvar_oper br o1) ≈o
      (rename_rvar_oper br o2))).
Proof.
  apply seq_tpo_ind; intros.
  - apply seq_bag.  eapply H.
    apply wf_ren_shift. auto.
    apply bij_ren_shift; auto.
  - reflexivity.
  - specialize (H n br HWR HBR); firstorder.
  - specialize (H n br HWR HBR);
    specialize (H0 n br HWR HBR).
    specialize (Transitive_seq_proc (rename_rvar_proc br P1)
                                    (rename_rvar_proc br P2)
                                    (rename_rvar_proc br P3)).
    firstorder.
  - simpl. apply seq_par_comm.
  - simpl. apply seq_par_assoc1.
  - simpl. apply seq_par_assoc2.
  - simpl.
    specialize (H n br HWR HBR);
    specialize (H0 n br HWR HBR).
    apply seq_par_cong; try assumption.
  - simpl.    
    specialize (H n br HWR HBR).
    apply seq_def; assumption.
  - simpl. apply seq_req_comm.
  - auto.
  - simpl.
    apply seq_lam; auto.
Qed.

Lemma seq_rename_rvar_term : 
forall t1 t2,
  t1 ≈t t2 ->
  (forall n
    (br : ren n n)
    (HWR : wf_ren br)
    (HBR : bij_ren br),
    (rename_rvar_term br t1) ≈t
    (rename_rvar_term br t2)).
Proof.
  apply tpo_seq_rename_rvar.
Qed.

Lemma seq_renaming_term :
forall t1 t2,
  t1 ≈t t2 ->
  (forall m n
    (bf : ren m m)
    (br : ren n n)
    (HWF : wf_ren bf)
    (HBF : bij_ren bf)
    (HWR : wf_ren br)
    (HBR : bij_ren br),
    (rename_fvar_term bf (rename_rvar_term br t1)) ≈t
    (rename_fvar_term bf (rename_rvar_term br t2))).
Proof.
  intros.
  specialize (seq_rename_rvar_term t1 t2 H n br HWR HBR) as Hr.
  specialize (seq_rename_fvar_term (rename_rvar_term br t1) (rename_rvar_term br t2)
              Hr m bf HWF HBF) as Hf.
  assumption.
Qed.


(* Shifting a renaming that is the identity on scope [n] gives
   a renaming that is the identity on scope [k + n] *)
Lemma ren_shift_id_on :
  forall k n (r : ren n n),
    (forall x, x < n -> r x = x) ->
    forall x, x < k + n -> (ren_shift k r) x = x.
Proof.
  intros.
  unfold ren_shift, ctxt_app, ren_id.
  destruct (lt_dec x k); auto.
  rewrite H; lia.
Qed.

(* A renaming that is the identity on the variables in scope
   doesn't change well-scoped syntax *)
Lemma rename_rvar_id_on_tpo :
  (forall m n (t : term), ws_term m n t ->
    forall (r : ren n n), (forall x, x < n -> r x = x) ->
      rename_rvar_term r t = t)
  /\ (forall m n (P : proc), ws_proc m n P ->
    forall (r : ren n n), (forall x, x < n -> r x = x) ->
      rename_rvar_proc r P = P)
  /\ (forall m n (o : oper), ws_oper m n o ->
    forall (r : ren n n), (forall x, x < n -> r x = x) ->
      rename_rvar_oper r o = o).
Proof.
  apply ws_tpo_ind; intros; simpl.
  all: try solve [repeat match goal with
         | [ H : forall r, _ -> rename_rvar_oper r ?o = ?o |- _ ] => rewrite H by auto
         | [ H : forall r, _ -> rename_rvar_proc r ?P = ?P |- _ ] => rewrite H by auto
         | [ H : forall x, x < ?n -> ?r x = x, _ : ?y < ?n |- _ ] => rewrite (H y) by auto
         end; auto].
  (* Bag *)
  rewrite H; auto.
  apply ren_shift_id_on; auto.
Qed.

Lemma rename_fvar_id_on_tpo :
  (forall m n (t : term), ws_term m n t ->
    forall (r : ren m m), (forall x, x < m -> r x = x) ->
      rename_fvar_term r t = t)
  /\ (forall m n (P : proc), ws_proc m n P ->
    forall (r : ren m m), (forall x, x < m -> r x = x) ->
      rename_fvar_proc r P = P)
  /\ (forall m n (o : oper), ws_oper m n o ->
    forall (r : ren m m), (forall x, x < m -> r x = x) ->
      rename_fvar_oper r o = o).
Proof.
  apply ws_tpo_ind; intros; simpl.
  all: try solve [repeat match goal with
         | [ H : forall r, _ -> rename_fvar_oper r ?o = ?o |- _ ] => rewrite H by auto
         | [ H : forall r, _ -> rename_fvar_proc r ?P = ?P |- _ ] => rewrite H by auto
         | [ H : forall r, _ -> rename_fvar_term r ?t = ?t |- _ ] => rewrite H by auto
         | [ H : forall x, x < ?m -> ?r x = x, _ : ?y < ?m |- _ ] => rewrite (H y) by auto
         end; auto].
  (* Bag *)
  rewrite H; auto.
  apply ren_shift_id_on; auto.
Qed.

(* Composing a bijection with its inverse is the identity in scope *)
Lemma ren_compose_bij_inv_id_on :
  forall n (r : ren n n) (HBR : bij_ren r),
    forall x, x < n -> ren_compose r (bij_inv r HBR) x = x.
Proof.
  intros.
  destruct HBR as [r_inv [HWI HI]]; simpl.
  unfold ren_compose, compose.
  destruct (HI x) as [HI1 _]. apply HI1; auto.
Qed.

Lemma aeq_implies_seq: 
 (forall (m n : nat) (bf : ren m m) (br : ren n n) (t t' : term)
    (HT : aeq_term m n bf br t t'),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    exists (t'' : term), 
    (aeq_term m n bf br t t'') /\ 
    (t ≈t (rename_fvar_term (bij_inv bf HBF)
                            (rename_rvar_term (bij_inv br HBR) t''))))
  /\
 (forall (m n : nat) (bf : ren m m) (br : ren n n) (P P' : proc)
    (HP : aeq_proc m n bf br P P'),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    exists (P'' : proc), 
    (aeq_proc m n bf br P P'') /\ 
    (P ≈p (rename_fvar_proc (bij_inv bf HBF)
                            (rename_rvar_proc (bij_inv br HBR) P''))))
  /\
 (forall (m n : nat) (bf : ren m m) (br : ren n n) (o o' : oper)
    (Ho : aeq_oper m n bf br o o'),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    exists (o'' : oper), 
    (aeq_oper m n bf br o o'') /\ 
    (o ≈o (rename_fvar_oper (bij_inv bf HBF)
                           (rename_rvar_oper (bij_inv br HBR) o'')))).
Proof.
  (* Witness: rename by the bijections directly; renaming by the inverses
     then gives back exactly the original syntax. *)
  destruct aeq_ws_tpo as [WSt [WSp WSo]].
  destruct rename_rvar_id_on_tpo as [RRt [RRp RRo]].
  destruct rename_fvar_id_on_tpo as [RFt [RFp RFo]].
  repeat split; intros.
  - exists (rename_fvar_term bf (rename_rvar_term br t)); split.
    + apply aeq_renaming_term; eauto.
    + rewrite rename_rvar_fvar_commute_term.
      rewrite rename_fvar_compose_term, rename_rvar_term_compose.
      rewrite RRt with (m := m); eauto using ren_compose_bij_inv_id_on.
      rewrite RFt with (n := n); eauto using ren_compose_bij_inv_id_on.
      all: reflexivity.
  - exists (rename_fvar_proc bf (rename_rvar_proc br P)); split.
    + apply aeq_renaming_proc; eauto.
    + rewrite rename_rvar_fvar_commute_proc.
      rewrite rename_fvar_compose_proc, rename_rvar_proc_compose.
      rewrite RRp with (m := m); eauto using ren_compose_bij_inv_id_on.
      rewrite RFp with (n := n); eauto using ren_compose_bij_inv_id_on.
      all: reflexivity.
  - exists (rename_fvar_oper bf (rename_rvar_oper br o)); split.
    + apply aeq_renaming_oper; eauto.
    + rewrite rename_rvar_fvar_commute_oper.
      rewrite rename_fvar_compose_oper, rename_rvar_oper_compose.
      rewrite RRo with (m := m); eauto using ren_compose_bij_inv_id_on.
      rewrite RFo with (n := n); eauto using ren_compose_bij_inv_id_on.
      all: reflexivity.
Qed.


Lemma aeq_renaming_inv_tpo :
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (t u : term)
    (HT : aeq_term m n bf br t u),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    aeq_term m n (bij_inv bf HBF) (bij_inv br HBR) u t)
  /\
  (forall (m n :nat) (bf : ren m m) (br : ren n n) (P Q : proc)
    (HP : aeq_proc m n bf br P Q),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    aeq_proc m n (bij_inv bf HBF) (bij_inv br HBR) Q P)
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (o o' : oper)
    (Ho : aeq_oper m n bf br o o'),
    forall (HWF : wf_ren bf) (HBF : bij_ren bf)
           (HWR : wf_ren br) (HBR : bij_ren br),
    aeq_oper m n (bij_inv bf HBF) (bij_inv br HBR) o' o).
Proof.
  (* Follows from aeq_inv_tpo by bundling wf_ren and bij_ren into wf_bij_ren *)
  destruct aeq_inv_tpo as [Ht [Hp Ho]].
  repeat split; intros.
  - exact (Ht _ _ _ _ _ _ HT (existT _ HWF HBF) (existT _ HWR HBR)).
  - exact (Hp _ _ _ _ _ _ HP (existT _ HWF HBF) (existT _ HWR HBR)).
  - exact (Ho _ _ _ _ _ _ Ho0 (existT _ HWF HBF) (existT _ HWR HBR)).
Qed.


(* Alpha Equivalence *)
(* Definition aeq (m n : nat) (t1 t2 : term) :=
  exists t1', t1 ≈t t1' /\ t1' [t≡ ] t2.

(* aeq should be an equivalence relation *)
Lemma reflexive_aeq : 
  forall m n (x : term), ws_term m n x -> aeq m n x x.
Proof.
  intros. 
  unfold aeq.
  exists x.
  split.
  apply Reflexive_seq_term.
  apply neq_term_refl; assumption.
Qed.

#[global] Instance aeq_Symmetric (m n : nat) : Symmetric (aeq m n).
Proof.
  unfold Symmetric.
  intros x y Hxy.
  unfold aeq in *.
  destruct Hxy as [x0 [Hx0 Hx0y]]; symmetry in Hx0.
  destruct Hx0y.

  (* 
  specialize (aeq_renaming_term m n bf br x0 HWF HBF HWR HBR) as H'.
  specialize (seq_renaming_term x0 x Hx0 m n bf br HWF HBF HWR HBR) as H''.
  specialize (neq_term_intro m n x0 
              (rename_fvar_term bf (rename_rvar_term br x0))
              bf br HWF HBF HWR HBR H') as Hx0'.
  specialize (aeq_renaming_term m n bf br x HWF HBF HWR HBR) as Hx.
  specialize (neq_term_intro m n x
              (rename_fvar_term bf (rename_rvar_term br x))
              bf br HWF HBF HWR HBR Hx) as Hx'. 
  *)

Admitted.

(* Uses aeq_Symmetric. *)
#[global] Instance aeq_Transitive (m n : nat) : Transitive (aeq m n).
Proof.
  unfold Transitive.
  intros x y z Hxy Hyz. 
  inversion Hxy; inversion Hyz; subst.
  destruct H as [Hx0 Hx0y].
  destruct H0 as [Hx1 Hx1z].
  unfold aeq.
  assert (aeq m n x1 x0).
  { unfold aeq.
    symmetry in Hx1; symmetry in Hx0y. 
    exists y.
    split; try assumption. }
  assert (H' : aeq m n x1 x0) by (apply H).
  apply aeq_Symmetric in H'.
  destruct H as [x2 [Hx2 Hx2x0]].
  destruct H' as [x3 [Hx3 Hx3x1]].
  assert (x ≈t x3). 
  { specialize (Transitive_seq_term x x0 x3 Hx0 Hx3);
    firstorder. }
  assert (x3 [t≡ ] z).
  { specialize (Transitive_neq_term x3 x1 z Hx3x1 Hx1z);
    firstorder. }
  exists x3; split; try assumption.
Qed.
*)










(* Linear Opal is not Strongly Confluent.
    Counter-example:
    f <- \r. r <- ()
             ∅  
    f r
  *)
Lemma no_strong_confluence :
  ~ forall m n (t t1 t2: term)
    (HWF : wf_term m n t)
    (HS1 : step t t1)
    (HS2 : step t t2),
      (exists t1', exists t2', 
        (step t1 t1') /\
          (step t2 t2') /\
          neq_term t1' t2').
Proof.
  unfold not; intros.
  specialize H with 0 1
  (* Initial Term *)
      (bag 1 1 (par
        (app 0 1)
  (par  (def 0 (lam 
                (bag 0 0 (par
                  (def 0 emp)
                  nul
                ))))
        (def 0 (bng 0))
      )))
  (* First Step *)
      (bag 1 2 (par
  (par  (req 1 2)
  (par  (def 1 emp)
        nul      ))
  (par  (def 0 (lam 
                (bag 0 0 (par
                  (def 0 emp)
                  nul
                ))))
        (def 0 (bng 0))
      )))
  (* Second Step *)
      (bag 1 1 (par
        (def 0 (lam 
                (bag 0 0
                  (def 0 emp)
                )))
  (par  (app 0 1)
        (def 0 (bng 0))
      ))).

  destruct H.
  - repeat econstructor; eauto; solve_ctxt_eq.

  - econstructor; try reflexivity.
    remember (bag 0 0 (par (def 0 emp) nul)) as t.
    remember (par (def 0 (lam t))
                  (def 0 (bng 0)))
            as L.
    remember (Ebag 1 1 Ehol <=<[ (Epar Ehol L) ]) as Et_fun.
    replace (bag 1 1 (par (app 0 1) L)) 
        with (Et_fun <=[ app 0 1 ]) by (subst; auto).
    remember (shift_hs_by_term_vars t Et_fun) as Et_shifted.
    replace (bag 1 2 (par (par (req 1 2) (par (def 1 emp) nul)) L)) 
        with (Et_shifted <=[ par (req 1 2) (par (def 1 emp) nul) ]) by (subst; auto).
    subst; constructor.

  - remember (def 0 (lam (bag 0 0 (par (def 0 emp) nul)))) as P1.
    remember (app 0 1) as P2.
    remember (def 0 (bng 0)) as P3.
    eapply step_rule with (t1' := (bag 1 1 (par P1 (par P2 P3)))).
    + constructor.
      eapply seq_proc_trans.
      1: apply seq_par_assoc1.
      eapply seq_proc_trans.
      2: apply seq_par_assoc2.
      now apply seq_par_cong.
    + subst.
      remember (def 0 emp) as P.
      remember (par (app 0 1) (def 0 (bng 0))) as P'.
      remember (Ebag 1 1 (Epar (Edeflam 0 (Ebag 0 0 Ehol)) P')) as Et.
      replace (bag 1 1 (par (def 0 (lam (bag 0 0 (par P nul)))) P'))
          with (Et <=[ par P nul ]) by (subst; auto).
      replace (bag 1 1 (par (def 0 (lam (bag 0 0 P))) P'))
          with (Et <=[ P ]) by (subst; auto).
      subst; constructor.

  - admit.
Admitted.








(* Confluence *)
Lemma confluence :
  forall m n (t t1 t2: term)
    (HWF : wf_term m n t)
    (HS1 : step t t1)
    (HS2 : step t t2),
      (exists t1', exists t2', 
        (multi_step t1 t1') /\
          (multi_step t2 t2') /\
          neq_term t1' t2').

(*
  invert HS1 HS2.
  t = EtA <=[ PA ] /\ t = EtB <=[ PB ]
  t1 = Et1 <=[ P1 ]
  t2 = Et2 <=[ P2 ]

  EtA <=[ PA ]  -->  Et1 <=[ P1 ]
  EtB <=[ PB ]  -->  Et2 <=[ P2 ]
  case {}

  Et1 <=[ P1 ]  ?=  Et3 <=[ PB ]  -?->  EtC <=[ P2 ]
  Et2 <=[ P2 ]  ?=  Et4 <=[ PA ]  -?->  EtD <=[ P1 ]
  EtC <=[ P2 ]  ?=a  EtD <=[ P1 ]
*)


Proof.
  (* intros.
  inversion HS1; subst.
  inversion HS2; subst.
  inversion H0; inversion H2; subst.
  - destruct (Nat.eq_dec r r0).
    + subst.
      assert (m' = m'0 /\ n' = n'0 /\ P ≈p P0).
      { rewrite H in H1.
        apply seq_term_inv in H1.
        destruct H1 as [EQ1 [EQ2 HP]].
        subst.
        repeat split; auto.
        apply seq_proc_par_inv_l in HP.
        assumption. }
      destruct H3 as [EQ1 [EQ2 HP]].
      subst.
      exists m. exists n. left.
      unfold aeq.
      exists (bag m'0 n'0 P0).
      split.
      * apply seq_bag. assumption.
      * apply neq_term_refl.
        specialize (wf_ws_term m n G D t) as Ht.
        apply Ht in HWF; clear Ht.
        (* step and ws interact? w/o assumptions of wfdness. *)
        admit. (* TODO: get this from HWF somehow *)
    + admit. (* two cases, r = r0 -> no step, r <> r0 -> complementary steps *)
  - admit. (* deduce r <> r0 -> complementary step *)
  - admit.
  - admit. (* symmetric with case 2 *)
  - admit. (* two cases, r = r0 -> no step, analogous to 1.a, other case r <> r0 *)
  - admit. (* analogous to case 3 but with more renaming involved *)
  - admit. (* symmetric to case 3 *)
  - admit. (* symmetric to case 6 *)
  - admit. (* three subcases?
               if: r = r0 ->
                       if r' = r0' then no step
                       if r' <> r0' then two different calls to the same function
                   r <> r0 ->
                       two calls to different functions *) *)
Admitted.
