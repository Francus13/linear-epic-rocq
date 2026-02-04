From Stdlib Require Import
  Arith
  Logic.FunctionalExtensionality
  Lia
  Classes.RelationClasses
  Morphisms
  Program.Basics
  List
  Vectors.FinFun.

Import Relation_Definitions.

(* deBruijn indices *)
Definition var := nat.

(* Contexts ----------------------------------------------------------------- *)

Definition ctxt (n:nat) (X:Type) := var -> X.

Definition ctxt_eq {X} n (c d : ctxt n X) :=
  forall x, x < n -> c x = d x.

(*
  In general, we want to be able to [rewrite] when contexts are "equivalent",
  which isn't the same as Rocq's [=].
*)

Infix "≡[ n ]" := (ctxt_eq n) (at level 70).

#[global] Instance refl_ctxt_eq : forall X n, Reflexive (@ctxt_eq X n).
Proof.
  intros. repeat red.
  intros. unfold ctxt_eq in *.
  split; intros; auto.
Qed.

#[global] Instance sym_ctxt_eq : forall X n, Symmetric (@ctxt_eq X n).
Proof.
  intros. repeat red.
  intros. unfold ctxt_eq in *.
  rewrite H; tauto.
Qed.

#[global] Instance trans_ctxt_eq : forall X n, Transitive (@ctxt_eq X n).
Proof.
  intros. repeat red.
  intros. unfold ctxt_eq in *.
  rewrite <- H0; auto. 
Qed.

#[global] Instance Proper_ctxt_eq {X n} : Proper ((@ctxt_eq X n) ==> (@ctxt_eq X n) ==> iff) (@ctxt_eq X n).
Proof.
  repeat red.
  intros.
  split; intros.
  - eapply transitivity. symmetry. apply H. eapply transitivity. apply H1. apply H0.
  - eapply transitivity. apply H. eapply transitivity. apply H1. symmetry. apply H0.
Qed.    

Definition cons {X:Type} {n:nat} (x:X) (c : ctxt n X) : ctxt (S n) X :=
  fun y =>
    match y with
    | 0 => x
    | S y => c y
    end.

Import ProperNotations. 

#[global] Instance cons_Proper {X} {n} : Proper (eq ==> (@ctxt_eq X n) ==> (@ctxt_eq X (S n))) cons.
Proof.
  repeat red; intros.
  unfold ctxt_eq in H0.
  unfold cons.
  destruct x1; auto.
  rewrite H0; auto. lia.
Qed.


Definition tail {X} {n} (c : ctxt (S n) X) : ctxt n X :=
  fun x => c (S x).

#[global] Instance tail_Proper {X} {n} : Proper ((@ctxt_eq X (S n)) ==> (@ctxt_eq X n)) tail.
Proof.
  repeat red.
  intros.
  unfold ctxt_eq in H.
  unfold tail.
  assert ((S x0) < (S n)) by lia.
  rewrite H; auto.
Qed.  

Lemma tail_cons : forall  {X} {n} (l : ctxt (S n) X) (x:X),
    tail (cons x l) = l.
Proof.
  intros. reflexivity. 
Qed.

Lemma cons_tail : forall {X} {n} (l : ctxt (S n) X),
    l = cons (l 0) (tail l).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  destruct x; auto.
Qed.  

Definition ctxt_app {X} {n m : nat} (c : ctxt n X) (d : ctxt m X) :  ctxt (n + m) X :=
  fun x =>
    if Compare_dec.lt_dec x n then c x else d (x-n).

Infix "⊗" := (@ctxt_app _ _ _) (at level 50).

Lemma ctxt_app_null_l : forall {X} {n} (c : ctxt 0 X) (d : ctxt n X),
    c ⊗ d = d.
Proof.
  unfold ctxt_app.
  intros.
  apply functional_extensionality.
  intros x.
  destruct (lt_dec x 0).
  - inversion l.
  - replace x with (x - 0) at 2 by apply Nat.sub_0_r.
    reflexivity.
Qed.  

Lemma ctxt_app_l : forall {X} {n m} (c : ctxt n X) (d : ctxt m X),
    (c ⊗ d) ≡[n] c.
Proof.
  unfold ctxt_app, ctxt_eq.
  intros.
  destruct (lt_dec x n).
  - reflexivity.
  - contradiction.
Qed.  

Lemma ctxt_app_r : forall {X} {n m} (c : ctxt n X) (d : ctxt m X),
    forall (x:nat), (n <= x) -> 
    (c ⊗ d) x = d (x - n).
Proof.
  unfold ctxt_app.
  intros.
  destruct (lt_dec x n).
  - lia.
  - reflexivity.
Qed.  


Lemma ctxt_app_assoc : forall {X} {n m l} (c : ctxt n X) (d : ctxt m X) (e : ctxt l X),
    c ⊗ (d ⊗ e) = (c ⊗ d) ⊗ e.
Proof.
  Set Printing All.
  intros.
  unfold ctxt_app.
  apply functional_extensionality.
  intros.
  destruct (lt_dec x n).
  - destruct (lt_dec x (n + m)).
    + reflexivity.
    + lia.
  - destruct (lt_dec (x - n) m).
    + destruct (lt_dec x (n + m)).
      * reflexivity.
      * lia.
    + destruct (lt_dec x (n + m)).
      * lia.
      * replace (x - (n + m)) with (x - n - m) by lia.
        reflexivity.
Qed.        

#[global] Instance Proper_ctxt_app {X n m} : Proper ((@ctxt_eq X n) ==> (@ctxt_eq X m) ==> (@ctxt_eq X (n +m))) (@ctxt_app X n m).
Proof.
  repeat red.
  unfold ctxt_eq, ctxt_app; intros.
  destruct (lt_dec x1 n); auto.
  assert ((x1 - n) < m) by lia.
  auto.
Qed.



(* Context append acts like a product with two "projections". *) 
Definition ctxt_trim {X:Type} (m n : nat) (c : ctxt (m + n) X) : ctxt m X := c.

#[global] Instance Proper_ctxt_trim {X m n} : Proper ((@ctxt_eq X (m + n)) ==> (@ctxt_eq X m)) (@ctxt_trim X m n).
Proof.
  repeat red.
  intros.
  unfold ctxt_eq in H.
  unfold ctxt_trim.
  rewrite H; auto. lia.
Qed.  

Definition ctxt_retract {X:Type} (m n : nat) (c : ctxt (m + n) X ): ctxt n X :=
  fun x => c (m + x).

#[global] Instance Proper_ctxt_retract {X m n} : Proper ((@ctxt_eq X (m + n)) ==> (@ctxt_eq X n)) (@ctxt_retract X m n).
Proof.
  repeat red.
  intros.
  unfold ctxt_eq in H.
  unfold ctxt_retract.
  rewrite H; auto.
  lia.
Qed.  

Lemma ctxt_app_trim_retract : forall m n X (c : ctxt (m + n) X),
    c = (ctxt_trim m n c) ⊗ (ctxt_retract m n c).
Proof.
  intros.
  unfold ctxt_app, ctxt_trim, ctxt_retract.
  apply functional_extensionality.
  intros x.
  destruct (lt_dec x m); auto.
  assert (m + (x - m) = x) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma ctxt_retract_app : forall m n X (c : ctxt m X) (d : ctxt n X),
    ctxt_retract m n (c ⊗ d) = d.
Proof.
  intros.
  unfold ctxt_app, ctxt_retract.
  apply functional_extensionality.
  intros x.
  destruct (lt_dec (m + x) m).
  - lia.
  - assert (m + x - m = x) by lia.
    rewrite H.
    reflexivity.
Qed.

Lemma ctxt_trim_app : forall m n X (c : ctxt m X) (d : ctxt n X),
    ctxt_trim m n (c ⊗ d) ≡[m] c.
Proof.
  unfold ctxt_app, ctxt_trim, ctxt_eq.
  intros.
  destruct (lt_dec x m).
  - reflexivity.
  - lia.
Qed.

Lemma ctxt_retract_1_is_tail :
  forall X n (c : ctxt (1 + n) X),
    tail c = ctxt_retract 1 n c.
Proof.
  intros.
  reflexivity.
Qed.
  

(* Linear contexts ---------------------------------------------------------- *)

(* Theory of "linear" contexts that map variables to their usage information. *)

(* The following definitions are about contexts of "usage" information as found in linear type systems. *)
Definition lctxt (n:nat) := ctxt n nat.

Definition sum {n} (c : lctxt n) (d : lctxt n) : lctxt n :=
  fun x => (c x) + (d x).

#[global] Instance Proper_sum {n} : Proper ((@ctxt_eq nat n) ==> (@ctxt_eq nat n) ==> (@ctxt_eq nat n)) (@sum n).
Proof.
  repeat red.
  unfold ctxt_eq, sum; intros.
  auto.
Qed.  
  
Infix "⨥" := (@sum _) (at level 50).

Lemma sum_ctxt_eq_inv : forall n (c1 c2 d : lctxt n),
    (c1 ⨥ c2) ≡[n] d -> exists d1 d2, d = (d1 ⨥ d2) /\ (d1 ≡[n] c1) /\ (d2 ≡[n] c2).
Proof.
  unfold sum, ctxt_eq.
  intros.
  exists (fun x => if lt_dec x n then (c1 x) else 0).
  exists (fun x => if lt_dec x n then (c2 x) else d x).
  repeat split.
  - apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    rewrite H; auto.
    lia.
  - intros.
    destruct (lt_dec x n); auto.
    lia.
  - intros.
    destruct (lt_dec x n); auto.
    lia.
Qed.    

Definition flat_ctxt i n : lctxt n := fun (x:nat) => i. 
Definition zero n : lctxt n := flat_ctxt 0 n.

Lemma flat_scons : forall i n, 
    (flat_ctxt i (S n)) = (@cons _ n i (flat_ctxt i n)).
Proof.
  intros i n.
  apply functional_extensionality.
  intros x.
  unfold cons.
  destruct x; auto.
Qed.  

Lemma flat_tail : forall i n, 
    (@tail _ n (flat_ctxt i (S n))) = flat_ctxt i n.
Proof.
  intros i n.
  apply functional_extensionality.
  intros x.
  unfold tail. reflexivity.
Qed.  

Lemma sum_flat_r : forall {n} i (c : lctxt n),
    c ⨥ (flat_ctxt i n) = fun (x:nat) => (c x) + i.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold flat_ctxt. lia.
Qed.

Lemma sum_flat_l : forall {n} i (c : lctxt n),
    (flat_ctxt i n) ⨥ c = fun (x:nat) => (c x) + i.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold flat_ctxt. lia.
Qed.

Lemma zero_scons : forall n, (zero (S n)) = (@cons _ n 0 (zero n)).
Proof. exact (flat_scons 0). Qed. 
Lemma zero_tail : forall n, (@tail _ n (zero (S n))) = zero n.
Proof. exact (flat_tail 0). Qed. 
Lemma sum_zero_r : forall {n} (c : lctxt n),
    c ⨥ (zero n) = c.
Proof. intros. apply functional_extensionality.
  intros. unfold zero. rewrite (sum_flat_r 0 c). lia. Qed.
Lemma sum_zero_l : forall {n} (c : lctxt n),
    (zero n) ⨥ c = c.
Proof. intros. apply functional_extensionality.
  intros. unfold zero. rewrite (sum_flat_l 0 c). lia. Qed. 

Lemma sum_assoc : forall {n} (c : lctxt n) (d : lctxt n) (e : lctxt n),
    c ⨥ (d ⨥ e) = (c ⨥ d) ⨥ e.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. lia.
Qed.

Lemma sum_commutative : forall {n} (c : lctxt n) (d : lctxt n),
    c ⨥ d = d ⨥ c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. lia.
Qed.

Example example_ctxt_eq :
  forall n (c1 c2 c3 : lctxt n),
    c1 ⨥ c2 ≡[n] c3 ->
    c1 ⨥ c1 ⨥ c2 ⨥ c2 ≡[n] c3 ⨥ c3.
Proof.
  intros.
  rewrite <- sum_assoc.
  rewrite <- sum_assoc.
  rewrite (@sum_assoc _ c1 c2 c2).
  rewrite H.
  rewrite (@sum_commutative _ c3 c2).
  rewrite sum_assoc.
  rewrite H.
  reflexivity.
Qed.  

(*  [delta x c] is the context that maps x to c and everything else to 0 *)

Definition delta (n:nat) (x:var) (c : nat) : lctxt n :=
  fun y => if lt_dec x n then if (Nat.eq_dec x y) then c else 0 else 0.
      
Notation "n [ x ↦ c ]" := (delta n x c).

Lemma delta_id : forall (n:nat) (x : var) (c:nat),
    x < n ->
    n[x ↦ c] x = c.
Proof.
  intros.
  unfold delta.
  destruct (lt_dec x n); try lia.
  destruct (Nat.eq_dec x x); auto.
  contradiction.
Qed.

Lemma delta_neq : forall n (x y : var) c,
    x <> y ->
    n[x ↦ c] y = 0.
Proof.
  intros.
  unfold delta.
  destruct (lt_dec x n); auto.
  destruct (Nat.eq_dec x y); auto.
  contradiction.
Qed.  
  
Lemma delta_c_inv : forall n (x y : var) c ,
    y < n ->
    c <> 0 ->
    n[x ↦ c] y = c -> x = y.
Proof.
  intros.
  unfold delta in H1.
  destruct (lt_dec x n).
  destruct (Nat.eq_dec x y); auto.
  lia.
  lia.
Qed.

Lemma delta_0_inv : forall n (x y : var) c ,
    x < n ->
    n[x ↦ c] y = 0  -> (c = 0 \/ x <> y).
Proof.
  intros.
  destruct c eqn:HC. left; auto.
  right. intros Heq. subst. rewrite delta_id in H0.
  discriminate.  assumption.
Qed.

Lemma delta_sum : forall n (x : var) c1 c2 ,
    n[x ↦ c1] ⨥ n[x ↦ c2] = n[x ↦ (c1 + c2)].
Proof.
  unfold delta. unfold sum.
  intros.
  apply functional_extensionality.
  intros.
  destruct (lt_dec x n); auto.
  destruct (Nat.eq_dec x x0); auto.
Qed.

Definition one n (x : var) : lctxt n := n[x ↦ 1].


Lemma delta_sum_ctxt_eq_inv : forall n x y (c d : lctxt n),
    (n[x↦y] ⨥ c) ≡[n] d -> exists d', d = (n[x↦y] ⨥ d') /\ (d' ≡[n] c).
Proof.
  unfold delta, sum, ctxt_eq.
  intros.
  exists (fun z => if lt_dec x n then if Nat.eq_dec x z then (d z) - y else d z else d z).
  split.
  - apply functional_extensionality.
    intros x0.
    destruct (lt_dec x n); auto.
    destruct (Nat.eq_dec x x0); auto.
    subst.
    apply H in l.
    destruct (Nat.eq_dec x0 x0); lia.
  - intros x0 HX0.
    destruct (lt_dec x n).
    + apply H in HX0.
      destruct (Nat.eq_dec x x0); auto.
      lia.
    + apply H in HX0.
      lia.
Qed.      


Lemma delta_ctxt_eq_inv : forall n x y (c : lctxt n),
    (n[x ↦ y] ≡[n] c) -> exists c', c = (n[x ↦ y] ⨥ c') /\ (c' ≡[n] (zero n)).
Proof.
  intros.
  rewrite <- (@sum_zero_r _ (n[x ↦ y])) in H.
  apply delta_sum_ctxt_eq_inv in H.
  apply H.
Qed.  

Definition SUM {n} (l : list (lctxt n)) : lctxt n :=
  List.fold_right sum (zero n) l.

Lemma SUM_app : forall n (l1 l2 : list (lctxt n)),
    SUM (l1 ++ l2) = (SUM l1) ⨥ (SUM l2).
Proof.
  induction l1; auto.
  intros.
  simpl.
  rewrite IHl1.
  rewrite sum_assoc.
  reflexivity.
Qed.

Lemma lctxt_sum : forall n (x : var) (D1 D2 : lctxt n),
    (D1 ⨥ D2) x = (D1 x) + (D2 x).
Proof.
  intros. reflexivity.
Qed.

(* Renaming Relations ------------------------------------------------------- *)

Module Renamings.

  Definition ren (n m : nat) := ctxt n var.

  (* Note: to make renamings more "canonical" we force them to map all variables
     "out of scope" to m (an illegal) variable in the range.  This will
     allow us to prove more equalities (of, e.g. delta) later one.

     This will force us to do "dynamic scope checks" inside the renaming functions.
  *)
  Definition wf_ren {n m:nat} (r : ren n m) : Prop :=
    forall x, (x < n -> (r x) < m) /\ (~(x < n) -> (r x) = m).

  Definition ren_id (n : nat) : ren n n :=
    fun (x:var) =>
      if (lt_dec x n) then x else n.

  Lemma ren_id_id :
    forall (n : nat) x,
      x < n ->
      (ren_id n) x = x.
  Proof.
    intros.
    unfold ren_id.
    destruct (lt_dec x n); auto.
    contradiction.
  Qed.

  (* Renaming by the identity does nothing. *)

Lemma map_ren_id :
  forall (l : list nat)
    (n : nat)
    (HRS : Forall (fun x : nat => x < n) l),
    map (ren_id n) l = l.
Proof.
  induction l; intros; simpl.
  (* Nil *)
  - reflexivity.
  (* Cons *)
  - inversion HRS; subst.
    rewrite IHl; auto.
    unfold ren_id.
    destruct (lt_dec a n); auto.
  lia.
Qed.  



  Definition ren_shift {n m:nat} (k:nat) (r : ren n m) : ren (k + n) (k + m) :=
    ctxt_app (ren_id k) (fun x => k + (r x)).

  Lemma wf_ren_shift : forall {n m} k (r : ren n m),
      wf_ren r ->
      wf_ren (ren_shift k r).
  Proof.
    unfold wf_ren, ren_shift, ctxt_app, ren_id.
    intros.
    destruct (lt_dec x k).
    - split; lia.
    - split; intros.
      + assert (x - k < n) by lia.
        apply H in H1.
        lia.
      + assert (~ (x - k) < n) by lia.
        apply H in H1.
        lia.
  Qed.

  Lemma ren_shift_id : forall {n} k,
      ren_shift k (ren_id n) = ren_id (k + n).
  Proof.
    unfold ren_shift, ren_id, ctxt_app.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x k).
    - destruct (lt_dec x (k + n)).
      + reflexivity.
      + lia.
    - destruct (lt_dec (x - k) n);
      destruct (lt_dec x (k + n)); lia.
  Qed.

  Definition ren_compose {n m X} (r : ren n m) (c : ctxt m X) : ctxt n X :=
    compose c r.

  Lemma ren_compose_correct : 
    forall {n m X} (r : ren n m) (c : ctxt m X) (x : nat),
    (c (r x)) = (ren_compose r c) x.
  Proof. auto. Qed.


  #[global] Instance Proper_ren_compose {n m X} (r : ren n m) (HR : wf_ren r) : Proper ((@ctxt_eq X m) ==> (@ctxt_eq X n)) (ren_compose r).
  Proof.
    repeat red.
    unfold ren_compose, compose, ctxt_eq.
    intros.
    subst.
    rewrite H; auto.
    unfold wf_ren in HR.
    apply HR. assumption.
  Qed.    
  
  (* Our insistance that renamings map to m outside their scope means this
     equality holds only for in-scope variables. *)
  Lemma ren_compose_id_l : forall {n X} (c : ctxt n X),
      (ren_compose (ren_id n) c) ≡[n] c.
  Proof.
    unfold ren_compose, compose, ren_id, ctxt_eq.
    intros.
    destruct (lt_dec x n); auto.
    contradiction.
  Qed.

  Lemma ren_compose_id_r : forall {n m} (r : ren n m),
      wf_ren r ->
      ren_compose r (ren_id m) = r.
  Proof.
    unfold wf_ren, ren_compose, compose, ren_id.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec (r x) m); auto.
    destruct (lt_dec x n).
    + assert (r x < m). { apply H. assumption. } contradiction.
    + symmetry. apply H. assumption.
  Qed.
  
  Lemma wf_ren_compose :
    forall {n m l} (r1 : ren n m) (r2 : ren m l),
      wf_ren r1 ->
      wf_ren r2 ->
      @wf_ren n l (ren_compose r1 r2).
  Proof.
    unfold wf_ren, ren_compose, compose.
    intros.
    split; intros.
    - eapply H0. eapply H. assumption.
    - apply H in H1.
      rewrite H1.
      apply H0. lia.
  Qed.

  Lemma ren_compose_shift : forall {n m l} k (r1 : ren n m) (r2 : ren m l),
      (ren_compose (ren_shift k r1) (ren_shift k r2)) =
        (@ren_shift n l k (ren_compose r1 r2)).
  Proof.
    intros.
    unfold ren_compose, compose, ren_shift, ren_id, ctxt_app.
    apply functional_extensionality.
    intros.
    destruct (lt_dec x k).
    - destruct (lt_dec x k); lia.
    - destruct (lt_dec (k + r1 (x - k)) k).
      lia.
      remember (r1 (x - k)) as X.
      assert (k + X - k = X) by lia.
      rewrite H.
      reflexivity.
  Qed.

  Lemma flat_ctxt_ren_compose_identity : forall {n m} x (r : ren n m),
      (ren_compose r (flat_ctxt x m)) = (flat_ctxt x m).
  Proof. auto using functional_extensionality. Qed.
  
  (* bijections *)

  Lemma wf_ren_bFun : forall {n} (r : ren n n),
      wf_ren r -> bFun n r.
  Proof.
    intros. unfold bFun.  unfold wf_ren in H.
    apply H.
  Qed.    
  
  Definition injective_ren {n} (r : ren n n) :=
    bInjective n r.

  Definition surjective_ren {n} (r : ren n n) :=
    bSurjective n r.

  Definition ren_inverses {n} (r r_inv : ren n n) :=
    forall x, x < n -> r_inv (r x) = x /\ r (r_inv x) = x.

  Lemma ren_inverses_comm : forall {n} (r r_inv : ren n n),
      ren_inverses r r_inv ->
      ren_inverses r_inv r.
  Proof.
    unfold ren_inverses.
    intros.
    split; apply H; auto.
  Qed.
  
  Lemma ren_inverses_exist : forall {n} (r : ren n n),
      wf_ren r ->
      surjective_ren r ->
      exists r_inv, wf_ren r_inv /\ ren_inverses r r_inv.
  Proof.
    unfold surjective_ren.
    intros.
    assert (bFun n r). apply wf_ren_bFun; auto.
    destruct (bSurjective_bBijective H1 H0) as [r_inv [HR HI]].
    exists (fun x => if lt_dec x n then r_inv x else n).
    split.
    - unfold wf_ren. intros.
      destruct (lt_dec x n); intros.
      + split; intros. apply HR. assumption.
        contradiction.
      + split; intros. contradiction. reflexivity.
    - unfold ren_inverses.
      intros.
      destruct (lt_dec (r x) n).
      + destruct (lt_dec x n).
        * apply HI. assumption.
        * contradiction.
      + destruct (lt_dec x n).
        * assert (r x < n). apply H1. assumption.
          contradiction.
        * contradiction.
  Qed.
  
  Definition bij_ren {n} (r : ren n n) :=
    { r_inv : ren n n &  wf_ren r_inv /\ ren_inverses r r_inv }.

  (* FRAN: I have not propogated this through this file, only this Renamings module. *)
  (* Bundles wf_ren and bij_ren in wf_bij_ren *)
  Definition wf_bij_ren {n} (r : ren n n) :=
    {HWB: wf_ren r & bij_ren r}.
    
  Definition proj_wf_ren {n r} (HWB : @wf_bij_ren n r) : wf_ren r :=
    match HWB with existT _ HWF _ => HWF end.
  Definition proj_bij_ren {n r} (HWB : @wf_bij_ren n r) : bij_ren r :=
    match HWB with existT _ _ HBJ => HBJ end.

  Definition prod_wf_ren_bij_ren {n r} : Type := (@wf_ren n n r) * (@bij_ren n r).
  Definition pair_wf_ren_bij_ren {n r} (HWFBJ : prod_wf_ren_bij_ren) : @wf_bij_ren n r :=
    match HWFBJ with (HWF, HBJ) => existT _ HWF HBJ end.

  Coercion proj_wf_ren : wf_bij_ren >-> wf_ren.
  Coercion proj_bij_ren : wf_bij_ren >-> bij_ren.
  Coercion pair_wf_ren_bij_ren : prod_wf_ren_bij_ren >-> wf_bij_ren.

(* FRAN: Is there a way to take a naming pattern as optional parameter? *)
  Ltac dest_wf_bij_ren :=
    repeat match goal with
    | [ H: context[wf_bij_ren ?R] |- _ ] => destruct H
    end.

  Lemma wf_ren_id : forall {n}, wf_ren (ren_id n).
  Proof. 
    unfold wf_ren, ren_id. intros.
    destruct (lt_dec x n); split; tauto.
  Defined.

  Lemma bij_ren_id : forall {n}, bij_ren (ren_id n).
  Proof. 
    unfold bij_ren, ren_id, wf_ren, ren_inverses; intros.
    exists (ren_id n).
    unfold ren_id.
    split; intros; split; intros.
    - destruct (lt_dec x n); auto.
      contradiction.
    - destruct (lt_dec x n); auto.
      contradiction.
    - destruct (lt_dec x n); auto.
      destruct (lt_dec x n); auto. contradiction.
      contradiction.
    - destruct (lt_dec x n); auto.
      destruct (lt_dec x n); auto. contradiction.
      contradiction.
  Defined.

  Lemma wf_bij_ren_id : forall {n}, wf_bij_ren (ren_id n).
  Proof. split. apply wf_ren_id. apply bij_ren_id. Defined.

  Definition bij_app {n m} (r1 : ren n n) (r2 : ren m m) : ren (n + m) (n + m) :=
    ctxt_app r1 (fun x => n + (r2 x)).

  Lemma wf_bij_app : forall {n m} (r1 : ren n n) (r2 : ren m m),
      wf_ren r1 ->
      wf_ren r2 -> 
      wf_ren (bij_app r1 r2).
  Proof.
    unfold wf_ren, bij_app, ctxt_app.
    intros.
    destruct (lt_dec x n).
    - split.
      + apply H in l. lia.
      + intros.
        lia.
    - split.
      + intros. 
        assert (x - n < m) by lia.
        apply H0 in H2.
        lia.
      + intros.
        assert (~ (x - n < m)). lia.
        assert (r2 (x - n) = m). apply H0.  assumption.
        rewrite H3.
        reflexivity.
  Qed.
    

  Lemma wf_bij_ren_app :
    forall {n m} (r1 : ren n n) (r2 : ren m m)
      (HWB1 : wf_bij_ren r1)
      (HWB2 : wf_bij_ren r2),
      @wf_bij_ren (n + m) (bij_app r1 r2).
  Proof.
    intros.
    unfold wf_bij_ren, bij_ren.
    destruct HWB1 as [HWF1 [r1_inv [HR1 HI1]]].
    destruct HWB2 as [HWF2 [r2_inv [HR2 HI2]]].
    split.
    1: apply wf_bij_app; auto.
    unfold bij_app, ctxt_app.
    exists (bij_app r1_inv r2_inv).
    split.
    - apply wf_bij_app; auto.
    - unfold ren_inverses.
      intros.
      unfold bij_app, ctxt_app.
      split.
      + destruct (lt_dec x n).
        * destruct (lt_dec (r1 x) n).
          apply HI1. assumption.
          assert (r1 x < n).
          apply HWF1. assumption.
          contradiction.
        * destruct (lt_dec (n + r2 (x - n)) n).
          lia.
          assert (n + (r2 (x - n)) - n = r2 (x - n)) by lia.
          rewrite H0.
          assert (x - n < m) by lia.
          assert (r2_inv (r2 (x - n)) = x - n).
          { apply HI2. assumption. }
          rewrite H2.
          lia.
      + destruct (lt_dec x n).
        * destruct (lt_dec (r1_inv x) n).
          apply HI1. assumption.
          assert (r1_inv x < n).
          { apply HR1. assumption. }
          lia.
        * destruct (lt_dec (n + r2_inv (x -n)) n).
          lia.
          assert (n + r2_inv (x - n) - n = r2_inv (x - n)) by lia.
          rewrite H0.
          assert (x - n < m) by lia.
          assert (r2(r2_inv (x - n)) = (x -n )).
          { apply HI2. assumption. }
          rewrite H2. lia.
  Defined.

  Lemma bij_app_id : forall {n m},
      bij_app (ren_id n) (ren_id m) = ren_id (n + m).
  Proof.
    unfold bij_app, ctxt_app,  ren_id.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n); try lia.
    - destruct (lt_dec x (n + m)); try lia.
    - destruct (lt_dec x (n + m)); destruct (lt_dec (x - n) m); try lia.
  Qed.
  

  Definition bij_inv {n} (r : ren n n) (H : bij_ren r) : ren n n :=
    let (r_inv, _) := H in r_inv.

  Lemma bij_inv_id : forall {n},
      bij_inv (ren_id n) (wf_bij_ren_id) = ren_id n.
  Proof. auto. Qed.

  Lemma bij_inv_wf : forall {n} (r : ren n n)
      (BR : bij_ren r),
      wf_ren (bij_inv r BR).
  Proof. intros. destruct BR as [r_inv [HBR HI]]; auto. Qed.

  Lemma bij_inv_bij :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r),
      bij_ren (bij_inv r HWB).
  Proof.
    intros. destruct HWB as [HWF [r_inv [HBR HI]]]; simpl.
    exists r. split; auto using ren_inverses_comm.
  Qed.

  Lemma bij_inv_wf_bij :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r),
      wf_bij_ren (bij_inv r HWB).
  Proof. split; auto using bij_inv_wf, bij_inv_bij. Qed.


  Lemma bij_inv_bij_inv_eq :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r)
      (HBJI : bij_ren (bij_inv r HWB)),
      (bij_inv (bij_inv r HWB) HBJI) = r.
  Proof. intros.
    destruct HWB as [HWF [r_inv [WRI BRI]]]; simpl in *.
    destruct HBJI as [r' [WR' BR']]; simpl in *.
    apply functional_extensionality. intros x.
    destruct (lt_dec x n).
    - unfold ren_inverses in *.
      assert (r x < n). { apply HWF; auto. }
      assert (r' (r_inv (r x)) = r x). { apply BR'. assumption. }
      rewrite <- H0.
      assert (r_inv (r x ) = x). {  apply BRI.  assumption. }
      rewrite H1.
      reflexivity.
    - assert (r' x = n). { apply WR'; auto. }
      assert (r x = n). { apply HWF; auto. }
      rewrite H. rewrite H0. reflexivity.
  Qed.                               
  
  Lemma bij_inv_app :
    forall {n m}
      (r1 : ren n n) (r2 : ren m m)
      (HWB1 : wf_bij_ren r1) (HWB2 : wf_bij_ren r2),
      bij_inv (bij_app r1 r2) (wf_bij_ren_app r1 r2 HWB1 HWB2) =
        bij_app (bij_inv r1 HWB1) (bij_inv r2 HWB2).
  Proof. intros.
    destruct HWB1 as [HWF1 [r1_inv [HR1 HI1]]].
    destruct HWB2 as [HWF2 [r2_inv [HR2 HI2]]].
    reflexivity.
  Qed.                  

  Lemma bij_ren_inv :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r),
      (ren_compose (bij_inv r HWB) r) = (ren_id n).
  Proof. intros.
    destruct HWB as [HWF [r_inv [HR HI]]]; simpl.
    apply functional_extensionality. intros.
    unfold ren_compose, compose, ren_id.
    destruct (lt_dec x n).
    - apply HI. assumption.
    - assert (r_inv x = n). { apply HR. assumption. }
      rewrite H. apply HWF. lia.
  Qed.

  Lemma bij_ren_inv_elt :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r) x,
      x < n ->
      x = ((bij_inv r HWB) (r x)).
  Proof. intros.
    destruct HWB as [HWF [r_inv [HR HI]]]; simpl.
    apply HI in H. destruct H.
    symmetry; auto.
  Qed.
  
  Lemma bij_ren_elt : forall {n} (r : ren n n),
      bij_ren r -> forall x, x < n -> exists y, y < n /\ x = r y.
  Proof.
    unfold bij_ren, wf_ren, ren_inverses.
    intros.
    destruct X as [r_inv [HWF HE]].
    exists (r_inv x).
    split.
    - apply HWF. assumption.
    - symmetry. apply HE. assumption.
  Qed.

  Lemma bij_ren_compose :
    forall {n} (r1 : ren n n) (r2 : ren n n)
      (HWB1 : wf_bij_ren r1) (HBJ2 : bij_ren r2),
      bij_ren (ren_compose r1 r2).
  Proof.
    unfold bij_ren, ren_inverses, ren_compose. intros.
    destruct HWB1 as [HWF1 [r1_inv [HWF1' HEQ1]]].
    destruct HBJ2 as [r2_inv [HWF2' HEQ2]].
    exists (ren_compose r2_inv r1_inv).
    split.
    - apply wf_ren_compose; auto.
    - split.
      + unfold ren_compose, compose.
        assert ((r1 x) < n). { apply HWF1. auto. }
        destruct (HEQ2 (r1 x) H0).
        rewrite H1.
        destruct (HEQ1 x H).
        rewrite H3. reflexivity.
      + unfold ren_compose, compose.
        assert ((r2_inv x) < n). { apply HWF2'.  auto. } 
        destruct (HEQ1 (r2_inv x) H0).
        rewrite H2.
        destruct (HEQ2 x H).
        rewrite H4.
        reflexivity.
  Defined.


Lemma wf_bij_ren_compose :
  forall {n} (r1 : ren n n) (r2 : ren n n)
    (HWB1 : wf_bij_ren r1) (HWB2 : wf_bij_ren r2),
    wf_bij_ren (ren_compose r1 r2).
Proof.
  intros; remember HWB1 as HWB1_copy; split;
  destruct HWB1; destruct HWB2; auto using wf_ren_compose, bij_ren_compose.
Qed.

Lemma compose_wf_bij_ren_ctxt_preservation :
  forall {X} (P : X -> Prop), 
    forall {n} (c : ctxt n X) (r : ren n n) (HWF : wf_ren r),
        (forall x, x < n -> P (c x)) -> 
        (forall x, x < n ->  P (ren_compose r c x)).
Proof.
  intros. unfold ren_compose, compose. apply (H (r x)).
  unfold wf_ren in HWF. destruct (HWF x). auto.
Qed.

  Lemma wf_bij_ren_app_compose :
    forall {n m} (r11 r12 : ren n n) (r21 r22 : ren m m)
      (HWB11 : wf_bij_ren r11) (HWB12 : wf_bij_ren r12)
      (HWB21 : wf_bij_ren r21) (HWB22 : wf_bij_ren r22),
      ren_compose (bij_app r11 r21) (bij_app r12 r22) =
        bij_app (ren_compose r11 r12) (ren_compose r21 r22).
  Proof.
    intros.
    destruct HWB11 as [HWF11 [r11_inv [HR11 HI11]]].
    destruct HWB12 as [HWF12 [r12_inv [HR12 HI12]]].
    destruct HWB21 as [HWF21 [r21_inv [HR21 HI21]]].
    destruct HWB22 as [HWF22 [r22_inv [HR22 HI22]]].
    unfold ren_compose.
    unfold bij_app.
    unfold ctxt_app, compose.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    - destruct (lt_dec (r11 x) n).
      + reflexivity.
      + assert (r11 x < n). { apply HWF11. auto. }
        contradiction.
    - destruct (lt_dec (n + r21 (x - n)) n).
      + lia.
      + assert ((n + r21 (x - n) - n) = (r21 (x - n))).
        lia.
        rewrite H.
        reflexivity.
  Qed.

  Lemma ren_compose_app :
    forall {m n X}
      (r1 : ren m m)  (r2 : ren n n)
      (HWB1 : wf_bij_ren r1) (HWB2 : wf_bij_ren r2)
      (c : ctxt m X) (d : ctxt n X),
      (ren_compose r1 c) ⊗ (ren_compose r2 d) = 
        ren_compose (bij_app r1 r2) (c ⊗ d).
  Proof.
    intros. apply functional_extensionality. intros.
    unfold ren_compose, compose, bij_app, ctxt_app.
    dest_wf_bij_ren. destruct (lt_dec x m).
    - destruct (lt_dec (r1 x) m).
      + reflexivity.
      + assert (r1 x < m). { apply x1. assumption. }
        contradiction.
    - destruct (lt_dec (m + r2 (x - m)) m).
      + lia.
      + assert ((m + (r2 (x - m)) - m) = (r2 (x - m))) by lia.
        rewrite H. reflexivity.
  Qed.        

  Lemma bij_app_inv :
    forall {m m'} (r1 : ren m m) (r2 : ren m' m')
      (HWB1 : wf_bij_ren r1) (HWB2 : wf_bij_ren r2),
      bij_app (bij_inv r1 HWB1) (bij_inv r2 HWB2) =
        bij_inv (bij_app r1 r2) (wf_bij_ren_app r1 r2 HWB1 HWB2).
  Proof.
    intros.
    destruct HWB1 as [HWF1 [r1_inv [WFI1 BRI1]]].
    destruct HWB2 as [HWF2 [r2_inv [FWI2 BRI2]]].
    reflexivity.
  Qed.
  
  (* SAZ: the stronger notion of renaming well-formedness, which requires
     out-of-scope variables to be canonical, lets us prove this
     equivalence.
   *) 
  Lemma wf_bij_ren_app_inv_compose_id :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r),
      ren_compose r (bij_inv r HWB) = ren_id n.
  Proof.
    intros.
    destruct HWB as [HWF [r_inv [HR HI]]]; simpl.
    unfold ren_inverses in HI.
    unfold ren_compose, compose, ren_id.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    + apply HI. assumption.
    + assert (r x = n).
      apply HWF. assumption.
      rewrite H.
      apply HR.
      lia.
  Qed.
  
  Lemma ren_sum_compose : forall {n} (r : ren n n) (c : lctxt n) (d : lctxt n),
      ren_compose r (c ⨥ d) = (ren_compose r c) ⨥ (ren_compose r d).
  Proof.
    intros.
    apply functional_extensionality.
    intros x.
    reflexivity.
  Qed.

  Lemma bij_ren_var :
    forall {n} (r : ren n n) x y
      (HWB : wf_bij_ren r),
      x < n ->
      y < n ->
      r x = y <-> x = (bij_inv r HWB) y.
  Proof.
    intros.
    destruct HWB as [HWF [r_inv [HWRI HE]]].
    simpl.
    unfold ren_inverses in HE.
    split; intros; subst.
    - specialize (HE _ H).
      destruct HE.
      rewrite H1. reflexivity.
    - specialize (HE _ H0).
      destruct HE.
      assumption.
  Qed.
      
  Lemma ren_delta_compose :
    forall {n} (r : ren n n) x c (HWB : wf_bij_ren r),
      x < n ->
      ren_compose r (n[x ↦ c]) = n[((bij_inv r HWB)  x) ↦ c].
  Proof.
    intros.
    unfold ren_compose, compose, delta.
    destruct HWB as [HWF [r_inv [HWF' HEQ]]].
    simpl.
    apply functional_extensionality.
    intros y.
    destruct (lt_dec x n); try lia.
    destruct (Nat.eq_dec x (r y)); subst.
    
    - destruct (lt_dec (r_inv (r y)) n); try lia.
      unfold ren_inverses in HEQ. unfold wf_ren in HWF.
      assert (y < n).
      { specialize (HWF y); destruct HWF. lia. }
      specialize (HEQ y); destruct HEQ; try lia.
      destruct (Nat.eq_dec (r_inv (r y)) y); try lia.
      unfold ren_inverses in HEQ. 
      specialize (HEQ (r y)); destruct HEQ; try lia.
      unfold wf_ren in HWF.
      specialize (HWF' (r y)); try lia.

    - destruct (lt_dec (r_inv x) n); try lia.
      destruct (Nat.eq_dec (r_inv x) y); try lia.
      unfold ren_inverses in HEQ.
      assert (x = (r y)).
      { specialize (HEQ x); destruct HEQ. 
        assumption.
        subst; symmetry; assumption. }
      contradiction.
  Qed.

  Lemma ren_compose_flat_ctxt : forall {n m} x (r : ren n m),
    (ren_compose r (flat_ctxt x m)) = (flat_ctxt x m).
  Proof. auto. Qed.
  
  Lemma ren_one_compose :
    forall {n} (r : ren n n) (HWB : wf_bij_ren r) x,
      x < n ->
      ren_compose r (one n x) = one n ((bij_inv r HWB) x).
  Proof.
    intros.
    unfold one.
    apply ren_delta_compose; auto.
  Qed.

  Lemma ren_SUM_compose :
    forall {n} (r : ren n n)
      (l : list (lctxt n)),
      ren_compose r (SUM l) = SUM (List.map (ren_compose r) l).
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite ren_sum_compose.
      rewrite IHl. reflexivity.
  Qed.


(* FRAN: Is this relevant? *)
Lemma map_ext_Forall_partial :
    forall {A B} (f g : A -> B) (l : list A) (P : A -> Prop),
    (forall x, P x -> f x = g x) ->
    Forall P l -> map f l = map g l.
Proof.
  intros. induction l.
  - reflexivity.
  - inversion H0; subst; simpl.
    rewrite H; auto. rewrite IHl; auto.
Qed.    

Lemma Forall_ren_wf :
  forall {n} (r : ren n n) (HR: wf_ren r) (rs:list var),
    Forall (fun x => x < n) rs ->
    Forall (fun x => x < n) (map r rs).
Proof.
  intros. apply Forall_map. eapply Forall_impl.
  2 : { apply H. }
  apply HR.
Qed.  
  
End Renamings.  

Module RelationalRenamings.

Definition ren (n m:nat) := ctxt n (var -> Prop).

Definition wf_ren {n m:nat} (r : ren n m) :=
  forall x y, x < n -> r x y -> y < m.

Definition ren_eq (n m:nat) (r1 r2 : ren n m) :=
  forall x y, x < n -> (r1 x y <-> r2 x y).


Infix "≡[ n , m ]" := (ren_eq n m) (at level 70).

#[global] Instance refl_ren_eq : forall n m, Reflexive (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros; auto.
Qed.

#[global] Instance sym_ren_eq : forall n m, Symmetric (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros.
  - rewrite H; tauto.
  - rewrite <- H; tauto.
Qed.

#[global] Instance trans_ren_eq : forall n m, Transitive (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros.
  - rewrite <- H0; auto. rewrite <- H; tauto.
  - rewrite H; auto. rewrite H0; tauto.
Qed.

(* Some renamings are functional *)
Definition fun_ren {n m} (r : ren n m) : Prop :=
  forall x y z, x < n -> r x y -> r x z -> y = z.

Definition ren_id (n : nat) : ren n n := fun (x y:var) => x = y.

Lemma wf_ren_id : forall n, wf_ren (ren_id n).
Proof.
  unfold wf_ren, ren_id.
  intros. subst. assumption.
Qed.  

Lemma fun_ren_id : forall n, fun_ren (ren_id n).
Proof.
  unfold fun_ren, ren_id.
  intros.
  subst. reflexivity.
Qed.  

Definition ren_zero : ren 0 0 := fun x y => False.

Lemma wf_ren_zero : wf_ren (ren_zero).
Proof.
  unfold wf_ren, ren_zero.
  intros. inversion H0.
Qed.  

Lemma fun_ren_zero : fun_ren (ren_zero).
Proof.
  unfold fun_ren, ren_zero.
  intros. contradiction.
Qed.  

Definition ren_app {n1 m1 n2 m2} (r1 : ren n1 m1) (r2 : ren n2 m2) : ren (n1+n2) (m1+m2) :=
  fun x y =>
    if Compare_dec.lt_dec x n1 then
      if Compare_dec.lt_dec y m1 then
        r1 x y else False
    else
      if Compare_dec.lt_dec y m1 then
        False else
      r2 (x - n1) (y - m1).

Infix "⨣" := (@ren_app _ _ _ _) (at level 50).

Lemma wf_ren_app : forall n1 m1 n2 m2
                     (r1 : ren n1 m1)
                     (r2 : ren n2 m2)
                     (HR1: wf_ren r1)
                     (HR2 : wf_ren r2),
    wf_ren (r1 ⨣ r2).
Proof.
  unfold wf_ren, ren_app.
  intros.
  destruct (lt_dec x n1); destruct (lt_dec y m1); try lia.
  assert ((x - n1)  < n2). { lia. }
  destruct (lt_dec y m2); try lia.
  specialize (HR2 (x-n1) (y-m1) H1 H0).
  lia.
Qed.  

Lemma fun_ren_app : forall n1 m1 n2 m2
                      (r1 : ren n1 m1)
                      (r2 : ren n2 m2)
                      (HR1: fun_ren r1)
                      (HR2 : fun_ren r2),
    fun_ren (r1 ⨣ r2).
Proof.
  unfold fun_ren, ren_app.
  intros.
  destruct (lt_dec x n1); destruct (lt_dec y m1); destruct (lt_dec z m1); try lia.
  - eapply HR1; eauto.
  - assert ((y - m1)  = (z - m1)). { eapply HR2; eauto. lia. }
    lia.
Qed.    

Lemma ren_app_zero_l : forall n m (r : ren n m),
    (ren_zero ⨣ r) ≡[n, m] r.
Proof.
  unfold ren_zero, ren_app, ren_eq.
  intros.
  destruct (lt_dec x 0); destruct (lt_dec y 0); auto.
  - inversion l.
  - inversion l.
  - inversion l.
  - repeat rewrite Nat.sub_0_r. tauto.
Qed.

Lemma ren_app_zero_r : forall n m (r : ren n m)
    (HR:wf_ren r),
    (r ⨣ ren_zero) ≡[n, m] r.
Proof.
  unfold wf_ren, ren_zero, ren_app, ren_eq.
  intros.
  destruct (lt_dec x n); destruct (lt_dec y m); auto.
  - tauto.
  - split; try tauto. intros HY. specialize (HR _ _ l HY). contradiction.
  - split; try tauto. 
  - split; try tauto. 
Qed.  

Lemma ren_app_assoc : forall n1 n2 m1 m2 o1 o2 (r1 : ren n1 n2) (r2 : ren m1 m2) (r3 : ren o1 o2),
    wf_ren r2 ->
    (r1 ⨣ r2) ⨣ r3 ≡[n1 + m1 + o1, n2 + m2 + o2] r1 ⨣ (r2 ⨣ r3).
Proof.
  unfold wf_ren, ren_eq, ren_app. intros.
  destruct (lt_dec x n1).
  - destruct (lt_dec x (n1 + m1)).
    + destruct (lt_dec y n2); destruct (lt_dec y (n2 + m2)); try lia.
      tauto.
    + destruct (lt_dec y n2); try lia.
  - destruct (lt_dec x (n1 + m1)).
    + destruct (lt_dec y (n2 + m2)); try lia.
      * destruct (lt_dec (x - n1) m1); try lia.
        destruct (lt_dec (y - n2) m2); try lia.
        -- tauto.
        -- destruct (lt_dec y n2); try lia.
      * destruct (lt_dec y n2); try lia.
        destruct (lt_dec (x - n1) m1); try lia.
        destruct (lt_dec (y - n2) m2); try lia.
    + destruct (lt_dec (x - n1) m1); try lia.
      destruct (lt_dec y n2); try lia.
      -- destruct (lt_dec y (n2 + m2)); try lia.
      -- destruct (lt_dec (y - n2) m2); destruct (lt_dec y (n2 + m2)); try lia.
         replace (y - (n2 + m2)) with (y - n2 - m2) by lia.
         replace (x - (n1 + m1)) with (x - n1 - m1) by lia.
         reflexivity.
Qed.      
      

Definition function_ren (n m : nat) (f:nat -> nat) : ren n m := fun x y => (f x) = y.

Lemma wf_function_ren : forall n m (f:nat -> nat) (HF: forall x, x < n -> (f x) < m), wf_ren (function_ren n m f).
Proof.
  unfold wf_ren, function_ren.
  intros. subst. auto.
Qed.

Lemma fun_function_ren : forall n m (f:nat -> nat), fun_ren (function_ren n m f).
Proof.
  unfold fun_ren, function_ren.
  intros.
  subst. reflexivity.
Qed.  

Definition shift_ren n' n m (r : ren n m) : ren (n' + n) (n' + m) :=
  (ren_id n') ⨣ r.

Lemma id_ren_app : forall n m, (ren_id n) ⨣ (ren_id m) ≡[n,m] (ren_id (n+m)).
Proof.
  unfold ren_id, ren_eq, ren_app.
  intros.
  split; intros.
  - destruct (lt_dec x n); destruct (lt_dec y n); tauto.
  - destruct (lt_dec x n); destruct (lt_dec y n); lia.
Qed.

Definition ren_compose {n m o} (r1 : ren n m) (r2 : ren m o) : ren n o :=
  fun x y => exists z, r1 x z /\ r2 z y.

Notation "f ;; g" := (@ren_compose _ _ _ f g) (at level 55, right associativity).

Lemma wf_ren_compose : forall n m o (r1 : ren n m) (r2 : ren m o),
    wf_ren r1 -> wf_ren r2 -> wf_ren (r1 ;; r2).
Proof.
  unfold wf_ren, ren_compose.
  intros.
  destruct H2 as [z [HR1 HR2]].
  eauto.
Qed.

Lemma ren_compose_id_l : forall n m (r : ren n m),
    (ren_id n) ;; r ≡[n,m] r.
Proof.
  unfold ren_id, ren_compose, ren_eq.
  intros. split; intros.
  - destruct H0 as [z [HX HR]].
    subst. assumption.
  - exists x. auto.
Qed.

Lemma ren_compose_id_r : forall n m (r : ren n m),
    r ;; (ren_id m) ≡[n,m] r.
Proof.
  unfold ren_id, ren_compose, ren_eq.
  intros. split; intros.
  - destruct H0 as [z [HX HR]].
    subst. assumption.
  - exists y. auto.
Qed.

Lemma ren_compose_assoc : forall n m o p (r1 : ren n m) (r2 : ren m o) (r3 : ren o p),
    (r1 ;; r2) ;; r3 ≡[n,p] r1 ;; (r2 ;; r3).
Proof.
  unfold ren_compose, ren_eq. intros.
  split; intros.
  - destruct H0 as [z [[w [HR1 HR2]] HR3]].
    exists w. split; auto. exists z; auto.
  - destruct H0 as [z [HR1 [w [HR2 HR3]]]].
    exists w. split; auto. exists z; auto.
Qed.

Lemma fun_ren_compose : forall n m o (r1 : ren n m) (r2 : ren m o),
    wf_ren r1 ->
    fun_ren r1 -> fun_ren r2 -> fun_ren (r1 ;; r2).
Proof.
  unfold wf_ren, fun_ren, ren_compose.
  intros.
  destruct H3 as [w1 [HW11 HW12]].
  destruct H4 as [w2 [HW21 HW22]].
  assert (w1 = w2). { eapply H0; eauto. }
  subst.
  eapply H1; eauto.
Qed.  

End RelationalRenamings.


(* Linear Contexts and Renamings -------------------------------------------- *)

(*
  0 -> 1
  1 -> 1
  2 -> _
  3 -> 2
  4 -> 0

  ren 5 3

  l(0) = k0
  l(1) = k1
  l(2) = k2
  l(3) = k3
  l(4) = k4

  cl(0) = k4
  cl(1) = k0 + k1
  cl(2) = k3
  
*)

Import ListNotations.

Lemma not_app_tl_empty : forall A (xs : list A) (x : A),
    ~ [] = xs ++ [x].
Proof.
  intros.
  intro H.
  induction xs; auto.
  - inversion H.
  - inversion H.
Qed.    

Lemma list_app_tl_inv : forall A (xs ys : list A) (x y : A),
    xs ++ [x] = ys ++ [y] ->
    xs = ys /\ x = y.
Proof.
  induction xs; intros; auto.
  - simpl in H.
    destruct ys.
    + inversion H. subst.
      split; auto.
    + inversion H.
      subst.
      apply not_app_tl_empty in H2.
      contradiction.
  - simpl in H.
    destruct ys.
    + inversion H. symmetry in H2.
      apply not_app_tl_empty in H2.
      contradiction.
    + simpl in H.
      inversion H; subst.
      apply IHxs in H2.
      destruct H2; subst.
      split; auto.
Qed.      


(* We can canonically represent a (linear) context by a sequence of natural numbers. *)

Definition lctxt_to_seq (n:nat) (c : lctxt n) : list nat :=
  List.map c (seq 0 n).

Definition seq_to_lctxt (n:nat) (l:list nat) : lctxt n :=
  fun x => List.nth x l 0.

Lemma lctxt_to_seq_inv :
  forall n (c : lctxt n),
    c n = 0 ->
    (seq_to_lctxt n (lctxt_to_seq n c)) ≡[n] c.
Proof.
  unfold seq_to_lctxt, lctxt_to_seq, ctxt_eq.
  intros.
  rewrite <- H at 2.
  rewrite map_nth.
  rewrite seq_nth; auto.
Qed.  
  
Lemma lctxt_to_seq_ext : forall n (c d : lctxt n),
    (lctxt_to_seq n c = lctxt_to_seq n d) <->
      (forall x, x < n -> c x = d x).
Proof.
  intros.
  split; intros.
  - induction n.
    + lia.
    + unfold lctxt_to_seq in H.
      rewrite seq_S in H.
      do 2 rewrite map_app in H.
      simpl in H.
      apply list_app_tl_inv in H.
      destruct H as [HEQ EQ].
      inversion H0.
      * assumption.
      * subst.
        apply IHn in HEQ.
        assumption.
        lia.
  - revert c d H.
    induction n; intros.
    + reflexivity.
    + unfold lctxt_to_seq.
      simpl.
      rewrite <- seq_shift.
      rewrite map_map.
      rewrite map_map.
      unfold lctxt_to_seq in IHn.
      setoid_rewrite (IHn (fun x => c (S x)) (fun x => d (S x))).
      rewrite H. reflexivity.
      lia.
      intros.
      rewrite H. reflexivity.
      lia.
Qed.      
      
Fixpoint iter {A B} (elt : nat -> A) (base : B) (combine : A -> B -> B) (start len : nat) : B :=
  match len with
  | 0 => base
  | S len0 => combine (elt start) (iter elt base combine (S start) len0)
  end.

Lemma iter_0 : 
  forall A B (elt : nat -> A) (b : B) f start,
    iter elt b f start 0 = b.
Proof.
  intros. reflexivity.
Qed.  

Lemma iter_cons :
  forall A B (elt : nat -> A) (b : B) f start len,
    f (elt start) (iter elt b f (1 + start) len) =
      iter elt b f start (1 + len).
Proof.
  reflexivity.
Qed.

Lemma iter_ext :
  forall A B (f g : nat -> A) (b : B) (combine : A -> B -> B) (start len : nat)
    (HEQ : forall x, x < start + len -> f x = g x),
    iter f b combine start len = iter g b combine start len.
Proof.
  intros. revert start HEQ.
  induction len; intros.
  - reflexivity.
  - simpl.
    assert (f start = g start). { apply HEQ.  lia. }
    rewrite H.
    rewrite IHlen.
    reflexivity.
    intros.
    apply HEQ. lia.
Qed.    

(*
Lemma iter_shift : forall A B (elt : nat -> A) (b : B) (f : A -> B -> B)  offs start len,
    iter elt b f (offs + start) len =
      iter (fun x => elt (offs + x)) b f start len.
Proof.
  induction offs; intros.
  - reflexivity.
  - simpl.
    replace (S (offs + start)) with (offs + S start) by lia.
*)    


Lemma iter_f_plus : forall A B m n i (elt : nat -> A) (b : B) (f : A -> B -> B),
    iter elt b f i (m + n) =
      iter elt (iter elt b f (i + m) n) f i m.
Proof.
  induction m; intros.
  - simpl.
    replace (i + 0) with i by lia.
    reflexivity.
  - simpl.
    rewrite IHm.
    replace (S i + m) with (i + S m) by lia.
    reflexivity.
Qed.    

(* iterates through a context starting at [start] *)
Definition ctxt_iter {X B} {n:nat} (c : ctxt n X) (base : B) (combine : X -> B -> B) (start:nat) : B :=
  iter c base combine start (n - start).

Lemma ctxt_iter_end :
  forall X B n (c : ctxt n X) (b:B) (combine : X -> B -> B),
    ctxt_iter c b combine n = b.
Proof.
  intros.
  unfold ctxt_iter.
  replace (n - n) with 0 by lia.
  apply iter_0.
Qed.  

Lemma ctxt_iter_ext :
  forall X B (n:nat) (c d : ctxt n X) (b:B) (combine : X -> B -> B) (start:nat)
    (HS : start < n)
    (HEQ : forall x, x < n -> c x = d x),
    ctxt_iter c b combine start = ctxt_iter d b combine start.
Proof.
  intros.
  unfold ctxt_iter.
  apply iter_ext.
  intros.
  apply HEQ.
  lia.
Qed.  

(*
Lemma cxt_iter_trim_retract :
  forall X B (m n:nat) (c : ctxt (m + n) X) (b : B) (combine : X -> B -> B) (start : nat),
    ctxt_iter c b combine start =
      ctxt_iter (ctxt_trim m n c) (ctxt_iter (ctxt_retract m n c) b combine 0) combine start.
Proof.
  intros.
  unfold ctxt_trim, ctxt_iter, ctxt_retract.
  destruct (lt_dec start m).
  - replace (m + n - start) with ((m - start) + n) by lia.
    rewrite iter_f_plus.
    replace (n - 0) with n by lia.
    replace (start + (m - start)) with m by lia.
    
    replace (n - (m - start)) with (n + start - m) by lia.
    admit.
  - replace (m - start) with 0 by lia.
    rewrite iter_0.
    
    replace (n - n) with 0 by lia.
    rewrite iter_0.
    
    
    
  
  
  destruct (lt_dec start (m + n)).
  - 
    + replace (m + n - start) with ((m - start) + n) by lia.
      rewrite iter_f_app.
      replace (start + (m - start)) with m by lia.
      replace (n - (m - start + n)) with 0 by lia.
      rewrite iter_0.
      


Lemma iter_ctxt_app : forall X B m n i (c : ctxt m X) (d : ctxt n X) (b : B) (f : X -> B -> B),
    ctxt_iter (c ⊗ d) b f i =
      ctxt_iter c (ctxt_iter d b f 0) f i.  
Proof.
  intros.
  destruct (lt_dec i m).
  - rewrite (ctxt_app_trim_retract _ _ _ (c ⊗ d)).
    unfold ctxt_iter at 1.
    replace (m + n - i) with ((m - i) + n) by lia.
    rewrite iter_f_app.
    replace (i + (m - i)) with m by lia.
    rewrite ctxt_retract_app.
    unfold ctxt_iter.
    
*)    


(*
Lemma lctxt_to_seq_ext' : forall n (c d : lctxt n),
    forall i, 
    (lctxt_to_seq i n c = lctxt_to_seq i n d) <->
      (forall x, (i + x) < n -> c (i + x) = d (i + x)).
Proof.
  induction n; intros; split; intros.
  - lia.
  - reflexivity.
  - unfold lctxt_to_seq in H.
    simpl in H. seq
    inversion H0.
    destruct x.
    * replace (i + 0) with i by lia.
      assumption.
    * replace (i + S x) with ((S i) + x) by lia.
      

      apply H3.
      
      
      * apply IHn. 
      
      simpl in H.
      apply list_app_tl_inv in H.
      destruct H as [HEQ EQ].
      inversion H0.
      * inversion EQ.
        subst. reflexivity.
      * subst.
        apply IHn in HEQ.
        assumption.
        lia.
  - revert c d H.
    induction n; intros.
    + reflexivity.
    + unfold lctxt_to_list.
      simpl.
      do 2 rewrite map_app.
      simpl.
      unfold lctxt_to_list in IHn.
      setoid_rewrite (IHn c d).
      rewrite (H n); try lia.
      reflexivity.
      intros. apply H; lia.
Qed.
  
*)



Fixpoint up_to (n:nat) : list nat :=
  match n with
  | 0 => []
  | S n => (up_to n) ++ [n]
  end.

Lemma up_to_length : forall n, length (up_to n) = n.
Proof.
  induction n; auto.
  simpl. rewrite length_app. simpl.
  rewrite IHn.
  lia.
Qed.  

(* Could map between general lists and context, but this may be all we need? *)
Definition lctxt_to_list (n:nat) (c : lctxt n) : list (var * nat) :=
  List.map (fun x => (x, c x)) (up_to n).

Lemma length_lctxt_to_list : forall n (c: lctxt n),
    length (lctxt_to_list n c) = n.
Proof.
  intros.
  unfold lctxt_to_list.
  rewrite length_map.
  apply up_to_length.
Qed.  

Definition list_to_lctxt_SUM (n:nat) (l : list (var * nat)) : lctxt n :=
  SUM (List.map (fun '(x,i) => delta n x i) l).

Definition var_list_to_lctxt_SUM (n:nat) (rs : list var) :=
  list_to_lctxt_SUM n (map (fun x => (x,1)) rs).

Lemma lctxt_to_list_S : forall (n:nat) (c : lctxt (S n)),
    lctxt_to_list (S n) c = (lctxt_to_list n c)++[(n,c n)].
Proof.
  intros.
  unfold lctxt_to_list.
  simpl.
  rewrite map_app.
  reflexivity.
Qed.  


Lemma lctxt_to_list_ext : forall n (c d : lctxt n),
    (lctxt_to_list n c = lctxt_to_list n d) <->
      c ≡[n] d.
Proof.
  unfold ctxt_eq.
  intros.
  split; intros.
  - induction n.
    + lia.
    + unfold lctxt_to_list in H.
      simpl in H.
      do 2 rewrite map_app in H.
      simpl in H.
      apply list_app_tl_inv in H.
      destruct H as [HEQ EQ].
      inversion H0.
      * inversion EQ.
        subst. reflexivity.
      * subst.
        apply IHn in HEQ.
        assumption.
        lia.
  - revert c d H.
    induction n; intros.
    + reflexivity.
    + unfold lctxt_to_list.
      simpl.
      do 2 rewrite map_app.
      simpl.
      unfold lctxt_to_list in IHn.
      setoid_rewrite (IHn c d).
      rewrite (H n); try lia.
      reflexivity.
      intros. apply H; lia.
Qed.

(* [cs] is a list of counts. The i'th element of the list is the
   usage for the i'th de Bruijn variable.
 *)
Fixpoint list_to_lctxt_app (cs : list (var * nat)) : lctxt (length cs) :=
  match cs with
  | [] => zero 0
  | (_,c)::cs' => @ctxt_app _ 1 (length cs') (delta 1 0 c) (list_to_lctxt_app cs')
  end.

Lemma list_to_lctxt_app_hd : forall x d l,
    list_to_lctxt_app ((x,d)::l) = @ctxt_app _ 1 (length l) (delta 1 0 d) (list_to_lctxt_app l).
Proof.
  intros. reflexivity.
Qed.  

Lemma list_to_lctxt_app_app : forall (l1 l2 : list (var * nat)),
    list_to_lctxt_app (l1++l2) =
      @ctxt_app _ (length l1) (length l2) (list_to_lctxt_app l1) (list_to_lctxt_app l2).
Proof.
  induction l1; intros.
  - simpl.
    rewrite ctxt_app_null_l. reflexivity.
  - destruct a as [x c].
    simpl.
    rewrite IHl1.
    simpl. 
    replace (S (@length (prod var nat) l1)) with (1 + (@length (prod var nat) l1)) by lia.
    rewrite <- ctxt_app_assoc.
    reflexivity.
Qed.    


Lemma list_to_lctxt_app_0 : forall n (c : lctxt n) x,
    n <= x ->
    list_to_lctxt_app (lctxt_to_list n c) x = 0.
Proof.
  induction n; intros; simpl in *; auto.
  rewrite lctxt_to_list_S.
  rewrite list_to_lctxt_app_app.
  unfold ctxt_app.
  rewrite length_lctxt_to_list.
  destruct (lt_dec x n).
  - lia.
  - simpl.
    unfold ctxt_app.
    destruct (lt_dec (x - n) 1).
    * unfold delta.
      lia.
    * reflexivity.
Qed.  

Lemma lctxt_to_list_app_eq : forall n (c : lctxt n),
    list_to_lctxt_app (lctxt_to_list n c) ≡[n] c.
Proof.
  unfold ctxt_eq.
  induction n; simpl; intros.
  - lia.
  - rewrite lctxt_to_list_S.
    rewrite list_to_lctxt_app_app.
    simpl.
    destruct (lt_dec x n).
    + rewrite ctxt_app_l. rewrite IHn; auto.
      rewrite length_lctxt_to_list. assumption.
    + assert (x = n) by lia.
      subst.
      rewrite ctxt_app_r.
      rewrite length_lctxt_to_list.
      replace (n - n) with 0 by lia.
      rewrite ctxt_app_l; auto.
      rewrite length_lctxt_to_list.
      lia.
Qed.

Lemma lctxt_sum_app_dist : forall n m (D11 D21 : lctxt n) (D12 D22 : lctxt m), 
    (@ctxt_app nat n m D11 D12) ⨥ (D21 ⊗ D22) = (D11 ⨥ D21) ⊗ (D12 ⨥ D22).
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  rewrite lctxt_sum.
  unfold ctxt_app.
  destruct (lt_dec x n).
  - reflexivity.
  - rewrite lctxt_sum.
    reflexivity.
Qed.    

Lemma lctxt_S_retract : forall n (D : lctxt (S n)),
    D = @ctxt_app _ 1 n 1[0 ↦ D(0)] (ctxt_retract 1 n D).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold ctxt_app.
  destruct (lt_dec x 1).
  - assert (x = 0) by lia.
    subst.
    reflexivity.
  - unfold ctxt_retract.
    replace (1 + (x - 1)) with x by lia.
    reflexivity.
Qed.    

Lemma ctxt_S_inv : forall {X} n (c : ctxt (S n) X),
    c = (ctxt_trim 1 n c) ⊗ (ctxt_retract 1 n c).
Proof.
  intros.
  apply ctxt_app_trim_retract.
Qed.  

Lemma ctxt_app_inv_r :
  forall {X} n m (c1 c2 : ctxt n X)  (d1 d2 : ctxt m X),
    (c1 ⊗ d1) = (c2 ⊗ d2) -> d1 = d2.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  assert ((c1 ⊗ d1) (n + x) = (c2 ⊗ d2) (n + x)).
  { rewrite H. reflexivity. }
  assert ((x + n) <= (n + x)) by lia.
  do 2 rewrite ctxt_app_r in H0; try lia.
  replace (n + x - n) with x in * by lia.
  assumption.
Qed.

Lemma ctxt_app_inv_r_eq :
  forall {X} n m (c1 c2 : ctxt n X)  (d1 d2 : ctxt m X),
    (c1 ⊗ d1) ≡[n + m] (c2 ⊗ d2) -> d1 ≡[m] d2.
Proof.
  intros.
  unfold ctxt_eq in *.
  intros.
  assert ((c1 ⊗ d1) (n + x) = (c2 ⊗ d2) (n + x)).
  { rewrite H. reflexivity. lia. }
  assert ((x + n) <= (n + x)) by lia.
  do 2 rewrite ctxt_app_r in H1; try lia.
  replace (n + x - n) with x in * by lia.
  assumption.
Qed.

Lemma ctxt_app_inv_l :
  forall {X} n m (c1 c2 : ctxt n X)  (d1 d2 : ctxt m X),
    (c1 ⊗ d1) = (c2 ⊗ d2) ->
    c1 ≡[n] c2.
Proof.
  unfold ctxt_eq.
  intros.
  assert ((c1 ⊗ d1) x = (c2 ⊗ d2) x).
  { rewrite H. reflexivity. }
  do 2 rewrite ctxt_app_l in H1; auto.
Qed.

Lemma ctxt_app_inv_l_eq :
  forall {X} n m (c1 c2 : ctxt n X)  (d1 d2 : ctxt m X),
    (c1 ⊗ d1) ≡[n + m] (c2 ⊗ d2) ->
    c1 ≡[n] c2.
Proof.
  unfold ctxt_eq.
  intros.
  assert ((c1 ⊗ d1) x = (c2 ⊗ d2) x).
  { rewrite H. reflexivity.  lia. }
  do 2 rewrite ctxt_app_l in H1; auto.
Qed.

Lemma ctxt_app_ext_l : forall X n m (c1 c2 : ctxt n X) (d : ctxt m X),
    (c1 ≡[n] c2) ->
    c1 ⊗ d = c2 ⊗ d.
Proof.
  unfold ctxt_eq.
  intros.
  apply functional_extensionality.
  intros x.
  unfold ctxt_app.
  destruct (lt_dec x n); auto.
Qed.  

Lemma sum_app_inv : forall n m (D1 D2 : lctxt (n + m)) (Da : lctxt n) (Db : lctxt m),
  (D1 ⨥ D2) = Da ⊗ Db ->
  exists (Da1 Da2 : lctxt n) (Db1 Db2 : lctxt m),
    (D1 = Da1 ⊗ Db1) /\ (D2 = Da2 ⊗ Db2) /\ (Da1 ⨥ Da2) = Da /\ (Db1 ⨥ Db2) = Db.
Proof. intros.
  induction n; intros.
  - rewrite ctxt_app_null_l in H.
    exists (zero 0). exists Da. exists D1. exists D2.
    repeat split.
    + rewrite ctxt_app_null_l.
      reflexivity.
    + rewrite ctxt_app_null_l.
      reflexivity.
    + assumption.
  - simpl in *.
    rewrite (lctxt_S_retract (n + m) D1) in H.
    rewrite (lctxt_S_retract (n + m) D2) in H.
    rewrite (lctxt_sum_app_dist 1 (n + m)) in H.
    rewrite (lctxt_S_retract n Da) in H.
    replace (S (n + m)) with (1 + (n + m)) in * by lia.
    replace (S n) with (1 + n) in * by lia.
    rewrite <- ctxt_app_assoc in H.
    rewrite delta_sum in H.
    specialize (ctxt_app_inv_r _ _ _ _ _ _ H) as HEQ.
    apply IHn in HEQ.
    destruct HEQ as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
    exists ((1 [0 ↦ D1 0]) ⊗ DA1).
    exists (1 [0 ↦ D2 0] ⊗ DA2).
    exists DB1. exists DB2.
    repeat split.
    + rewrite <- ctxt_app_assoc.
      rewrite <- EQ1.
      rewrite <- lctxt_S_retract.
      reflexivity.
    + rewrite <- ctxt_app_assoc.
      rewrite <- EQ2.
      rewrite <- lctxt_S_retract.
      reflexivity.
    + rewrite lctxt_sum_app_dist.
      rewrite delta_sum.
      specialize (ctxt_app_inv_l _ _ _ _ _ _ H) as HEQ.
      eapply ctxt_app_ext_l with (d := (DA1 ⨥ DA2))(m := n) in HEQ.
      rewrite HEQ.
      rewrite EQ3.
      symmetry.
      apply lctxt_S_retract.
    + assumption.
Qed.      

Lemma sum_app_inv_ctxt : forall n m (D1 D2 : lctxt (n + m)) (Da : lctxt n) (Db : lctxt m),
   Da ⊗ Db ≡[n + m] (D1 ⨥ D2) ->
  exists (Da1 Da2 : lctxt n) (Db1 Db2 : lctxt m),
    (D1 ≡[n + m] Da1 ⊗ Db1) /\ (D2 ≡[n + m] Da2 ⊗ Db2) /\ (Da1 ⨥ Da2) ≡[n] Da /\ (Db1 ⨥ Db2) ≡[m] Db.
Proof.
  induction n; intros.
  - rewrite ctxt_app_null_l in H.
    exists (zero 0). exists Da. exists D1. exists D2.
    repeat split.
    + rewrite ctxt_app_null_l.
      reflexivity.
    + rewrite ctxt_app_null_l.
      reflexivity.
    + symmetry. apply H.
  - simpl in *.
    rewrite (lctxt_S_retract (n + m) D1) in H.
    rewrite (lctxt_S_retract (n + m) D2) in H.
    rewrite (lctxt_sum_app_dist 1 (n + m)) in H.
    rewrite (lctxt_S_retract n Da) in H.
    replace (S (n + m)) with (1 + (n + m)) in * by lia.
    replace (S n) with (1 + n) in * by lia.
    rewrite <- ctxt_app_assoc in H.
    rewrite delta_sum in H.
    specialize (ctxt_app_inv_r_eq _ _ _ _ _ _ H) as HEQ.
    apply IHn in HEQ.
    destruct HEQ as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
    exists ((1 [0 ↦ D1 0]) ⊗ DA1).
    exists (1 [0 ↦ D2 0] ⊗ DA2).
    exists DB1. exists DB2.
    repeat split.
    + rewrite <- ctxt_app_assoc.
      rewrite <- EQ1.
      rewrite <- lctxt_S_retract.
      reflexivity.
    + rewrite <- ctxt_app_assoc.
      rewrite <- EQ2.
      rewrite <- lctxt_S_retract.
      reflexivity.
    + rewrite lctxt_sum_app_dist.
      rewrite delta_sum.
      specialize (ctxt_app_inv_l_eq _ _ _ _ _ _ H) as HEQ.
      rewrite <- HEQ.
      rewrite EQ3.
      simpl.
      rewrite lctxt_S_retract.
      reflexivity.
    + assumption.
Qed.      

Lemma sum_zero_inv_l : forall n (c1 c2 : lctxt n),
    (c1 ⨥ c2) = zero n -> c1 = zero n.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  assert ((c1 ⨥ c2) x = zero n x). { rewrite H. reflexivity. }
  unfold sum, zero, flat_ctxt in *.
  lia.
Qed.

Lemma sum_zero_inv_r : forall n (c1 c2 : lctxt n),
    (c1 ⨥ c2) = zero n -> c2 = zero n.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  assert ((c1 ⨥ c2) x = zero n x). { rewrite H. reflexivity. }
  unfold sum, zero, flat_ctxt in *.
  lia.
Qed.

Lemma sum_zero_inv_l_eq : forall n (c1 c2 : lctxt n),
    (c1 ⨥ c2) ≡[n] zero n -> c1 ≡[n] zero n.
Proof.
  unfold ctxt_eq.
  intros.
  assert ((c1 ⨥ c2) x = zero n x). { rewrite H. reflexivity. auto. }
  unfold sum, zero, flat_ctxt in *.
  lia.
Qed.

Lemma sum_zero_inv_r_eq : forall n (c1 c2 : lctxt n),
    (c1 ⨥ c2) ≡[n] zero n -> c2 ≡[n] zero n.
Proof.
  unfold ctxt_eq.
  intros.
  assert ((c1 ⨥ c2) x = zero n x). { rewrite H. reflexivity. auto. }
  unfold sum, zero, flat_ctxt in *.
  lia.
Qed.

Lemma fun_apply : forall A B (f g : A -> B),
    f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H. reflexivity.
Qed.  

Lemma app_delta_zero_inv_lt :
  forall n m (c : lctxt m) x y,
    y > 0 ->
    x < m + n ->
    (m + n)[x ↦ y] = c ⊗ (zero n)
    ->
      x < m.
Proof.
  intros.
  apply fun_apply with (x:=x) in H1.
  unfold delta, ctxt_app, zero, flat_ctxt in H1.
  destruct (lt_dec x (m + n)); auto.
  destruct (Nat.eq_dec x x); try lia.
  destruct (lt_dec x m); try lia.
  destruct (lt_dec x m); try lia.
Qed.

Lemma app_delta_zero_inv_lt_eq :
  forall n m (c : lctxt m) x y,
    y <> 0 ->
    x < m + n ->
    (m + n)[x ↦ y] ≡[m + n] c ⊗ (zero n)
    ->
      x < m.
Proof.
  unfold ctxt_eq.
  intros.
  specialize (H1 x H0).
  unfold delta, ctxt_app, zero, flat_ctxt in H1.
  destruct (lt_dec x (m + n)); auto.
  destruct (Nat.eq_dec x x); try lia.
  destruct (lt_dec x m); try lia.
  destruct (lt_dec x m); try lia.
Qed.

Lemma app_delta_zero_inv_ctxt :
  forall n m (c : lctxt m) x y,
    y <> 0 ->
    x < m + n ->
    (m + n)[x ↦ y] ≡[m+n] c ⊗ (zero n)
    ->
      (m[x ↦ y]) ≡[m] c.
Proof.
  unfold ctxt_eq.
  intros.
  assert (x < m). { eapply app_delta_zero_inv_lt_eq; eauto. } 
  assert (x0 < m + n) by lia.
  specialize (H1 x0 H4).
  unfold delta, ctxt_app, zero, flat_ctxt in *.
  destruct (lt_dec x m); try lia.
  destruct (lt_dec x (m + n)); try lia.
  destruct (Nat.eq_dec x x0); try lia.
  destruct (lt_dec x0 m); try lia.
  destruct (lt_dec x0 m); try lia.
Qed.

Lemma delta_app_zero_r :
  forall m n x y,
    x < m ->
    (@ctxt_app _ m n (m[x ↦ y]) (zero n)) = (m + n)[x ↦ y].
Proof.
intros.
apply functional_extensionality.
unfold ctxt_app, delta, zero, flat_ctxt.
intros x0. 
destruct (lt_dec x0 m).
destruct (lt_dec x m); try lia.
destruct (Nat.eq_dec x x0).
destruct (lt_dec x (m+n)); try lia.
destruct (lt_dec x (m+n)); try lia. 
destruct (lt_dec x (m+n)); try lia. 
destruct (Nat.eq_dec x x0); try lia.
Qed.

Lemma delta_app_zero_l :
  forall m n x y,
    x < m ->
    (@ctxt_app _ n m (zero n) (m[x ↦ y]) ) = (n + m)[(n + x) ↦ y].
Proof.
intros.
apply functional_extensionality.
unfold ctxt_app, delta, zero, flat_ctxt.
intros x0. 
destruct (lt_dec x0 n).
destruct (lt_dec (n+x) (n+m)); try lia.
destruct (Nat.eq_dec (n+x) x0); try lia.
destruct (lt_dec x m); try lia.
destruct (Nat.eq_dec x (x0-n)); try lia.
destruct (lt_dec (n+x) (n+m)); try lia.
destruct (Nat.eq_dec (n+x) x0); try lia.
destruct (lt_dec (n+x) (n+m)); try lia.
destruct (Nat.eq_dec (n+x) x0); try lia.
Qed.


(* One piece of an Ltac definition that might be useful below *)
Ltac destruct_Nat_eq_decs :=
  match goal with
    [ |- ctxt(Nat.eq_dec ?R1 ?R2) ] => destruct (Nat.eq_dec R1 R2); try lia
  end.

(*
I don't know if this is the most elegant approach, and it did take quite some time to run
'all: destruction.' the first time I stepped through the proof.
*)
Ltac destruction :=
 repeat match goal with
           | [ |- context[lt_dec ?R1 ?R2] ] => destruct (lt_dec R1 R2); try lia
           | [ |- context[Nat.eq_dec ?R1 ?R2] ] => destruct (Nat.eq_dec R1 R2); try lia
           end. 

Lemma lctxt_sum_3_inv1 : forall n' n r r1 r2 r1' r2' (D : lctxt n'),
    ((n' + n) [r ↦ 1] ⨥ ((n' + n) [r1 ↦ 1] ⨥ (n' + n) [r2 ↦ 1]))
      ⨥ ((n' + n) [r ↦ 1] ⨥ ((n' + n) [r1' ↦ 1] ⨥ (n' + n) [r2' ↦ 1])) = D ⊗ zero n
    ->
        D ≡[n'] ((n')[r ↦ 2] ⨥ ((n')[r1 ↦ 1] ⨥ ((n') [r1' ↦ 1] ⨥ ((n') [r2 ↦ 1] ⨥ (n') [r2' ↦ 1])))).
Proof.
unfold ctxt_eq.
intros.
apply fun_apply with (x:=x) in H.
unfold ctxt_app, delta, sum in *.
unfold zero, flat_ctxt in H.
symmetry in H; destruct (lt_dec x n').
- repeat match goal with
           | [ |- _ ] => destruct (lt_dec _ (n' + n)) in H; try lia
           | [ |- _ ] => destruct (Nat.eq_dec _ _) in H; try lia
           end.
  (* FRAN: Admitted here to quicken make *)
  (* all : destruction. *)
  all: admit.
- lia.
Admitted.    




    
