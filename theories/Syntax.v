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

From LEpic Require Import Contexts.
Import Renamings.

Local Open Scope program_scope.
Local Open Scope bool_scope.

(* Helpful tactic for destructing hypotheses succinctly *)
Ltac dest_conj_disj_exist :=
  repeat match goal with
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  end.


(* Raw de Bruijn Syntax ------------------------------------------------------ *)

(* Terms are represented using de Bruijn indexes.

   There are two types of identifiers:

   Unrestricted (a.k.a. non-linear) Identifiers
    - these represent names of lambdas
    - by convention, we use [m : nat] to represent the number of such 
      identifies in scope within a term
    - we use [f] (for "function") and variants as the metavariable
      for writing down function identifiers

   Linear Identifiers
    - these represent "cuts" or "resource names" in the semantics
    - by convention, we use [n : nat] to represent the number of such
      identifiers in scope within a term
    - we use [r] (for "resource") and variants as the metavariable
      for writing down function identifiers 

   # Terms:

   A "term" [t] is a "bag" [bag m n P], consisting of a processes [P]. 
   It binds [m] (fresh) function identifiers and [n] (fresh) resource
   identifiers.

   # Processes:

   A process [P] is one of:
     - a definition [def r o] (written informally as "r <- o"),
       which defines the resource [r] as the operand [o]

     - a function application [f r].  Functions always take one
       argument, [r], and the function identifer [f] should be
       bound to a lambda somwehere in the context

     - two processes running "in parallel": [par P1 P2]

     - a null process: [nul]. Null does no computation,
       acting as the unit to par.

   # Operands:

   An operand [o] provides a definition of a resource identifier and
   can be one of:

     - emp          the empty tuple ()
     - [tup r1 r2]  a "tuple" (pair) of resources
     - [bng f]      the name of a function
     - [lam t]      an lambda, which is a term exactly one free resource


  (* SAZ: We could contemplate defining Rocq notations for terms. *) 

*)

Definition rvar := nat.
Definition fvar := nat.

Inductive term :=
| bag (m n:nat) (P:proc)   (* nu. {f1...fm} {r1..rn} P *)

with proc :=
| def (r:rvar) (o:oper)  (* r <- o *)
| app (f:fvar) (r:rvar)  (* f r *)
| par (P1 P2 : proc)     (* P1 | P2 *)
| nul

with oper :=
| emp                    (* empty tuple *)
| tup (r1 r2:rvar)       (* (r1,r2) *)
| bng (f:fvar)           (* !f *)
| lam (t : term).        (* lam r. t *)

Scheme term_ind_m := Induction for term Sort Prop
  with proc_ind_m := Induction for proc Sort Prop
  with oper_ind_m := Induction for oper Sort Prop.
Combined Scheme tpo_ind from term_ind_m, proc_ind_m, oper_ind_m.

Scheme term_rect_m := Induction for term Sort Type
  with proc_rect_m := Induction for proc Sort Type
  with oper_rect_m := Induction for oper Sort Type.
Combined Scheme tpo_rect from term_rect_m, proc_rect_m, oper_rect_m.

Scheme term_rec_m := Induction for term Sort Set
  with proc_rec_m := Induction for proc Sort Set
  with oper_rec_m := Induction for oper Sort Set.
Combined Scheme tpo_rec from term_rec_m, proc_rec_m, oper_rec_m.

(* Projects the term components *)
Definition get_fvars t := match t with bag m _ _ => m end.
Definition get_rvars t := match t with bag _ n _ => n end.
Definition get_proc t := match t with bag _ _ P => P end.


(* Scoping *)

(* Well scoping - just checks that de Bruijn variables are in bounds.

   [ws_term m n t] means that term [t] is well-scoped with at most
   [m] function identifiers and [n] resource identifiers.

   (and similarly for [ws_proc] and [ws_oper]).

   A de Bruijn variable is "in scope" if it is less than the number
   of variables in the context.
 *)
Unset Elimination Schemes.
Inductive ws_term : nat -> nat -> term -> Prop :=
| ws_bag :
  forall m n
    m' n'
    P
    (WS : ws_proc (m' + m) (n' + n) P),
    ws_term m n (bag m' n' P)

with ws_proc : nat -> nat -> proc -> Prop :=
| ws_def :
  forall m n
    (r : rvar) (HR : r < n)
    (o : oper) (WSO : ws_oper m n o),
    ws_proc m n (def r o)

| ws_app :
  forall m n
    (f : fvar) (HF : f < m)
    (r : rvar) (HR : r < n),
    ws_proc m n (app f r)

| ws_par :
  forall m n
    (P1 P2 : proc)
    (WSP1 : ws_proc m n P1)
    (WSP2 : ws_proc m n P2),
    ws_proc m n (par P1 P2)

| ws_nul :
  forall m n,
    ws_proc m n nul
            
with ws_oper : nat -> nat -> oper -> Prop :=
|ws_emp :
  forall m n,
    ws_oper m n emp

| ws_tup :
  forall m n
    (r1 : rvar) (HR1 : r1 < n)
    (r2 : rvar) (HR2 : r2 < n),
    ws_oper m n (tup r1 r2)

| ws_bng :
  forall m n
    (f : fvar)
    (HF : f < m),
    ws_oper m n (bng f)
            
| ws_lam :
  forall m n
    (t : term)
    (WST : ws_term m 1 t),
    ws_oper m n  (lam t).
Set Elimination Schemes.

Scheme ws_term_ind := Induction for ws_term Sort Prop
    with ws_proc_ind := Induction for ws_proc Sort Prop
                        with ws_oper_ind := Induction for ws_oper Sort Prop.

Combined Scheme ws_tpo_ind from ws_term_ind, ws_proc_ind, ws_oper_ind.



(* Structural Equivalence --------------------------------------------------- *)

(* Defines "structural" equivalence of the syntax.  The syntax is considered
   up to reordering of the process components within a bag.  That is,
   we can permute and re-associate the [par] operator.

   Note that such permutations do not affect the meaning of de Bruijn
   indices.

   These relations define equivalence relations on syntax.
 *)

Inductive seq_term : term -> term -> Prop :=
| seq_bag :
  forall m n P1 P2,
    seq_proc P1 P2 ->
    seq_term (bag m n P1) (bag m n P2)

with seq_proc : proc -> proc -> Prop :=
| seq_proc_refl :
  forall (P : proc),
    seq_proc P P

| seq_proc_symm :
  forall P1 P2,
    seq_proc P1 P2 ->
    seq_proc P2 P1
             
| seq_proc_trans :
  forall P1 P2 P3,
    seq_proc P1 P2 ->
    seq_proc P2 P3 ->
    seq_proc P1 P3
             
| seq_par_comm :
  forall (P1 P2 : proc),
    seq_proc (par P1 P2) (par P2 P1)

| seq_par_assoc1 :
  forall (P1 P2 P3 : proc),
    seq_proc (par P1 (par P2 P3)) (par (par P1 P2) P3)

| seq_par_assoc2 :
  forall (P1 P2 P3 : proc),
    seq_proc (par (par P1 P2) P3) (par P1 (par P2 P3))
             
| seq_par_cong :
  forall P1 P1' P2 P2',
    seq_proc P1 P1' ->
    seq_proc P2 P2' ->
    seq_proc (par P1 P2) (par P1' P2')

| seq_def :
  forall r o1 o2,
    seq_oper o1 o2 ->
    seq_proc (def r o1) (def r o2)
             
with seq_oper : oper -> oper -> Prop :=
| seq_oper_refl :
  forall o,
    seq_oper o o

| seq_lam :
  forall t1 t2,
    seq_term t1 t2 ->
    seq_oper (lam t1) (lam t2)
.

Scheme seq_term_mut_ind := Induction for seq_term Sort Prop
    with seq_proc_mut_ind := Induction for seq_proc Sort Prop
                        with seq_oper_mut_ind := Induction for seq_oper Sort Prop.

Combined Scheme seq_tpo_ind from seq_term_mut_ind, seq_proc_mut_ind, seq_oper_mut_ind.

Hint Constructors seq_term seq_proc seq_oper : core.

Infix "≈t" := seq_term (at level 55).
Infix "≈p" := seq_proc (at level 55).
Infix "≈o" := seq_oper (at level 55).



(* Proving Structural Equivalence is Refl/Symm/Trans *)

Lemma tpo_seq_reflexive :
  (forall (t : term), t ≈t t) /\
    (forall (P : proc), P ≈p P) /\
    (forall (o : oper), o ≈o o).
Proof.
  apply tpo_ind; intros; auto.
Qed.

#[global] Instance Reflexive_seq_term : Reflexive (seq_term).
Proof. unfold Reflexive. apply tpo_seq_reflexive. Qed.
#[global] Instance Reflexive_seq_proc : Reflexive (seq_proc).
Proof. unfold Reflexive. apply tpo_seq_reflexive. Qed.
#[global] Instance Reflexive_seq_oper : Reflexive (seq_oper).
Proof. unfold Reflexive. apply tpo_seq_reflexive. Qed.

Lemma tpo_seq_transitive :
  (forall (t1 t2 t3 : term), t1 ≈t t2 -> t2 ≈t t3 -> t1 ≈t t3) /\
    (forall (P1 P2 P3 : proc), P1 ≈p P2 -> P2 ≈p P3 -> P1 ≈p P3) /\
    (forall (o1 o2 o3 : oper), o1 ≈o o2 -> o2 ≈o o3 -> o1 ≈o o3).
Proof.
  apply tpo_ind; intros.
  (* Process Equivalence is transitive by construction *)
  all: try solve [eapply seq_proc_trans; eauto].
  (* Operand Equivalence, excepting lambdas, has only the refl constructor *)
  all: try solve [inversion H; subst; inversion H0; subst; reflexivity].
  (* Bag Equivalence *)
  - inversion H0; subst.
    inversion H1; subst.
    constructor. eapply H; eauto.
  (* Lambda Equivalence *)
  - inversion H1; subst; auto.
    inversion H0; subst; auto.
    econstructor.
    eapply H; eauto.
Qed.

#[global] Instance Transitive_seq_term : Transitive (seq_term).
Proof. unfold Transitive. apply tpo_seq_transitive. Qed.
#[global] Instance Transitive_seq_proc : Transitive (seq_proc).
Proof. unfold Transitive. apply tpo_seq_transitive. Qed.
#[global] Instance Transitive_seq_oper : Transitive (seq_oper).
Proof. unfold Transitive. apply tpo_seq_transitive. Qed.

Lemma tpo_seq_symmetric :
  (forall (t1 t2 : term), t1 ≈t t2 -> t2 ≈t t1) /\
    (forall (P1 P2 : proc), P1 ≈p P2 -> P2 ≈p P1) /\
    (forall (o1 o2 : oper), o1 ≈o o2 -> o2 ≈o o1).
Proof.
  apply tpo_ind; intros; auto.
  (* Process Equivalence is symmetric by construction (via auto) *)
  (* Operand Equivalence, excepting lambdas, has only the refl constructor *)
  all: try solve [inversion H; reflexivity].
  (* Bag Equivalence *)
  - inversion H0; subst.
    constructor. apply H. assumption.
  (* Lambda Equivalence *)
  - inversion H0; subst; auto.
Qed.

#[global] Instance Symmetric_seq_term : Symmetric (seq_term).
Proof. unfold Symmetric. apply tpo_seq_symmetric. Qed.
#[global] Instance Symmetric_seq_proc : Symmetric (seq_proc).
Proof. unfold Symmetric. apply tpo_seq_symmetric. Qed.
#[global] Instance Symmetric_seq_oper : Symmetric (seq_oper).
Proof. unfold Symmetric. apply tpo_seq_symmetric. Qed.



(* structural equivalence "inversion" lemmas:
   - these lemmas extract information about the structure of a
     piece of syntax that is known to be structurally equivalent
     to a more defined piece of syntax.
 *)

Lemma seq_proc_inv_def' : forall P1 P2,
    P1 ≈p P2 ->
    (forall r o, P1 = def r o -> exists o', P2 = def r o' /\ o ≈o o') /\
      (forall r o, P2 = def r o -> exists o', P1 = def r o' /\ o ≈o o').
Proof.
  intros P1 P2 H.
  induction H.
  (* Equivalence cases unapplicable to def processes *)
  all: try solve [split; try clear H; intros; discriminate H].
  (* Reflexivity *)
  - split; intros; exists o; auto.
  (* Symmetry *)
  - split; intros; apply IHseq_proc in H0; auto.
  (* Transitivity *)
  - split; intros. 
    + apply IHseq_proc1 in H1.
      destruct H1 as [o' [HP2 Ho']].
      apply IHseq_proc2 in HP2.
      destruct HP2 as [o'' [HP3 Ho'']].
      exists o''. split; eauto. eapply transitivity; eauto.
    + apply IHseq_proc2 in H1.
      destruct H1 as [o' [HP2 Ho']].
      apply IHseq_proc1 in HP2.
      destruct HP2 as [o'' [HP3 Ho'']].
      exists o''. split; eauto. eapply transitivity; eauto.
  (* Def Congruence *)
  - split; intros.
    + inversion H0. subst. exists o2. split; auto.
    + inversion H0. subst. exists o1. split; auto.
      apply symmetry.
      assumption.
Qed.

Lemma seq_proc_inv_def_l : forall P o r,
    P ≈p def r o -> exists o', P = def r o' /\ o ≈o o'.
Proof.
  intros.
  apply seq_proc_inv_def' in H.
  destruct H as [_ H].
  apply H. reflexivity.
Qed.  

Lemma seq_proc_inv_def_r : forall P o r,
    def r o ≈p P -> exists o', P = def r o' /\ o ≈o o'.
Proof.
  intros.
  apply seq_proc_inv_def' in H.
  destruct H as [H _].
  apply H. reflexivity.
Qed.  

Lemma seq_proc_inv_app' : forall P1 P2,
    P1 ≈p P2 ->
    (forall f r, P1 = app f r -> P2 = app f r) /\
      (forall f r, P2 = app f r -> P1 = app f r).
Proof.
  intros P1 P2 H.
  induction H.
  (* Equivalence cases unapplicable to app processes *)
  all: try solve [split; try clear H; intros; discriminate H].
  (* Reflexivity *)
  - split; intros; auto.
  (* Symmetry *)
  - split; intros; subst.
    + eapply IHseq_proc; auto.
    + eapply IHseq_proc; auto.
  (* Transitivity *)
  - split; intros.
    + eapply IHseq_proc2.
      eapply IHseq_proc1.
      auto.
    + eapply IHseq_proc1.
      eapply IHseq_proc2.
      auto.
Qed.    

Lemma seq_proc_inv_app_l : forall f r P,
    P ≈p app f r -> P = app f r.
Proof.
  intros.
  apply seq_proc_inv_app' in H.
  apply H.
  reflexivity.
Qed.

Lemma seq_proc_inv_app_r : forall f r P,
    app f r ≈p P -> P = app f r.
Proof.
  intros.
  apply seq_proc_inv_app' in H.
  apply H.
  reflexivity.
Qed.



(* Well Formedness ---------------------------------------------------------- *)

(* These relations check the useage (linearity / definition) constraints as well
   as scoping of the variables.

   The type [lctxt k] defines a "linearity context" for [k] de Bruijn variables
   it maps each identifier to its "usage", i.e. the number of times it is "used"
   in the scope.

   # Unrestricted Contexts: [G]

   By convention, we use [G] (or maybe [Γ] on paper) to range over unrestricted
   identifier contexts.

    Within a given scope, each unrestricted identifer [f] must be *defined*
   (i.e. appear under a [bng]) exactly once, though it may be called an
   arbitrary number of times.  The usage for each [f] is therefore the
   number of times it is *defined* in a scope.  (We will need a separate judgment
   to determine whether a given [f] is not used at all, which will justify
   a "garbage collection" rule for unrestricted contexts.)

   # Restricted / Linear Contexts: [D]

   By convention, we use [D] (or maybe [Δ] on paper) to range over unrestricted
   identifier contexts.

   Within a given scope, each linear / restricted identifier [r] must be
   mentioned exactly twice.  (Or not mentioned at all.)  Unlike for 
   [f]'s, if [D r = 0] then there should be no occurrence of the restricted
   variable in a given scope, and we can immediately "strengthen" the
   context to discard it.
 *)

Unset Elimination Schemes.

(* (wf_term m n t) iff t is a well-formed bag with:
    1) m free and *undefined* unrestricted variables
    2) n free restricted variables appearing *exactly* once in t

  G and D track free variables that may occur.
  Free function variables (in G) should not be defined and so mapped to 0,
  and free resource variables (in D) should appear exactly once. *)
Inductive wf_term : forall (m n:nat), term -> Prop :=
| wf_bag :
  forall m n m' n'
    (G : lctxt m) (D : lctxt n)
    (UG : forall x, x < m -> (G x) = 1)
    (UD : forall x, x < n -> (D x) = 2 \/ (D x) = 0)
    (P : proc)
    (WFP : wf_proc (m + m') (n + n') (G ⊗ (zero m')) (D ⊗ (flat_ctxt 1 n')) P),
    wf_term m' n' (bag m n P)

with wf_proc : forall (m n:nat), lctxt m -> lctxt n -> proc -> Prop :=
| wf_def :
  forall m n
    (G : lctxt m)
    (D D' : lctxt n)
    (r : rvar) (HR : r < n)
    (o : oper)
    (HD : D ≡[n] (one n r) ⨥ D')
    (WFO : wf_oper m n G D' o),
    wf_proc m n G D (def r o)

| wf_app :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (f : fvar) (HF : f < m)
    (r : rvar) (HR : r < n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (one n r)),
    wf_proc m n G D (app f r)

| wf_par :
  forall m n
    (G1 G2 G : lctxt m)
    (D1 D2 D : lctxt n)
    (P1 P2 : proc)
    (WFP1 : wf_proc m n G1 D1 P1)
    (WFP2 : wf_proc m n G2 D2 P2)
    (HG : G ≡[m] (G1 ⨥ G2))
    (HD : D ≡[n] (D1 ⨥ D2)),
    wf_proc m n G D (par P1 P2)

| wf_nul :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (zero n)),
    wf_proc m n G D nul
            
with wf_oper : forall (m n:nat), lctxt m -> lctxt n -> oper -> Prop :=
| wf_emp :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (zero n)),
    wf_oper m n G D emp

| wf_tup :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (r1 : rvar) (HR1 : r1 < n)
    (r2 : rvar) (HR2 : r2 < n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (one n r1 ⨥ one n r2)),
    wf_oper m n G D (tup r1 r2)

| wf_bng :
  forall m n
    (G : lctxt m) (D : lctxt n)    
    (f : fvar)
    (HF : f < m)
    (HG : G ≡[m] (one m f))
    (HD : D ≡[n] (zero n)),
    wf_oper m n G D (bng f)
            
| wf_lam :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (zero n))
    (t : term)
    (WFT : wf_term m 1 t),
    wf_oper m n G D (lam t).
Set Elimination Schemes.

Scheme wf_term_ind := Induction for wf_term Sort Prop
    with wf_proc_ind := Induction for wf_proc Sort Prop
                        with wf_oper_ind := Induction for wf_oper Sort Prop.

Combined Scheme wf_tpo_ind from wf_term_ind, wf_proc_ind, wf_oper_ind.

(* A helpful tactic for dealing with equivalences of existT terms that
   arise when inverting wf judgments. *)
Ltac existT_eq :=
      repeat match goal with 
      | [H : existT _ _ _ = existT _ _ _ |- _ ] =>
          apply Eqdep_dec.inj_pair2_eq_dec in H; [| apply Nat.eq_dec]
      end.



(* Prove that well-formedness respects structural equivalence. *)

(* It seems that the trick for this proof is to close under commutatitivy explicitly. *)
Lemma tpo_wf_seq :
  (forall t1 t2,
      t1 ≈t t2 ->
     (forall m n,
      wf_term m n t1 ->
      wf_term m n t2)
     /\
     (forall m n,
      wf_term m n t2 ->
      wf_term m n t1))
       
  /\
  (forall P1 P2,
      P1 ≈p P2 ->
      (forall m n G D,
          wf_proc m n G D P1 ->
          wf_proc m n G D P2)

      /\
        (forall m n G D,
          wf_proc m n G D P2 ->
          wf_proc m n G D P1))
  /\
  (forall o1 o2,
      o1 ≈o o2 ->
      (forall m n G D,
          wf_oper m n G D o1 ->
          wf_oper m n G D o2)
      /\
      (forall m n G D,
          wf_oper m n G D o2 ->
          wf_oper m n G D o1)).
Proof.
  apply seq_tpo_ind; intros.
  (* Reflexive and Symmetric Eq cases *)
  all: try solve [tauto].
  (* Congruence cases *)
  all: try solve [
    destruct H as [HL1 HR1];
    try destruct H0 as [HL2 HR2];
    split; intros;
    inversion H; existT_eq; subst;
    econstructor; eauto
  ].
  (* Process Eq Transitive *)
  - destruct H as [HL1 HR1].
    destruct H0 as [HL2 HR2].
    split; intros.
    + apply HL2. apply HL1. assumption.
    + apply HR1. apply HR2. assumption.
  (* Par Commute *)
  - split; intros.
    all: inversion H; existT_eq; subst.
    all: rewrite sum_commutative in HG; rewrite (@sum_commutative _ D1 D2) in HD.
    all: eapply wf_par; eauto.
  (* Par Associate 1 *)
  - split; intros.
    all: inversion H; subst. 
    + inversion WFP2; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      * reflexivity.
      * reflexivity.
      * rewrite <- sum_assoc. rewrite <- HG0. assumption.
      * rewrite <- sum_assoc. rewrite <- HD0. assumption.
    + inversion WFP1; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      * reflexivity.
      * reflexivity.
      * rewrite sum_assoc. rewrite <- HG0. assumption.
      * rewrite sum_assoc. rewrite <- HD0. assumption.
  (* Par Associate 2 (mostly same as above) *)
  - split; intros.
    all: inversion H; subst. 
    + inversion WFP1; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      * reflexivity.
      * reflexivity.
      * rewrite sum_assoc. rewrite <- HG0. assumption.
      * rewrite sum_assoc. rewrite <- HD0. assumption.
    + inversion WFP2; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      * reflexivity.
      * reflexivity.
      * rewrite <- sum_assoc. rewrite <- HG0. assumption.
      * rewrite <- sum_assoc. rewrite <- HD0. assumption.
Qed.

Lemma wf_seq_term : forall t1 t2 m n, 
  t1 ≈t t2 -> wf_term m n t1 -> wf_term m n t2.
Proof. intros t1 t2 m n H; generalize t1 t2 H m n. apply tpo_wf_seq. Qed.
Lemma wf_seq_proc : forall P1 P2 m n G D, 
  P1 ≈p P2 -> wf_proc m n G D P1 -> wf_proc m n G D P2.
Proof. intros P1 P2 m n G D H; generalize P1 P2 H m n G D. apply tpo_wf_seq. Qed.
Lemma wf_seq_oper : forall o1 o2 m n G D, 
  o1 ≈o o2 -> wf_oper m n G D o1 -> wf_oper m n G D o2.
Proof. intros o1 o2 m n G D H; generalize o1 o2 H m n G D. apply tpo_wf_seq. Qed.



(* Prove that well-formedness respects context equivalence. *)
Lemma tpo_equiv_wf :
(* The first element is trivial, but allows using wf_tpo_ind *)
  (forall m n t,
    wf_term m n t ->
      True)
  /\
  (forall m n G1 D1 P,
    wf_proc m n G1 D1 P ->
      forall G2 D2,
    G1 ≡[m] G2 ->
    D1 ≡[n] D2 ->
      wf_proc m n G2 D2 P)
  /\
  (forall m n G1 D1 o,
    wf_oper m n G1 D1 o ->
      forall G2 D2,
    G1 ≡[m] G2 ->
    D1 ≡[n] D2 ->
      wf_oper m n G2 D2 o).
Proof.
  apply wf_tpo_ind; intros.
  (* All cases are by transitivity:
      from G1 ≡[m] G2 in the premise and G1 ≡[m] ?G from inverting wf, 
      we get G2 ≡[m] ?G to reconstruct wf *)
  all:
    econstructor; eauto;
    try (eapply transitivity; eauto; symmetry; eauto).
  (* Rocq needs help for Def *)
  - apply H; auto. reflexivity.
Qed.  

#[global] Instance Proper_wf_proc {m n : nat} : Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> seq_proc ==> iff) (wf_proc m n).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply tpo_equiv_wf; eauto.
    eapply wf_seq_proc; eauto.
  - symmetry in H, H0, H1.
    eapply tpo_equiv_wf; eauto.
    eapply wf_seq_proc; eauto.
Qed.

#[global] Instance Proper_wf_oper {m n : nat} : Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> seq_oper ==> iff) (wf_oper m n).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply tpo_equiv_wf; eauto.
    eapply wf_seq_oper; eauto.
  - symmetry in H, H0, H1.
    eapply tpo_equiv_wf; eauto.
    eapply wf_seq_oper; eauto.
Qed.



(* Expressions have unique contexts that make them well-formed. *)
Lemma tpo_unique_wf :
(* The first element is trivial, but allows using wf_tpo_ind *)
  (forall m n t,
    wf_term m n t ->
      True)
  /\
  (forall m n G1 D1 P,
    wf_proc m n G1 D1 P ->
      forall G2 D2,
    wf_proc m n G2 D2 P ->
      G1 ≡[m] G2 /\ D1 ≡[n] D2)
  /\
  (forall m n G1 D1 o,
    wf_oper m n G1 D1 o ->
      forall G2 D2,
    wf_oper m n G2 D2 o ->
      G1 ≡[m] G2 /\ D1 ≡[n] D2).
Proof.
  apply wf_tpo_ind; intros.
  (* Most cases are by inversion on the other wf judgment *)
  all: try solve 
    [try inversion H; try inversion H0; existT_eq; subst;
    try rewrite HG, HD, HG0, HD0;
    split; auto; reflexivity].
  (* Def and Par also require IH *)
  - inversion H0; existT_eq; subst. 
    apply H in WFO0; destruct WFO0.
    rewrite HD0, <- H1, <- H2. split; auto; reflexivity.
  - inversion H1; existT_eq; subst. 
    rewrite HG, HD, HG0, HD0. 
    apply H in WFP0; apply H0 in WFP3; destruct WFP0, WFP3.
    rewrite H2, H3, H4, H5.
    split; auto; reflexivity.
Qed.

Lemma unique_wf_proc : (forall m n G1 D1 P, wf_proc m n G1 D1 P -> 
  forall G2 D2, wf_proc m n G2 D2 P -> G1 ≡[m] G2 /\ D1 ≡[n] D2).
Proof. apply tpo_unique_wf. Qed.
Lemma unique_wf_oper : (forall m n G1 D1 o, wf_oper m n G1 D1 o -> 
  forall G2 D2, wf_oper m n G2 D2 o -> G1 ≡[m] G2 /\ D1 ≡[n] D2).
Proof. apply tpo_unique_wf. Qed.



(* Every well formed piece of syntax is also well scoped *)
Lemma tpo_wf_ws :
  (forall m n t,
      wf_term m n t ->
      ws_term m n t)
  /\
  (forall m n G D P,
      wf_proc m n G D P ->
      ws_proc m n P)
  /\
  (forall m n G D o,
      wf_oper m n G D o ->
      ws_oper m n o).
Proof.
  apply wf_tpo_ind; intros. 
  (* All cases are trivial *)
  all: constructor; auto.
Qed.  

Lemma wf_ws_term : (forall m n t, wf_term m n t -> ws_term m n t).
Proof. apply tpo_wf_ws. Qed.
Lemma wf_ws_proc : (forall m n G D P, wf_proc m n G D P -> ws_proc m n P).
Proof. apply tpo_wf_ws. Qed.
Lemma wf_ws_oper : (forall m n G D o, wf_oper m n G D o -> ws_oper m n o).
Proof. apply tpo_wf_ws. Qed.



(* renaming ----------------------------------------------------------------- *)

(* The operational semantics involve renaming resource identifiers.

   Renamings, in general, are defined in [Contexts.v], but for de Bruijn
   indices, a renaming amounts to a function that takes a variable and
   returns a variable.

   The type [ren n n'] "renames" a variable in scope [n] to be a variable
   in scope [n'].  (In general, [n] and [n'] might be different.)

   The following functions just "map" a renaming over all the occurrences
   of the (free) identifiers in a term.
*)

(* z{y/x} *)
Definition rename_var (x:var) (y:var) (z:var) :=
  if Nat.eq_dec z x then y else z.

(* Linear resource variables are only locally scoped within the bag
   of a term, so operations that rename them don't need to traverse
   nested subterms.
 *)
    
Definition rename_rvar_oper {n n'} (v : ren n n') (o:oper) :=
  match o with
  | emp => emp
  | tup r1 r2 => tup (v r1) (v r2)
  | bng f => bng f
  | lam t => lam t
  end.

Fixpoint rename_rvar_proc {n n'} (v : ren n n') P : proc :=
  match P with
  | def r o => def (v r) (rename_rvar_oper v o)
  | app f r => app f (v r)
  | par P1 P2 => par (rename_rvar_proc v P1) (rename_rvar_proc v P2)
  | nul => nul
  end.

Definition rename_rvar_term {n n'} (v : ren n n') (t : term) :=
  match t with
  | bag m n'' P => bag m n'' (rename_rvar_proc (ren_shift n'' v) P)
  end.

(* Unrestricted identifiers *are* lexically scoped in the sense
   that an identifier introduced in an outer scope might be mentioned
   in an inner, nested term (e.g. under a [lam]).  That means
   we have to "shift" renamings as we traverse through the syntax,
   ensuring that we only rename the "free" occurences.
*)

Fixpoint rename_fvar_term {m m'} (v : ren m m') (t : term) : term :=
  match t with
  | bag m'' n P => bag m'' n (rename_fvar_proc (ren_shift m'' v) P)
  end

with rename_fvar_proc {m m'} (v : ren m m') (P : proc) : proc :=
  match P with
  | def r o => def r (rename_fvar_oper v o)
  | app f r => app (v f) r
  | par P1 P2 => par (rename_fvar_proc v P1) (rename_fvar_proc v P2)
  | nul => nul
  end

with rename_fvar_oper {m m'} (v : ren m m') (o : oper) : oper :=
  match o with
  | emp => emp
  | tup r1 r2 => tup r1 r2
  | bng f => bng (v f)
  | lam t => lam (rename_fvar_term v t)
  end.



(* Renamings can be composed *)
Lemma rename_rvar_compose_tpo : 
  (forall (t : term) n n' n'' (v1 : ren n n') (v2 : ren n' n''),
      rename_rvar_term v2 (rename_rvar_term v1 t) = @rename_rvar_term n n'' (ren_compose v1 v2) t)
  /\
  (forall (P : proc) n n' n'' (v1 : ren n n') (v2 : ren n' n''),
       rename_rvar_proc v2 (rename_rvar_proc v1 P) = @rename_rvar_proc n n'' (ren_compose v1 v2) P)
  /\
  (forall (o : oper) n n' n'' (v1 : ren n n') (v2 : ren n' n''),
      rename_rvar_oper v2 (rename_rvar_oper v1 o) = @rename_rvar_oper n n'' (ren_compose v1 v2) o).
Proof.
  apply tpo_ind; intros; simpl. 
  (* Aside from Bag, all cases are by IH(s) *)
  all: try solve [try rewrite H; try rewrite H0; reflexivity].
  (* Bag needs to shift the names *)
  - rewrite <- ren_compose_shift.
    rewrite <- H.
    reflexivity.
Qed.

Lemma rename_fvar_compose_tpo :
  (forall (t:term),
    forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
      rename_fvar_term v2 (rename_fvar_term v1 t) = @rename_fvar_term m m'' (ren_compose v1 v2) t)
  /\
  (forall (P:proc),
    forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
      rename_fvar_proc v2 (rename_fvar_proc v1 P) = @rename_fvar_proc m m'' (ren_compose v1 v2) P)
  /\ 
  (forall (o:oper),
    forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
      rename_fvar_oper v2 (rename_fvar_oper v1 o) = @rename_fvar_oper m m'' (ren_compose v1 v2) o).
Proof.
  apply tpo_ind; intros; simpl. 
  (* Aside from Bag, all cases are by IH(s) *)
  all: try solve [try rewrite H; try rewrite H0; reflexivity].
  (* Bag needs to shift the names *)
  - rewrite <- ren_compose_shift.
    rewrite <- H.
    reflexivity.
Qed.

Lemma rename_rvar_term_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (t : term),
    rename_rvar_term v2 (rename_rvar_term v1 t) = @rename_rvar_term n n'' (ren_compose v1 v2) t.
Proof. intros; apply rename_rvar_compose_tpo. Qed.
Lemma rename_rvar_proc_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (P : proc),
    rename_rvar_proc v2 (rename_rvar_proc v1 P) = @rename_rvar_proc n n'' (ren_compose v1 v2) P.
Proof. intros; apply rename_rvar_compose_tpo. Qed.
Lemma rename_rvar_oper_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (o : oper),
    rename_rvar_oper v2 (rename_rvar_oper v1 o) = @rename_rvar_oper n n'' (ren_compose v1 v2) o.
Proof. intros; apply rename_rvar_compose_tpo. Qed.

Lemma rename_fvar_compose_term : forall m m' m'' (v1 : ren m m') (v2 : ren m' m'') (t : term),
      rename_fvar_term v2 (rename_fvar_term v1 t) = @rename_fvar_term m m'' (ren_compose v1 v2) t.
Proof. intros; apply rename_fvar_compose_tpo. Qed.
Lemma rename_fvar_compose_proc : forall m m' m'' (v1 : ren m m') (v2 : ren m' m'') (P : proc),
    rename_fvar_proc v2 (rename_fvar_proc v1 P) = @rename_fvar_proc m m'' (ren_compose v1 v2) P.
Proof. intros; apply rename_fvar_compose_tpo. Qed.
Lemma rename_fvar_compose_oper : forall m m' m'' (v1 : ren m m') (v2 : ren m' m'') (o : oper),
    rename_fvar_oper v2 (rename_fvar_oper v1 o) = @rename_fvar_oper m m'' (ren_compose v1 v2) o.
Proof. intros; apply rename_fvar_compose_tpo. Qed.

  

(* Renamings of linear and unrestricted variables commute with each other. *) 

Lemma rename_rvar_fvar_commute_tpo :
  (forall (t:term),
    forall m m' n n' (fv : ren m m') (rv : ren n n'),
      rename_rvar_term rv (rename_fvar_term fv t) = rename_fvar_term fv (rename_rvar_term rv t))
  /\
  (forall (P:proc),
    forall m m' n n' (fv : ren m m') (rv : ren n n'),
      rename_rvar_proc rv (rename_fvar_proc fv P) = rename_fvar_proc fv (rename_rvar_proc rv P))
  /\ 
  (forall (o:oper),
    forall m m' n n' (fv : ren m m') (rv : ren n n'),
      rename_rvar_oper rv (rename_fvar_oper fv o) = rename_fvar_oper fv (rename_rvar_oper rv o)).
Proof.
  apply tpo_ind; intros; simpl.
  (* By IHs *)
  all: try rewrite H; try rewrite H0; reflexivity.
Qed.

Lemma rename_rvar_fvar_commute_term : forall m m' n n' (fv : ren m m') (rv : ren n n') (t:term),
    rename_rvar_term rv (rename_fvar_term fv t) = rename_fvar_term fv (rename_rvar_term rv t).
Proof. intros; apply rename_rvar_fvar_commute_tpo. Qed.
Lemma rename_rvar_fvar_commute_proc : forall m m' n n' (fv : ren m m') (rv : ren n n') (P:proc),
    rename_rvar_proc rv (rename_fvar_proc fv P) = rename_fvar_proc fv (rename_rvar_proc rv P).
Proof. intros; apply rename_rvar_fvar_commute_tpo. Qed.
Lemma rename_rvar_fvar_commute_oper : forall m m' n n' (fv : ren m m') (rv : ren n n') (o:oper),
    rename_rvar_oper rv (rename_fvar_oper fv o) = rename_fvar_oper fv (rename_rvar_oper rv o).
Proof. intros; apply rename_rvar_fvar_commute_tpo. Qed.

  


  (* ren_id is a renaming identity *)

Lemma rename_rvar_id_tpo :
  (forall m n (t:term),
      ws_term m n t -> rename_rvar_term (ren_id n) t = t)
  /\
  (forall m n (P:proc),
      ws_proc m n P -> rename_rvar_proc (ren_id n) P = P)
  /\
  (forall m n (o:oper),
      ws_oper m n o -> rename_rvar_oper (ren_id n) o = o).
Proof.
  apply ws_tpo_ind; intros; simpl.
  (* By IHs and Properties of Identity Renamings *)
  all: try rewrite ren_shift_id; try rewrite H; try rewrite H0;
        repeat rewrite ren_id_id; auto.
Qed.
  
Lemma rename_fvar_id_tpo :
  (forall m n (t:term), 
      ws_term m n t -> rename_fvar_term (ren_id m) t = t)
  /\
  (forall m n (P:proc), 
      ws_proc m n P -> rename_fvar_proc (ren_id m) P = P)
  /\ 
  (forall m n (o:oper), 
      ws_oper m n o -> rename_fvar_oper (ren_id m) o = o).
Proof.
  apply ws_tpo_ind; intros; simpl.
  (* By IHs and Properties of Identity Renamings *)
  all: try rewrite ren_shift_id; try rewrite H; try rewrite H0;
        repeat rewrite ren_id_id; auto.
Qed.

Lemma rename_rvar_id_term :
    forall m n (t:term), ws_term m n t -> rename_rvar_term (ren_id n) t = t.
Proof. intros; eapply rename_rvar_id_tpo; eauto. Qed.
Lemma rename_rvar_id_oper : 
  forall m n (o:oper), ws_oper m n o -> rename_rvar_oper (ren_id n) o = o.
Proof. intros; eapply rename_rvar_id_tpo; eauto. Qed.
Lemma rename_rvar_id_proc :
  forall m n (P:proc), ws_proc m n P -> rename_rvar_proc (ren_id n) P = P.
Proof. intros; eapply rename_rvar_id_tpo; eauto. Qed.
Lemma rename_fvar_id_term :
 forall m n (t:term), ws_term m n t -> rename_fvar_term (ren_id m) t = t.
Proof. intros; eapply rename_fvar_id_tpo; eauto. Qed.
Lemma rename_fvar_id_proc :
 forall m n (P:proc), ws_proc m n P -> rename_fvar_proc (ren_id m) P = P.
Proof. intros; eapply rename_fvar_id_tpo; eauto. Qed.
Lemma rename_fvar_id_oper :
 forall m n (o:oper), ws_oper m n o -> rename_fvar_oper (ren_id m) o = o.
Proof. intros; eapply rename_fvar_id_tpo; eauto. Qed.



(* TODO? alpha-equivalence 

t1 seq t1' peq t2 => t1 aeq t2 

symmetry, reflexivity, transitivity of aeq

-> strong confluence t steps t1, t steps t2
exists t1' t2' st t1' aeq t2' and t1 steps t1' and t2 steps t2'
*)



(* nu equivalence -------------------------------------------------------- *)
(* The "nu-bound" variables within a bag can be permuted without affecting the
meaning of the term.

   That means that [bag m' n' P] is "permutation equivalent" to [bag m' n' P'] when
   we rename (in P and P') the [m'] bound function identifiers 
   and [n'] bound identifiers up to some bijection.

   Permutation equivalence is also parameterized by two renamings that are used
   when passing outer permutations (of m and n variables) inwards. As such, two terms are truly
   permutation equivalent when these renaming parameters are identities (or m and n are 0).

*)

Unset Elimination Schemes.
Inductive peq_term :
  forall (m n:nat) (bf : ren m m) (br : ren n n) , term -> term -> Prop :=
| peq_bag :
  forall m n m' n'
    (bf : ren m m)
    (br : ren n n)
    (bf' : ren m' m')
    (br' : ren n' n')
    (WBF' : wf_bij_ren bf')
    (WBR' : wf_bij_ren br')
    (P P' : proc)
    (EQP : peq_proc (m' + m) (n' + n) (bij_app bf' bf) (bij_app br' br) P P')
  ,
    peq_term m n bf br (bag m' n' P) (bag m' n' P')
             
with peq_proc : forall (m n : nat) (bf : ren m m) (br : ren n n), proc -> proc -> Prop :=
| peq_def : forall m n r (HR : r < n) o o'
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br o o' ->
    peq_proc m n bf br (def r o) (def (br r) o')

| peq_app : forall m n f (HF : f < m) r (HR : r < n)
    (bf : ren m m)
    (br : ren n n),
    peq_proc m n bf br (app f r) (app (bf f) (br r))

| peq_par : forall m n P1 P1' P2 P2'
    (bf : ren m m)
    (br : ren n n),
    peq_proc m n bf br P1 P1' ->
    peq_proc m n bf br P2 P2' ->
    peq_proc m n bf br (par P1 P2) (par P1' P2')

| peq_nul : forall m n
    (bf : ren m m)
    (br : ren n n),
    peq_proc m n bf br nul nul
             
with peq_oper : forall (m n : nat) (bf : ren m m) (br : ren n n), oper -> oper -> Prop :=
| peq_emp : forall m n
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br emp emp

| peq_tup : forall m n r1 (HR1 : r1 < n) r2 (HR2 : r2 < n)
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br (tup r1 r2) (tup (br r1) (br r2))

| peq_bng : forall m n f (HF : f < m)
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br (bng f) (bng (bf f))

| peq_lam : forall m n t t'
    (bf : ren m m)
    (br : ren n n),
    peq_term m 1 bf (ren_id 1) t t' ->
    peq_oper m n bf br (lam t) (lam t').
(* FRAN: We may need to allow the parameter variable to permute? *)
Set Elimination Schemes.

Hint Constructors peq_term peq_proc peq_oper : core.

Scheme peq_term_ind := Induction for peq_term Sort Prop
    with peq_proc_ind := Induction for peq_proc Sort Prop
                         with peq_oper_ind := Induction for peq_oper Sort Prop.

Combined Scheme peq_tpo_ind from peq_term_ind, peq_proc_ind, peq_oper_ind.


(* PEQ is transitive with the compositions of renamings *)
Lemma peq_compose_tpo :
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (t t' : term)
     (HT: peq_term m n bf br t t'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)
      (bf' : ren m m) (br' : ren n n) (t'' : term)
      (WBF' : wf_bij_ren bf') (WBF' : wf_bij_ren br')    
      (HT' : peq_term m n bf' br' t' t''),
      peq_term m n (ren_compose bf bf') (ren_compose br br') t t'')
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (P P' : proc)
     (HT: peq_proc m n bf br P P'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)   
      (bf' : ren m m) (br' : ren n n) (P'' : proc)
      (WBF' : wf_bij_ren bf') (WBF' : wf_bij_ren br')             
      (HT' : peq_proc m n bf' br' P' P''),
      peq_proc m n (ren_compose bf bf') (ren_compose br br') P P'')
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (o o' : oper)
     (HT: peq_oper m n bf br o o'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)   
      (bf' : ren m m) (br' : ren n n) (o'' : oper)
      (WBF' : wf_bij_ren bf') (WBF' : wf_bij_ren br')            
      (HT' : peq_oper m n bf' br' o' o''),
      peq_oper m n (ren_compose bf bf') (ren_compose br br') o o'').
Proof.
  (* Induct on the first peq *)
  apply peq_tpo_ind; intros.
  (* Invert the second peq *)
  all: inversion HT'; existT_eq; subst; auto.
  (* Most cases solved by composing the renamings,
      followed by the corresponding peq constructor and IHs *)
  all: try solve [
    repeat rewrite (ren_compose_correct br br'); 
    repeat rewrite (ren_compose_correct bf bf');
    econstructor; auto
  ]. 
  (* Bag *)
  - econstructor.
    (* Construct what the composed renamings will be *)
    + eapply wf_bij_ren_compose. apply WBF'. apply WBF'2.
    + eapply wf_bij_ren_compose. apply WBR'. apply WBR'0.
    (* Processes are peq by IH 
        (which requires the composed renamings be wf and bij) *)
    + rewrite <- wf_bij_ren_app_compose; auto.
      rewrite <- wf_bij_ren_app_compose; auto.
      apply H; auto using wf_bij_ren_app.
  (* Lam *)
  - econstructor.
    (* Introduce an identity renaming to compose with *)
    rewrite <- (ren_compose_id_r (ren_id 1) wf_bij_ren_id).
    (* Terms are peq by IH *)
    apply H; auto using wf_bij_ren_id.
Qed.


(* PEQ is symmetric with the inverse renamings *)
Lemma peq_inv_tpo :
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (t t' : term)
     (HT: peq_term m n bf br t t'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
      peq_term m n (bij_inv bf WBF) (bij_inv br WBR) t' t)
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (P P' : proc)
     (HT: peq_proc m n bf br P P'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
      peq_proc m n (bij_inv bf WBF) (bij_inv br WBR) P' P)
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (o o' : oper)
     (HT: peq_oper m n bf br o o'),
    forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
      peq_oper m n (bij_inv bf WBF) (bij_inv br WBR) o' o).
Proof.
  apply peq_tpo_ind; intros.
  (* Most cases are by IH after expanding x to ((bij_inv r _) (r x)) *)
  (* FRAN: Can't figure out how to make this cleanly repeat without diverging *)
  all: try solve [auto;
    match goal with
      (* 2 variables for 2 renamings (app) *)
      | [ _: ?x < ?n, _: ?y < ?m, r: ren ?n ?n, r': ren ?m ?m,
              WB: wf_bij_ren ?r, WB': wf_bij_ren ?r' |- _ ] => 
          assert (x = ((bij_inv r WB) (r x))) as ?HI;
            try solve [apply bij_ren_inv_elt; auto];
          assert (y = ((bij_inv r' WB') (r' y))) as ?HI';
            try solve [apply bij_ren_inv_elt; auto];
          rewrite HI at 2; rewrite HI' at 2
      (* 2 variables for 1 renaming (tup) *)
      | [ _: ?x < ?n, _: ?y < ?n, r: ren ?n ?n, WB: wf_bij_ren ?r |- _ ] => 
          assert (x = ((bij_inv r WB) (r x))) as ?HI;
            try solve [apply bij_ren_inv_elt; auto];
          assert (y = ((bij_inv r WB) (r y))) as ?HI';
            try solve [apply bij_ren_inv_elt; auto];
          rewrite HI at 2; rewrite HI' at 2
      (* 1 variables for 1 renaming (def) *)
      | [ _: ?x < ?n, r: ren ?n ?n, WB: wf_bij_ren ?r |- _ ] => 
          assert (x = ((bij_inv r WB) (r x))) as ?HI;
            try solve [apply bij_ren_inv_elt; auto];
          rewrite HI at 2
      end; 
    constructor; repeat try (apply WBF; auto); repeat try (apply WBR; auto); auto]. 
  (* Bag *)
  - apply peq_bag with (bf' := bij_inv bf' WBF') (br' := bij_inv br' WBR').
    1, 2: auto using bij_inv_wf_bij.
    rewrite <- bij_inv_app with (HWB1 := WBF')(HWB2 := WBF).    
    rewrite <- bij_inv_app with (HWB1 := WBR')(HWB2 := WBR).
    apply H.
  (* Lam *)
  - constructor; auto.
    rewrite <- bij_inv_id.
    apply H; auto.
Qed.


(* PEQ is reflexive on "well scoped" terms using the appropriate identity renamings *)
Lemma peq_id_refl_tpo :
  (forall m n (t : term),
      ws_term m n t ->
      peq_term m n (ren_id m) (ren_id n) t t)
  /\ (forall m n (P : proc),
        ws_proc m n P ->
        peq_proc m n (ren_id m) (ren_id n) P P)
  /\ (forall m n (o : oper),
        ws_oper m n o ->
        peq_oper m n (ren_id m) (ren_id n) o o).
Proof.
  apply ws_tpo_ind; intros.
  (* Most cases are by IH after expanding x to ((ren_id _) x) *)
  (* FRAN: Similar to above, would be nice to have the match repeat without diverging *)
  all: try solve [auto; 
    match goal with
      (* 2 variables *)
      | [ _: ?x < ?n, _: ?y < ?m |- _ ] => 
          rewrite <- (ren_id_id n x) at 2; auto;
          rewrite <- (ren_id_id m y) at 2; auto
      (* 1 variable *)
      | [ _: ?x < ?n |- _ ] => 
          rewrite <- (ren_id_id n x) at 2; auto
      end].
  (* Bag *)
  - econstructor; eauto using wf_bij_ren_id.
    rewrite bij_app_id.
    rewrite bij_app_id.
    apply H.
Qed.



(* We can existentially quantify over the renamings to get a "permutation"
   equivalence on syntax directly.  These relations are what actually formed
   a partial equivalence relation (PER).
 *)

 (* FRAN: Why are these parameterized by their variable bindings? *)

Inductive peq_t (m n : nat) (t t' : term) : Prop :=
| peq_t_intro :
  forall (bf : ren m m) (br : ren n n)
    (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)
    (EQ : peq_term m n bf br t t'),
    peq_t m n t t'.

Inductive peq_p (m n : nat) (P P' : proc) : Prop :=
| peq_p_intro :
  forall (bf : ren m m) (br : ren n n)
    (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)
    (EQ : peq_proc m n bf br P P'),
    peq_p m n P P'.

Inductive peq_o (m n : nat) (o o' : oper) : Prop :=
| peq_o_intro :
  forall (bf : ren m m) (br : ren n n)
    (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br)
    (EQ : peq_oper m n bf br o o'),
    peq_o m n o o'.

Infix "[t≡ m n ]" := (peq_t m n) (at level 55).
Infix "[p≡ m n ]" := (peq_p m n) (at level 55).
Infix "[o≡ m n ]" := (peq_o m n) (at level 55).

Lemma peq_t_refl : forall m n t,
    ws_term m n t ->
    peq_t m n t t.
Proof. specialize (peq_id_refl_tpo); intros.
  destruct H as [HT _].
  specialize (HT m n t H0).
  econstructor; eauto using wf_bij_ren_id. Qed.
Lemma peq_p_refl : forall m n P,
    ws_proc m n P ->
    peq_p m n P P.
Proof. specialize (peq_id_refl_tpo); intros.
  destruct H as [_ [HP _]].
  specialize (HP m n P  H0).
  econstructor; eauto using wf_bij_ren_id. Qed.
Lemma peq_o_refl : forall m n o,
    ws_oper m n o ->
    peq_o m n o o.
Proof. specialize (peq_id_refl_tpo); intros.
  destruct H as [_ [_ HO]].
  specialize (HO m n o H0).
  econstructor; eauto using wf_bij_ren_id. Qed.

#[global] Instance Transitive_peq_term {m n} : Transitive (peq_t m n).
Proof. unfold Transitive; intros. inversion H; inversion H0. econstructor.
  3 : eapply peq_compose_tpo; eauto. 
  all: auto using wf_bij_ren_compose. Qed.
#[global] Instance Transitive_peq_proc {m n} : Transitive (peq_p m n).
Proof. unfold Transitive; intros. inversion H; inversion H0. econstructor.
  3 : eapply peq_compose_tpo; eauto. 
  all: auto using wf_bij_ren_compose. Qed.
#[global] Instance Transitive_peq_oper {m n} : Transitive (peq_o m n).
Proof. unfold Transitive; intros. inversion H; inversion H0. econstructor.
  3 : eapply peq_compose_tpo; eauto. 
  all: auto using wf_bij_ren_compose. Qed.

#[global] Instance Symmetric_peq_term {m n} : Symmetric (peq_t m n).
Proof. unfold Symmetric; intros. inversion H.
  apply peq_t_intro with (bf := bij_inv bf WBF)(br := bij_inv br WBR).
  1, 2 : auto using bij_inv_wf_bij.
  apply peq_inv_tpo; auto. Qed.
#[global] Instance Symmetric_peq_proc {m n} : Symmetric (peq_p m n).
Proof. unfold Symmetric; intros. inversion H.
  apply peq_p_intro with (bf := bij_inv bf WBF)(br := bij_inv br WBR).
  1, 2 : auto using bij_inv_wf_bij.
  apply peq_inv_tpo; auto. Qed.
#[global] Instance Symmetric_peq_oper {m n} : Symmetric (peq_o m n).
Proof. unfold Symmetric; intros. inversion H.
  apply peq_o_intro with (bf := bij_inv bf WBF)(br := bij_inv br WBR).
  1, 2 : auto using bij_inv_wf_bij.
  apply peq_inv_tpo; auto. Qed.


(* Well-formedness also respects permutation equivalence, but we have to compose
   the context with the *inverse* renaming to explain how the book keeping works
   out.  *) 
Lemma peq_wf_tpo :
  (forall (m n:nat) (t1 : term), 
      wf_term m n t1 ->
      forall (t2 : term) (bf : ren m m) (br : ren n n),
        peq_term m n bf br t1 t2 ->
        forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
          wf_term m n t2)
  /\ (forall (m n:nat) (G : lctxt m) (D : lctxt n) (P1 : proc), 
        wf_proc m n G D P1 ->
      forall (P2 : proc) (bf : ren m m) (br : ren n n),
          peq_proc m n bf br P1 P2 ->
        forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
          wf_proc m n
              (ren_compose (bij_inv bf WBF) G)
              (ren_compose (bij_inv br WBR) D)
              P2)
  /\ (forall (m n:nat) (G : lctxt m) (D : lctxt n) (o1 : oper),  
        wf_oper m n G D o1 ->
      forall (o2 : oper) (bf : ren m m) (br : ren n n),
          peq_oper m n bf br o1 o2 ->
        forall (WBF : wf_bij_ren bf) (WBR : wf_bij_ren br),
          wf_oper m n
              (ren_compose (bij_inv bf WBF) G)
              (ren_compose (bij_inv br WBR) D)
              o2).
Proof.
  apply wf_tpo_ind; intros.
  (* All cases but Bag follow this structure: *)
  all: try solve [
    (* Invert on the PEQ judgment *)
    match goal with
    | [ H: context[peq_term] |- _ ] => inversion H; existT_eq; subst
    | [ H: context[peq_proc] |- _ ] => inversion H; existT_eq; subst
    | [ H: context[peq_oper] |- _ ] => inversion H; existT_eq; subst
    end;

    (* For convenience *)
    remember (bij_inv_wf_bij _ WBR) as WBRI;
    remember (bij_inv_wf_bij _ WBF) as WBFI;

    (* Rewrites any known context structure *)
    specialize (@Proper_ren_compose _ _ nat (bij_inv br WBR) WBRI); intros;
    try rewrite HD;
    specialize (@Proper_ren_compose _ _ nat (bij_inv bf WBF) WBFI); intros;
    try rewrite HG;
    
    (* Does any context rewriting necessary for constructing WF *)
    try (unfold zero; repeat rewrite ren_compose_flat_ctxt);
    try (repeat rewrite ren_sum_compose);
    try (repeat rewrite ren_one_compose with (HWB := WBRI); auto;
      rewrite (bij_inv_bij_inv_eq _ WBR));
    try (repeat rewrite ren_one_compose with (HWB := WBFI); auto;
      rewrite (bij_inv_bij_inv_eq _ WBF));

    (* The PEQ expression (t' p' o') is WF under the renamed contexts, 
          with subexpressions WF by IH *)
    econstructor; eauto;
    try reflexivity;
    try (apply WBR; auto);
    try (apply WBF; auto);
    (* Special case for proving Lambda's subterm WF*)
    try (apply (H _ _ _ H6); auto using wf_bij_ren_id)
  ].
  (* Bag *)
  - inversion H0; existT_eq; subst.
    apply wf_bag with (G:=(ren_compose (bij_inv bf' WBF') G))
                      (D:=(ren_compose (bij_inv br' WBR') D)).
    (* Composing the renamings doesn't change resource usage *)
    + apply (compose_wf_bij_ren_ctxt_preservation 
                (fun x => x = 1) _ _); auto using bij_inv_wf.
    + apply (compose_wf_bij_ren_ctxt_preservation 
                (fun x => x = 2 \/ x = 0) _ _); auto using bij_inv_wf.
    (* By IH after many renaming/context rewritings *)
    + unfold zero; rewrite <- (flat_ctxt_ren_compose_identity 0 (bij_inv bf WBF)).
      rewrite <- (flat_ctxt_ren_compose_identity 1 (bij_inv br WBR)).
      repeat rewrite ren_compose_app; auto using bij_inv_wf_bij.
      repeat rewrite bij_app_inv.
      apply H; auto.
Qed.    

