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

From LinOpal Require Import Contexts Syntax.
Import Renamings.
Import Stdlib.Relations.Relation_Operators.

Local Open Scope program_scope.
Local Open Scope bool_scope.

(* Observations describe data that escapes to the environment.
   Every free rvar has exactly one obs,
   and every free fvar has a multiset of obs.
   Multisets here are functions to nat,
   returning how many instances of the argument are in the multiset. *)
Inductive obs :=
| var (r : rvar)
| emp
| tup (o1 o2 : obs)
| dcl (c : is_closed) (e : effect)
| lam (c : is_closed) (es : list effect) (o : obs)
with
effect := 
| eff (f : fvar) (os : list obs)
with
is_closed := 
| closed
| open
.


(* Refinement of observations: o1 ⊑ₒ o2 means o1 is at least as
   refined as o2 (a less-than-or-equal ordering).
   - emp is bottom: it is the least informative observation, so
     every observation refines it (o ⊑ₒ emp for all o).
   - closed is more refined than open.
   - Lists of effects and observations are multisets: they are
     compared up to reordering, and dropping elements makes a
     list less refined (see sub_multiset). *)

(* Closedness: closed refines open.
   Unicode has no subscript c, so the notation uses a superscript. *)
Reserved Notation "c1 ⊑ᶜ c2" (at level 70, no associativity).

Inductive sub_closed : is_closed -> is_closed -> Prop :=
| sub_closed_refl c : c ⊑ᶜ c
| sub_closed_open : closed ⊑ᶜ open
where "c1 ⊑ᶜ c2" := (sub_closed c1 c2).

Lemma sub_closed_trans c1 c2 c3 :
  c1 ⊑ᶜ c2 -> c2 ⊑ᶜ c3 -> c1 ⊑ᶜ c3.
Proof.
  intros H12 H23. destruct H12; inversion H23; subst; constructor.
Qed.

(* sub_multiset R l1 l2: l2 can be obtained from l1 by reordering,
   dropping elements, and replacing each remaining element x by
   some y with R x y. So l1 is the more refined multiset. *)
Section SubMultiset.
  Context {A : Type} (R : A -> A -> Prop).

  Inductive sub_multiset : list A -> list A -> Prop :=
  | sm_nil : sub_multiset nil nil
  | sm_elem x y l1 l2 :
      R x y -> sub_multiset l1 l2 -> sub_multiset (x :: l1) (y :: l2)
  | sm_drop x l1 l2 :
      sub_multiset l1 l2 -> sub_multiset (x :: l1) l2
  | sm_swap x y l : sub_multiset (y :: x :: l) (x :: y :: l)
  | sm_trans l1 l2 l3 :
      sub_multiset l1 l2 -> sub_multiset l2 l3 -> sub_multiset l1 l3.
End SubMultiset.

Reserved Notation "o1 ⊑ₒ o2" (at level 70, no associativity).
Reserved Notation "e1 ⊑ₑ e2" (at level 70, no associativity).

Inductive sub_obs : obs -> obs -> Prop :=
| sub_emp o : o ⊑ₒ emp
| sub_var r : var r ⊑ₒ var r
| sub_tup o1 o2 o1' o2' :
    o1 ⊑ₒ o1' -> o2 ⊑ₒ o2' -> tup o1 o2 ⊑ₒ tup o1' o2'
| sub_dcl c1 c2 e1 e2 :
    c1 ⊑ᶜ c2 -> e1 ⊑ₑ e2 -> dcl c1 e1 ⊑ₒ dcl c2 e2
| sub_lam c1 c2 es1 es2 o1 o2 :
    c1 ⊑ᶜ c2 -> sub_multiset sub_effect es1 es2 -> o1 ⊑ₒ o2 ->
    lam c1 es1 o1 ⊑ₒ lam c2 es2 o2
where "o1 ⊑ₒ o2" := (sub_obs o1 o2)
with sub_effect : effect -> effect -> Prop :=
| sub_eff f os1 os2 :
    sub_multiset sub_obs os1 os2 -> eff f os1 ⊑ₑ eff f os2
where "e1 ⊑ₑ e2" := (sub_effect e1 e2).

(* sub_obs and sub_effect are preorders.
   obs is nested through lists, so these proofs recurse with
   Fixpoint and inner fixes rather than the generated induction
   principles, which give no hypotheses for list elements. *)
Fixpoint sub_obs_refl (o : obs) : o ⊑ₒ o
with sub_effect_refl (e : effect) : e ⊑ₑ e.
Proof.
  - destruct o; constructor; try apply sub_closed_refl; auto.
    induction es; constructor; auto.
  - destruct e. constructor.
    induction os; constructor; auto.
Qed.

Lemma sub_effect_trans (e1 e2 e3 : effect) :
  e1 ⊑ₑ e2 -> e2 ⊑ₑ e3 -> e1 ⊑ₑ e3.
Proof.
  intros H12 H23. destruct H12. inversion H23; subst.
  constructor. eapply sm_trans; eauto.
Qed.

Fixpoint sub_obs_trans (o1 o2 o3 : obs) (H12 : o1 ⊑ₒ o2) {struct H12} :
  o2 ⊑ₒ o3 -> o1 ⊑ₒ o3.
Proof.
  intros H23. destruct H12; inversion H23; subst;
    try apply sub_emp; constructor;
    eauto using sub_effect_trans, sub_closed_trans, sm_trans.
Qed.

#[global] Instance sub_obs_PreOrder : PreOrder sub_obs.
Proof.
  constructor.
  - exact sub_obs_refl.
  - exact sub_obs_trans.
Qed.

#[global] Instance sub_effect_PreOrder : PreOrder sub_effect.
Proof.
  constructor.
  - exact sub_effect_refl.
  - exact sub_effect_trans.
Qed.

(* Sanity checks. *)
Example sub_obs_emp_top : tup (var 0) emp ⊑ₒ emp.
Proof. apply sub_emp. Qed.

Example sub_obs_tup : tup (var 0) (var 1) ⊑ₒ tup (var 0) emp.
Proof. repeat constructor. Qed.

Example sub_effect_reorder :
  eff 0 (var 1 :: var 2 :: nil) ⊑ₑ eff 0 (emp :: var 1 :: nil).
Proof.
  constructor. eapply sm_trans; [apply sm_swap |].
  repeat constructor.
Qed.

Example sub_effect_drop :
  eff 0 (var 1 :: var 2 :: nil) ⊑ₑ eff 0 (var 2 :: nil).
Proof.
  constructor. apply sm_drop. repeat constructor.
Qed.

Example sub_obs_closed_open (e : effect) : dcl closed e ⊑ₒ dcl open e.
Proof. constructor; [constructor | reflexivity]. Qed.

Example sub_effect_reorder_more :
  eff 0 (var 1 :: var 2 :: var 3 :: nil) ⊑ₑ eff 0 (var 3 :: var 2 :: var 1 :: nil).
Proof.
  constructor.
  (* [1;2;3] -> [1;3;2] *)
  apply sm_trans with (l2 := var 1 :: var 3 :: var 2 :: nil).
  { apply sm_elem; [reflexivity | apply sm_swap]. }
  (* [1;3;2] -> [3;1;2] *)
  apply sm_trans with (l2 := var 3 :: var 1 :: var 2 :: nil).
  { apply sm_swap. }
  (* [3;1;2] -> [3;2;1] *)
  apply sm_elem; [reflexivity | apply sm_swap].
Qed.



(* Relating terms and observations *)

(* Fixpoint is_escaping_channel (m n : nat) (r : rvar) 

Inductive observe_channel  *)
