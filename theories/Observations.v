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

From LinOpal Require Import Contexts Syntax EvalContexts Semantics Preservation.
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

Fixpoint eq_obs (o1 o2 : obs) : bool :=
  match (o1, o2) with
  | (var r, var r) => true
  | (emp, emp) => true
  | (tup oA oB, tup oC oD) => Bool.and (eq_obs oA oC) (eq_obs oB oD)
  | (dcl c e1, dcl c e2) => eq_effect e1 e2
  | (lam c es1 o1', lam c es2 o2') => 
  end.
