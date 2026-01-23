From Stdlib Require Import
  Arith   
  Logic.FunctionalExtensionality         
  Classes.RelationClasses
  Morphisms
  Program.Basics
  List
  Lia.

From LEpic Require Import Syntax.
From LEpic Require Import Contexts.

Inductive obs :=
| var (r: rvar)
| emp
| tup (o1 o2: obs)
| dcl (mc: maybe_closed) (e: effect)
| lam (mc: maybe_closed) (es: list effect) (o: obs)
with
effect := 
| eff (f: fvar) (os: list obs)
with
maybe_closed := 
| closed
| open (rs: list rvar)
.

Definition machine := prod obs term.

Inductive wf_machine : machine -> Prop :=
| wf_mach :
  forall m n
    (G : lctxt m)
    (D : lctxt n)
    (o : obs)
    (t : term),
    wf_observation o ->
    wf_term m n G D t ->
    wf_machine (o, t)

with wf_observation : obs -> Prop :=
| wf_obs :
  forall
    (o : obs),
    wf_observation o
.

Inductive machine_strict_step : machine -> machine -> Prop :=
| term_step :
  forall m n
    (o1 o2 : obs)
    (t1 t2 : term),
    step m n t1 t2 ->
    machine_strict_step (o1 t1) (o2 t2)
.
