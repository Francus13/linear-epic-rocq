# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

A Rocq (Coq) formalization of a linear, opportunistic lambda calculus ("LEpic"). It targets **Rocq 9.0**, uses the `Stdlib` library (`From Stdlib Require Import ...`, not `Coq.`), and `Permutations.v` also needs the `Equations` plugin. This is research code: proofs are still in progress, and some lemmas end in `Admitted` or contain `admit`.

## Build

Run these from the repo root:

- `make`: builds every file listed in `_CoqConfig`. It first generates `_CoqProject` and `Makefile.rocq`.
- `make clean`: removes the build outputs and the generated files.
- Check one file and its dependencies: `make -f Makefile.rocq theories/Semantics.vo`. Or compile it directly with `rocq compile -Q theories LEpic theories/Semantics.v`, after its dependencies are built.

To add or remove a file from the build, edit **`_CoqConfig`**. `_CoqProject` is generated from it, so edits to `_CoqProject` are overwritten. The logical path is `-Q theories LEpic`, so files import each other with `From LEpic Require Import ...`.

`theories/Examples.v` and `theories/OldSemanticsProofs.v` are not in `_CoqConfig`, so `make` does not build them. `OldSemanticsProofs.v` holds an older version of the semantics and its proofs, kept for reference.

There is no test suite. A file is correct when it compiles. To list the proofs that are still open, run `grep -n "Admitted\|admit\." theories/*.v`.

## Architecture

The dependency chain is: `Contexts` → `Syntax` → `EvalContexts` → `Semantics` → `Confluence`. `Observations` depends only on `Contexts` and `Syntax`. `Permutations` stands alone: it has its own `bij` datatype (built from id, swap, comp and plus), and no other file imports it yet.

- **`Contexts.v`**: contexts are functions. `ctxt n X := var -> X`, and `lctxt n := ctxt n nat` counts how many times each variable is used.
  - Basic operations: `sum`, `zero`, `one`, `delta`, `⊗` (append) and `SUM`. Equality is pointwise (`ctxt_eq`).
  - `Module Renamings` (the one the rest of the code imports) defines `ren n m := ctxt n var` and `wf_ren`. `wf_ren` requires in-scope variables to map in-scope and out-of-scope variables to map out-of-scope. This definition was changed on 5/11/2026; the older version is still in a comment. The module also defines `bij_ren` / `wf_bij_ren` (renamings that are bijections), plus `lctxt_rename` and composition.
  - `Module RelationalRenamings` is an alternative where renamings are relations. The main development does not use it.
  - Useful tactics: `lia_destruct`, `lia_goal`, `solve_ctxt_eq` and `destruction`.
- **`Syntax.v`**: the core syntax, using de Bruijn indices. The long comment at the top of the file explains the conventions. There are two kinds of variable:
  - `m` / `f`: unrestricted (function) variables.
  - `n` / `r`: linear (resource) variables.

  The syntax is three mutually inductive types:
  - `term`: `bag m n P`, which binds `m` new function variables and `n` new resource variables.
  - `proc`: `def r o`, `app f r`, `par`, `nul`, `req`.
  - `oper`: `emp`, `tup`, `bng`, `lam`.

  Each relation comes in `_term`/`_proc`/`_oper` versions:
  - `ws_*`: well-scoped.
  - `seq_*`: structural equivalence, written `≈t`. It lets processes be permuted.
  - `wf_*`: well-formed, meaning scoping plus linearity. Function variables are used once each. Each resource variable has a usage count of 0 or 2, and free resources are used exactly once.
  - `peq_*`: renaming by a bijection.

  `rename_rvar_*` and `rename_fvar_*` apply renamings. `dest_conj_disj_exist` and `existT_eq` are helper tactics.
- **`EvalContexts.v`**: evaluation contexts (`EC_term` / `EC_proc`, with a hole `Ehol`). Notation: `Et <=[ P ]` fills the hole with a process, and `Et <=<[ EP ]` fills it with another context. The "hole scope" is the innermost `bag` around the hole, and many helpers (`split_hole_scope`, `mutate_hole_scope`, `bound_*vars_*`) work with it. `wf_EC_term` tracks how many variables are in scope at the hole, and `wf_hs_fun` states that a function on contexts preserves well-formedness.
- **`Semantics.v`**: `prim_step` defines the reduction rules on filled evaluation contexts: par-nul, emp cut, tup cut, application in the same scope or a different scope, and `req` renaming. `step` is `prim_step` up to `≈t` on both sides, and `multi_step` is its reflexive-transitive closure. This file also proves `wf_prim_step`, which is preservation for primitive steps.
- **`Confluence.v`**: lifts preservation to `step` (`wf_step`, admitted) and defines alpha equivalence: `aeq m n t1 t2 := exists t1', t1 ≈t t1' /\ peq_t m n t1' t2`. The `confluence` lemma is stated, and its proof is an outline of `admit`ted cases.
- **`Observations.v`**: a first draft of observations and a machine semantics.

## Conventions

- Inline comments signed `FRAN:` or `SAZ:` are notes from the authors. Keep them.
- Some proofs are deliberately `Admitted` so that `make` runs faster; these are marked with comments like "Admitted here to quicken make". Before treating one of these as an open problem, check the comment next to it.
- The `.lia.cache` file at the repo root is large and is ignored by git.
