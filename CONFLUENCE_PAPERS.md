# Confluence of nondeterministic calculi with evaluation-context semantics

A survey of papers whose languages reduce nondeterministically under evaluation
contexts and that prove confluence (or determinacy). They are sorted by how closely
they match LEpic, where `step` is a primitive step taken up to `≈t` and linearity
rules out interference between redexes.

Entries marked *(from memory)* are standard references that were not re-checked
against a source when this survey was compiled (2026-10-20). The rest were.

## 1. Closest to LEpic: linearity gives confluence

- **Fowler, Kokke, Dardha, Lindley, Morris, "Separating Sessions Smoothly"**
  (CONCUR 2021; LMCS 19(3), 2023). This is the best template. HGV is a linear
  session-typed λ-calculus whose configurations reduce under evaluation contexts,
  modulo structural congruence. They prove the **diamond property** by relying on
  linearity: two redexes that overlap can be fired in either order. They also prove
  deadlock freedom and strong normalisation. Their proof is said to follow the one
  for GV in **Lindley & Morris, "A Semantics for Propositions as Sessions"**
  (ESOP 2015), which shows GV is deadlock-free, deterministic and terminating.
  Neither is mechanized.
- **Kobayashi, Pierce, Turner, "Linearity and the Pi-Calculus"** (POPL 1996;
  TOPLAS 21(5), 1999). Communication on linear channels gives **partial
  confluence**. Their reduction contexts and structural congruence match LEpic's
  `par`/`nul` and `≈t` closely. Kobayashi's follow-up TR96-02 adds partial
  deadlock-freedom.
- **Lafont, "Interaction Nets"** (POPL 1990) *(from memory)*. Interaction nets have
  one-step **strong confluence**, because every active pair is disjoint. If LEpic's
  tup/emp cuts behave like interaction rules, this is the cleanest confluence
  argument to borrow.

## 2. Deterministic parallelism: evaluation contexts with nondeterministic scheduling

- **Kuper & Newton, "LVars: lattice-based data structures for deterministic
  parallelism"** (FHPC 2013), and **Kuper, Turon, Krishnaswami, Newton, "Freeze
  After Writing"** (POPL 2014). The reduction semantics picks a redex
  nondeterministically. Determinism (in the POPL paper, quasi-determinism) is proved
  through an Independence lemma, a strong local confluence lemma, and then the
  diamond property. The proofs are on paper. The authors of a 2025 arXiv paper
  (2511.23283, on the Musketeer program logic) say they have a mechanized proof of
  schedule-independent safety for a simplified LVars model, but they don't present
  it in that paper.
- **Burckhardt & Leijen, "Semantics of Concurrent Revisions"** (ESOP 2011). This is
  a revision calculus with evaluation contexts and locally nondeterministic
  scheduling, and they prove it confluent and determinate. **Overbeek, "Formalizing
  Determinacy of Concurrent Revisions"** (CPP 2020) mechanized the proof in
  Isabelle/HOL (it's in the AFP). He found ambiguities in the original semantics
  that forced changes, and he simplified the proof. Read this one for the lessons on
  mechanizing such a proof.
- **Flanagan & Felleisen, "The Semantics of Future and Its Use in Program
  Optimization"** (POPL 1995; Rice TR94-238). This is a futures calculus built from
  evaluation contexts, and it is confluent. **Niehren, Schwinghammer, Smolka, "A
  concurrent lambda calculus with futures"** (TCS 2006) explains why confluence
  fails once reference cells are added.

## 3. Probabilistic and quantum calculi: confluence despite nondeterministic choice

- **Faggian & Ronchi della Rocca, "Lambda Calculus and Probabilistic Computation"**
  (LICS 2019). The naive calculus with probabilistic choice is not confluent. They
  restrict where the choice rule may fire, using surface contexts and a
  linear-logic-based base calculus. They then prove confluence and standardization
  in an asymptotic sense.
- **Dal Lago, Masini, Zorzi, "Confluence Results for a Quantum Lambda Calculus with
  Measurements"** (ENTCS 270, 2011). This proves confluence of Q* for finite and
  infinite computations, despite measurement. Their earlier calculus Q, which has no
  measurement, is confluent too (MSCS 2009).

## 4. Deterministic but the basis for the method

- **Ariola, Felleisen, Maraist, Odersky, Wadler, "The Call-by-Need Lambda
  Calculus"** (POPL 1995), and **Ariola & Felleisen** (JFP 1997) *(from memory)*.
  These are the standard examples of proving a calculus confluent while giving its
  evaluation through evaluation contexts.
- **Felleisen & Hieb** (TCS 1992) *(from memory)*. Church–Rosser for control and
  state calculi defined with evaluation contexts.

## 5. Mechanization and confluence modulo an equivalence

- **Huet, "Confluent Reductions"** (JACM 1980), and **Ohlebusch, "Church–Rosser
  theorems for abstract reduction modulo an equivalence relation"** (RTA 1998)
  *(from memory)*. These are the abstract theorems you need, because `step` is
  defined modulo `≈t`. The key fact is that a diamond for `prim_step`, together with
  commutation between `prim_step` and `≈t`, gives confluence modulo `≈t`.
- **Cruz-Filipe, Montesi, Peressotti, "Formalising a Turing-Complete Choreographic
  Language in Coq"** (ITP 2021; Coq code on Zenodo, DOI 10.5281/zenodo.4479102).
  This has confluence lemmas mechanized in Coq. They report that the number of cases
  exploded because of the many structural precongruence rules, and that their
  induction hypotheses were too weak, so they had to induct on derivation size.
  Expect the same when proving that `≈t` commutes with `prim_step`.

## Takeaways for `Confluence.v`

1. HGV/GV is the closest precedent: linearity gives a one-step diamond up to
   structural congruence.
2. The standard proof structure is a local diamond for `prim_step` (LVars' "strong
   local confluence"), a lemma that `prim_step` commutes with `≈t`, and then a
   Huet/Ohlebusch-style lift to `multi_step`.
3. No Coq mechanization turned up that is a direct precedent. The closest are
   Overbeek's Isabelle proof and the Coq choreography development, and both report
   that structural congruence was the hardest part.

## Sources

- [LVars (Indiana TR710)](https://www.cs.indiana.edu/pub/techreports/TR710.pdf)
- [Freeze After Writing (POPL 2014)](https://www.cl.cam.ac.uk/~nk480/lvish-popl.pdf)
- [Semantics of Concurrent Revisions](https://www.microsoft.com/en-us/research/publication/semantics-of-concurrent-revisions/)
- [Overbeek, CPP 2020](https://popl20.sigplan.org/details/CPP-2020-papers/10/Formalizing-Determinacy-of-Concurrent-Revisions)
- [AFP entry: Concurrent Revisions](https://isa-afp.org/entries/Concurrent_Revisions.html)
- [Lindley & Morris, ESOP 2015](https://conf.researchr.org/details/esop-2015/esop-2015-papers/20/A-Semantics-for-Propositions-as-Sessions)
- [Separating Sessions Smoothly](https://arxiv.org/pdf/2105.08996)
- [Kobayashi/Pierce/Turner (Pierce bibliography)](https://cis.upenn.edu/~bcpierce/papers/pict_bib.html)
- [Kobayashi TR96-02](https://library.t.u-tokyo.ac.jp/cslib/tech-reports/TR96-02-abstract.html)
- [λ(fut), Niehren et al.](https://www.ps.uni-saarland.de/Publications/documents/jlambda-fut.pdf)
- [Faggian & Ronchi della Rocca](https://arxiv.org/abs/1901.02853v5)
- [Dal Lago/Masini/Zorzi, Q*](https://www.arxiv.org/abs/0905.4567)
- [Dal Lago/Masini/Zorzi, Q](https://arxiv.org/abs/cs/0703152)
- [Choreographies in Coq (ITP 2021)](https://arxiv.org/pdf/2102.02627)
- [Musketeer / internal determinism](https://arxiv.org/pdf/2511.23283)
