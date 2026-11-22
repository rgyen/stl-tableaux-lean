# Assumptions

- **Proposition 3.10(2).** Splitting the `↑` form (Definition 3.1(ii))
  yields an `↑↓` predicate, an unclocked interval predicate, and a judgement
  for the left marker under a distinct clock reset. At an interval position,
  the split uses the current interval's left marker and requires that
  interval to lie in the predicate's scope. [Predicate splitting](../STLTableaux/Rules/Finite/Equivalences.lean#L353)
- **Theorem 4.22 and Lemma C.15.** Closure completeness assumes a satisfied
  judgement whose predicate invariants hold and a partition fully stable
  for the formulas in the judgement's interval predicates. Lean proves
  existence using a decreasing rank and obtains explicit sequences of rule
  expansions by expanding predicates in rounds. The manuscript proves
  existence by one-step expansion. The proof of Lemma C.15 uses clock
  renamings that fix the clocks of the initial transition form. [Closure proofs](../STLTableauxTest/Axioms/ClosureProofDependencies.lean)
- **Lemma 4.35 and Theorem 4.37.** For a `MixedReady` formula and a fully
  stable partition, the original and simplified tableaux agree on the
  existence of a satisfied accepting run at the same clock valuation.
  The finite tableau is sound on any partition and includes empty final
  continuations. Under the input and partition conditions above,
  satisfaction at time zero yields one accepting run whose trace holds for
  every initial clock valuation. The clock and state bounds use the size
  and resolution of the formula supplied to the construction.
  [Simplified tableau](../STLTableaux/Finiteness/Correctness/SimplifiedTableauCorrectness.lean#L133) · [Finite tableau](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean)
- **Lemma 5.5.** The translation assumes finite variable support
  covering the input and a `NormalizedReady` formula with non-strict atoms.
  Forward correctness uses atomic right continuity. Reverse recognition
  holds for every partition induced by an admissible execution and a
  goal-reaching cut. A goal at the horizon may be reached by one jump from
  the last flow endpoint.
  [Translation correctness](../STLTableaux/Automata/Translation/CanonicalTranslationCorrectness.lean#L51)
- **Theorem 5.7 and Corollary 5.8.** Both require a finite set covering the
  variables of the tableau input and continuous system flows. In each system
  execution reaching the fixed horizon, the end of each flow and the start
  of the next must admit a chain of one to `n` zero-time jumps. Reachability
  synchronizes a prefix of a full system trajectory with an admissible
  property execution. Theorem 5.7 requires the normalized negation to satisfy
  `NormalizedReady` and to have non-strict atoms with continuous functions.
  Corollary 5.8 applies the atom conditions to the original formula. The
  no-goal direction requires finite variability for the original formula
  in Theorem 5.7 and for `Formula.robustCounterInput φ ε` in Corollary 5.8.
  [Model checking](../STLTableaux/ModelChecking/Reduction/CanonicalModelChecking.lean#L150) · [Robust model checking](../STLTableaux/ModelChecking/Reduction/CanonicalModelChecking.lean#L230)

[Theorem and example index](correspondence.md)
