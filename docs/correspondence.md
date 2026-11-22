# Theorem correspondence

The table links manuscript references to Lean declarations and their checks.
Import the library with `import STLTableaux`.

## Main results

| Manuscript | Lean declarations | Checks |
|---|---|---|
| Theorem 3.13 (expansion rule correctness) | [Finite timing bounds](../STLTableaux/Rules/Finite/Correctness.lean#L153) · [Unbounded timing bounds](../STLTableaux/Rules/Unbounded/UnboundedCorrectness.lean#L64) | [Rules](../STLTableauxTest/Interfaces/Rules.lean) |
| Proposition 3.14 (invariant preservation) | [Finite timing bounds](../STLTableaux/Rules/Finite/Preservation.lean#L355) · [Unbounded timing bounds](../STLTableaux/Rules/Unbounded/UnboundedCorrectness.lean#L99) | [Rules](../STLTableauxTest/Interfaces/Rules.lean) |
| Theorem 4.14 (closure soundness) | [`minimal_closure_holds_of_atomicProjection`](../STLTableaux/Closure/Correctness/FaithfulClosureSoundness.lean#L371) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) |
| Definition 4.15 ($p$-expansion) | [`BranchwisePExpansion`](../STLTableaux/Closure/Expansion/BranchwiseExpansion.lean#L14) · [`AlphaBranchwisePExpansion`](../STLTableaux/Closure/Expansion/BranchwiseExpansion.lean#L91) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) |
| Definition 4.17 (expansion levels) | [`branchwiseExpansionLevel`](../STLTableaux/Closure/Expansion/BranchwiseExpansion.lean#L98) · [`alphaBranchwiseExpansionLevel`](../STLTableaux/Closure/Expansion/BranchwiseExpansion.lean#L102) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) |
| Definition 4.18 and Lemmas 4.19–4.20 (rank, decrease, and termination) | [`orbitBranchwiseLevelRank`](../STLTableaux/Closure/Expansion/BranchwiseRankOrbit.lean#L103) · [`orbitBranchwiseLevelRank_eq`](../STLTableaux/Closure/Expansion/BranchwiseRankOrbit.lean#L124) · [`alpha_branchwise_rank_decrease`](../STLTableaux/Closure/Expansion/BranchwiseRank.lean#L251) · [`alpha_branchwise_rank_eventually_zero`](../STLTableaux/Closure/Expansion/BranchwiseRank.lean#L259) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) · [Closure dependencies](../STLTableauxTest/Axioms/ClosureProofDependencies.lean) |
| Theorem 4.22 (closure completeness) | [`satisfied_closure_exists`](../STLTableaux/Closure/Correctness/FaithfulClosureCompleteness.lean#L275) · [`satisfied_closure_branchwise_path`](../STLTableaux/Closure/Expansion/BranchwiseClosure.lean#L346) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) · [Closure dependencies](../STLTableauxTest/Axioms/ClosureProofDependencies.lean) |
| Definition 4.28 and Lemma 4.33 (tableau construction and generator path existence) | [`closureTableau`](../STLTableaux/Tableau/Construction/GeneratorPath.lean#L122) · [`generator_path_exists_with_closure`](../STLTableaux/Tableau/Construction/GeneratorPath.lean#L173) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) |
| Lemmas D.1, D.2, and 4.31 (trace invariants and equivalence) | [`trace_invariant`](../STLTableaux/Tableau/Traces/TableauTraceLemmas.lean#L103) · [`trace_ftrace_implication`](../STLTableaux/Tableau/Traces/TableauTraceLemmas.lean#L200) · [`trace_equivalence`](../STLTableaux/Tableau/Traces/TableauTraceLemmas.lean#L120) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) · [Closure dependencies](../STLTableauxTest/Axioms/ClosureProofDependencies.lean) |
| Theorems 4.32 and 4.34 (tableau soundness and completeness) | [`recognizes_iff_formula`](../STLTableaux/Tableau/Correctness/TableauCorrectness.lean#L11) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) |
| Lemma 4.35 (simplified tableau) | [`simplified_satisfied_accepting_iff`](../STLTableaux/Finiteness/Correctness/SimplifiedTableauCorrectness.lean#L133) | [Claims](../STLTableauxTest/Axioms/Claims.lean) · [Simplified tableau](../STLTableauxTest/Regression/SimplifiedTableauChecks.lean) |
| Lemma 4.36 (bounded accepting runs) | The manuscript bounds the number of interval predicates per state by $O(\lvert\varphi\rvert\,r(\varphi))$. The proof of Theorem 4.37 constructs [a satisfied accepting path over a finite set of clocks](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean#L312). | [Claims](../STLTableauxTest/Axioms/Claims.lean) |
| Theorem 4.37 (finite tableau) | [Construction](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean#L54) · [Clock bound](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean#L291) · [State bound](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean#L249) · [Recognition](../STLTableaux/Finiteness/Correctness/FiniteTableau.lean#L431) | [Claims](../STLTableauxTest/Axioms/Claims.lean) · [Whole library](../STLTableauxTest/Axioms/Library.lean) |
| Lemma C.15 (common expansion level) and the numeric conditions of Corollary C.16 | [`all_closures_mem_branchwise_level_at_first_orbit_rank_zero`](../STLTableaux/Closure/Expansion/BranchwiseClosureTermination.lean#L79) · [`minimal_closure_numeric`](../STLTableaux/Closure/Correctness/FaithfulClosureSoundness.lean#L360) | [Tableau](../STLTableauxTest/Interfaces/Tableau.lean) · [Closure dependencies](../STLTableauxTest/Axioms/ClosureProofDependencies.lean) |
| Lemma 5.5 (translation correctness) | [`canonical_translation_correctness`](../STLTableaux/Automata/Translation/CanonicalTranslationCorrectness.lean#L51) | [Claims](../STLTableauxTest/Axioms/Claims.lean) · [Model checking](../STLTableauxTest/Regression/CanonicalModelCheckingChecks.lean) |
| Proposition 5.6 (bounded zero-time jump extension) | [`boundedZeroTimeExtension_trajectory_iff`](../STLTableaux/Automata/Execution/BoundedZeroTimeExtension.lean#L190) | [Claims](../STLTableauxTest/Axioms/Claims.lean) |
| Theorem 5.7 (model checking) | [`canonical_model_checking`](../STLTableaux/ModelChecking/Reduction/CanonicalModelChecking.lean#L150) | [Claims](../STLTableauxTest/Axioms/Claims.lean) · [Model checking](../STLTableauxTest/Regression/CanonicalModelCheckingChecks.lean) |
| Corollary 5.8 (robust model checking) | [`canonical_robust_model_checking`](../STLTableaux/ModelChecking/Reduction/CanonicalModelChecking.lean#L230) | [Claims](../STLTableauxTest/Axioms/Claims.lean) · [Model checking](../STLTableauxTest/Regression/CanonicalModelCheckingChecks.lean) · [Robustness bounds in a concrete example](../STLTableauxTest/Regression/PrelimPartitionConnectionChecks.lean) |
| Numbered examples from Sections 3–4 and Appendix C | [Examples](../STLTableaux/Examples.lean) | [Example declarations](../STLTableauxTest/Axioms/Examples.lean) |

Run the full check to execute the checks in the table. The assumptions
guide gives the premises and scope of the results.
[Validation](validation.md) · [Assumptions](assumptions.md)

## Scope

- Correctness and termination of the on-the-fly construction (Algorithm 1)
  and existence and minimality of coarsest fully stable partitions are outside
  the formalization.
- The size bounds use the formula supplied to the finite construction. The
  model-checking result uses admissible synchronized executions. The figure
  examples cover the transitions specified in their Lean statements.
- The prototype and benchmark results are available in the experiment archive.

## Supplemental lemmas on checking intervals

These lemmas cover merge equivalences, preservation of invariants and endpoint
exclusivity, and bounds for ordered intervals. [Checking intervals](checking-intervals.md)
