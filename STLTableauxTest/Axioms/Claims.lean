import STLTableaux
import Lean

open STLTableau.Section3

/-! Check the declarations for the main results in `docs/correspondence.md`. -/

run_elab do
  let names : Array Lean.Name := #[
    -- Formula preprocessing
    ``STLTableau.Formula.normalizeForTableau,
    ``STLTableau.Formula.satisfies_normalizeForTableau,
    ``STLTableau.Formula.mixedReady_normalizeForTableau,
    ``STLTableau.Formula.satisfies_normalizeViolation,
    -- Theorem 3.13 and Proposition 3.14
    ``STLTableau.rule_correct,
    ``STLTableau.rule_complete_preserving,
    ``STLTableau.UnboundedClocked.rule_correct,
    ``STLTableau.UnboundedClocked.rule_complete_preserving,
    -- Expansion levels and termination
    ``STLTableau.Section3.ClosureCatalogue.BranchwisePExpansion,
    ``STLTableau.Section3.ConcreteContextual.AlphaBranchwisePExpansion,
    ``STLTableau.Section3.ConcreteContextual.alphaBranchwiseExpansionLevel,
    ``STLTableau.Section3.ConcreteContextual.orbitBranchwiseLevelRank,
    ``STLTableau.Section3.ConcreteContextual.orbitBranchwiseLevelRank_eq,
    ``STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_eventually_zero,
    ``ConcreteContextual.all_closures_mem_branchwise_level_at_first_orbit_rank_zero,
    -- Theorems 4.14 and 4.22
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_holds_of_atomicProjection,
    ``STLTableau.Section3.ConcreteContextual.satisfied_alphaBranchwise_preserving,
    ``STLTableau.Section3.ConcreteContextual.satisfied_closure_branchwise_path,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_numeric,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_guided_path,
    -- Theorems 4.32 and 4.34
    ``STLTableau.Section4.Generated.recognizes_iff_formula,
    ``STLTableau.Section4.Generated.formula_of_recognizes,
    ``STLTableau.Section4.Generated.recognizes_of_formula,
    -- Lemmas 4.35 and 4.36
    ``STLTableau.Section4.Finiteness.CompletedDerivation.Admitted,
    ``STLTableau.Section4.Finiteness.CompletedDerivation.Tree,
    ``STLTableau.Section4.Finiteness.PairedTableau.tableau,
    ``STLTableau.Section4.Finiteness.simplifiedTableau,
    ``STLTableau.Section4.Finiteness.simplified_fullTrace_and_formula_of_atomic,
    ``STLTableau.Section4.Finiteness.simplified_satisfied_accepting_iff,
    ``STLTableau.Section4.Finiteness.finiteTableau_bounded_accepting_path,
    -- Theorem 4.37
    ``STLTableau.Section4.Finiteness.finiteTableau,
    ``STLTableau.Section4.Finiteness.finiteTableau_states_finite,
    ``STLTableau.Section4.Finiteness.finiteTableau_clocks_finite,
    ``STLTableau.Section4.Finiteness.finiteTableau_clock_card_le,
    ``STLTableau.Section4.Finiteness.finiteTableau_state_card_le,
    ``STLTableau.Section4.Finiteness.finiteTableau_sound,
    ``STLTableau.Section4.Finiteness.finiteTableau_complete,
    ``STLTableau.Section4.Finiteness.finiteTableau_recognizes_normalized_input,
    -- Lemma 5.5
    ``STLTableau.Section4.Tableau.CanonicalExecution,
    ``STLTableau.Section4.Tableau.CanonicalExecution.GoalInduces,
    ``STLTableau.Section4.Tableau.CanonicalReaches,
    ``STLTableau.Section4.Finiteness.canonical_translation_correctness,
    ``STLTableau.Section4.Finiteness.canonical_forward_of_initialFlow,
    -- Bounded zero-time jumps
    ``STLTableau.HybridAutomaton.boundedZeroTimeExtension_trajectory_iff,
    ``STLTableau.HybridAutomaton.initialJumpClosure_trajectory_iff,
    -- Theorem 5.7
    ``STLTableau.Section4.Finiteness.canonical_model_checking,
    ``STLTableau.Section4.Finiteness.canonical_negation_goal,
    ``STLTableau.Section4.Finiteness.canonical_negation_no_goal,
    -- Corollary 5.8
    ``STLTableau.Section4.Finiteness.canonical_robust_model_checking,
    ``STLTableau.Formula.robustCounterInput,
    ``STLTableau.Formula.satisfies_robustCounterInput_of_violation,
    ``STLTableau.Formula.robustness_le_of_satisfies_robustCounterInput,
    -- Worked examples
    ``STLTableau.Examples.TableauConstruction.release_generated_accepting_path,
  ]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
  Lean.logInfo m!"Checked {names.size} declarations. They use only standard Lean axioms."
