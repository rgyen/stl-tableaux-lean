import STLTableaux.Compatibility

/-! Check the Section 4 closure and tableau declarations and their axioms,
through tableau completeness (Theorem 4.34). -/

#check STLTableau.Section3.SyntacticallySubsumed.sound
#check STLTableau.Section3.ClosureCatalogue.closed_holds_of_atomicProjection
#check STLTableau.Section4.Trace.holds_congr_of_agree
#check STLTableau.Section4.Trace.holdsWith_mono
#check STLTableau.Section4.Trace.holdsWith_congr
#check STLTableau.Section4.Trace.length_le_remaining
#check STLTableau.Section4.Tableau.recognizes_of_closed_trace
#check STLTableau.Section4Counterexamples.normalized_arbitrary_generator_stability_gap
#check STLTableau.branch_nonpast_parts
#check STLTableau.UnboundedClocked.branch_nonpast_preserves
#check STLTableau.UnboundedClocked.opening_nonpast_preserves
#check STLTableau.ConcreteRule.compatible_branch_preserving_current
#check STLTableau.AlphaBranchRepresentation.satisfied_pExpansion_of_rule_complete_up_to_alpha
#check STLTableau.AlphaBranchRepresentation.ruleClosed_alphaNext_iff
#check STLTableau.AlphaBranchRepresentation.rank_alphaNext

#check STLTableau.Section3.ConcreteFinite.branch_normalization
#check STLTableau.Section3.ConcreteFinite.closed_holds_of_atomicProjection
#check STLTableau.ConcreteRule.branch_current_subformula
#check STLTableau.AlphaBranchRepresentation.closure_preservesCurrentStability
#check STLTableau.AlphaBranchRepresentation.satisfied_alphaClosure_exists

#check STLTableau.Section4Counterexamples.normalized_generator_closed_extension_counterexample

#check STLTableau.Section3.ConcreteInfinite.branch_normalization
#check STLTableau.Section3.ConcreteInfinite.opening_normalization
#check STLTableau.Section3.ConcreteMixed.closed_holds_of_atomicProjection

#check STLTableau.Section3.Judgement.underlyingStable_plain
#check STLTableau.Section3.GeneratorStability.finite_branch_subformula
#check STLTableau.Section3.GeneratorStability.finite_branch_stable
#check STLTableau.Section3.GeneratorStability.infinite_branch_subformula
#check STLTableau.Section3.GeneratorStability.infinite_branch_stable
#check STLTableau.Section3.GeneratorStability.opening_branch_subformula
#check STLTableau.Section3.GeneratorStability.opening_branch_stable
#check STLTableau.Section4Counterexamples.same_variable_generator_closed_extension_counterexample

#check STLTableau.Section3.FaithfulClosure.satisfied_closure_exists
#check STLTableau.Section4.Generated.generator_path_exists
#check STLTableau.Section3.FaithfulClosure.preserving_step
#check STLTableau.Section3.ConcreteContextual.union_rank_decrease
#check STLTableau.Section3.SyntacticallySubsumed.evaluatedInvariant

#check STLTableau.Section4.Generated.generator_path_exists_with_closure
#check STLTableau.Section3.ConcreteMixed.branch_freeClocks
#check STLTableau.Section4.Generated.recognizes_of_satisfied_closed_generator
#check STLTableau.Section4.Generated.recognizes_of_formula
#check STLTableau.Section3.NumericBranch.contextual_preserves
#check STLTableau.Section3.NumericBranch.contextual_sound
#check STLTableau.Section3.ConcreteContextual.minimal_closure_numeric
#check STLTableau.Section3.ConcreteContextual.minimal_closure_holds_of_atomicProjection
#check STLTableau.Section3.ConcreteContextual.closure_ready
#check STLTableau.Section4.Generated.formula_of_recognizes
#check STLTableau.Section4.Generated.recognizes_iff_formula
#check STLTableau.Section3.TransitionForm.tnf_exists_of_compatible
#check STLTableau.Section3.TransitionForm.tnf_exists_up_to_alpha
#check STLTableau.Section3.SyntacticallySubsumed.type_subsumption
#check STLTableau.Section3.SyntacticallySubsumed.bodyFreeClocks_mono
#check STLTableau.Section3.GeneralClosure.satisfied_closure_exists_up_to_next_alpha
#check STLTableau.Section4.Generated.trace_invariant
#check STLTableau.Section4.Generated.trace_equivalence
#check STLTableau.Section4.Generated.trace_ftrace_implication

-- Single-predicate expansion levels and rank (Definitions 4.15, 4.17 and 4.18).
#check STLTableau.Section3.ClosureCatalogue.BranchwisePExpansion
#check STLTableau.Section3.ConcreteContextual.AlphaBranchwisePExpansion
#check STLTableau.Section3.ConcreteContextual.branchwiseExpansionLevel
#check STLTableau.Section3.ConcreteContextual.alphaBranchwiseExpansionLevel
#check STLTableau.Section3.ConcreteContextual.alphaBranchwiseLevelRank
#check STLTableau.Section3.ConcreteContextual.alpha_branchwise_freshProvenance
#check STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_decrease
#check STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_eventually_zero
#check STLTableau.Section3.ConcreteContextual.branchwise_of_pExpansion
#check STLTableau.Section3.ConcreteContextual.satisfied_alphaBranchwise_preserving
#check STLTableau.Section3.ConcreteContextual.minimal_closure_guided_path
#check STLTableau.Section3.ConcreteContextual.minimal_closure_numeric_of_guardTypes
#check STLTableau.Section3.ConcreteContextual.minimal_closure_mem_branchwise_level
#check STLTableau.Section3.ConcreteContextual.minimal_closure_mem_fixed_branchwise_rounds
#check STLTableau.Section3.ConcreteContextual.satisfied_closure_branchwise_path
open STLTableau.Section3.ConcreteContextual in
#check all_closures_mem_branchwise_level_at_first_rank_zero
open STLTableau.Section3.ConcreteContextual in
#check all_closures_mem_branchwise_level_at_first_orbit_rank_zero
open STLTableau.Section3.ConcreteContextual in
#check orbitBranchwiseLevelRank_eq

-- Auxiliary expansion by complete rounds.
#check STLTableau.Section3.ClosureCatalogue.PExpansion
#check STLTableau.Section3.ConcreteContextual.satisfied_pExpansion_preserving
#check STLTableau.Section3.ClosureCatalogue.expansionLevel
#check STLTableau.Section3.ConcreteContextual.alphaExpansionLevel
#check STLTableau.Section3.ConcreteContextual.literalLevelRank
#check STLTableau.Section3.ConcreteContextual.alphaLevelRank
#check STLTableau.Section3.ConcreteContextual.literal_level_rank_decrease
#check STLTableau.Section3.ConcreteContextual.alpha_level_rank_decrease
#check STLTableau.Section3.ConcreteContextual.literal_level_rank_eventually_zero
#check STLTableau.Section3.ConcreteContextual.alpha_level_rank_eventually_zero
#check STLTableau.Section3.ConcreteContextual.satisfied_closure_exists_via_rounds
#check STLTableau.Section3.ConcreteContextual.minimal_closure_mem_expansion_level
#check STLTableau.Section3.ConcreteContextual.minimal_closure_expansion_sequence

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
    ``STLTableau.Section3.ConcreteContextual.orbitBranchwiseLevelRank_eq,
    ``STLTableau.Section3.ConcreteContextual.all_closures_mem_branchwise_level_at_first_orbit_rank_zero,
    ``STLTableau.Section3.ConcreteContextual.alpha_branchwise_freshProvenance,
    ``STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.alpha_branchwise_rank_eventually_zero,
    ``STLTableau.Section3.ConcreteContextual.branchwise_of_pExpansion,
    ``STLTableau.Section3.ConcreteContextual.satisfied_alphaBranchwise_preserving,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_guided_path,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_numeric_of_guardTypes,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_mem_branchwise_level,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_mem_fixed_branchwise_rounds,
    ``STLTableau.Section3.ConcreteContextual.satisfied_closure_branchwise_path,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_expansion_sequence,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_mem_expansion_level,
    ``STLTableau.Section3.ConcreteContextual.pExpansion_new_current_witness,
    ``STLTableau.Section3.ConcreteContextual.pExpansion_new_current_complexity,
    ``STLTableau.Section3.ConcreteContextual.literal_level_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_rank_decrease,
    ``STLTableau.Section3.ConcreteContextual.literal_level_rank_eventually_zero,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_rank_eventually_zero,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_satisfied,
    ``STLTableau.Section3.ConcreteContextual.alpha_level_source,
    ``STLTableau.Section3.ExpansionFamily.familyRank_attained,
    ``STLTableau.Section3.ExpansionFamily.familyRank_zero_iff_closed,
    ``STLTableau.Section3.ConcreteContextual.satisfied_closure_via_expansion_levels,
    ``STLTableau.Section3.ConcreteContextual.satisfied_closure_exists_via_rounds,
    ``STLTableau.Section3.ClosureCatalogue.pExpansion_exists_below,
    ``STLTableau.Section3.ConcreteContextual.satisfied_pExpansion_preserving,
    ``STLTableau.Section3.TransitionForm.tnf_exists_of_compatible,
    ``STLTableau.Section3.TransitionForm.tnf_exists_up_to_alpha,
    ``STLTableau.Section3.SyntacticallySubsumed.type_subsumption,
    ``STLTableau.Section3.SyntacticallySubsumed.bodyFreeClocks_mono,
    ``STLTableau.Section3.GeneralClosure.satisfied_closure_exists_up_to_next_alpha,
    ``STLTableau.Section4.Generated.trace_invariant,
    ``STLTableau.Section4.Generated.trace_equivalence,
    ``STLTableau.Section4.Generated.trace_ftrace_implication,
    ``STLTableau.Section4.Trace.ScopePreservingSubsumed.sound,
    ``STLTableau.Section4.Generated.atomic_trace_subsumed_fullTrace,
    ``STLTableau.Section4.Generated.fullTrace_freeClocks_subset_generator,
    ``STLTableau.Section3.finite_numeric_iff_positional,
    ``STLTableau.Section4.Generated.formula_of_recognizes,
    ``STLTableau.Section4.Generated.fullTrace_and_generator_of_atomic_trace,
    ``STLTableau.Section4.Generated.recognizes_iff_formula,
    ``STLTableau.Section3.ConcreteContextual.closure_ready,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_numeric,
    ``STLTableau.Section3.ConcreteContextual.minimal_closure_holds_of_atomicProjection,
    ``STLTableau.Section3.NumericBranch.contextual_preserves,
    ``STLTableau.Section3.NumericBranch.contextual_sound,
    ``STLTableau.Section3.TransitionForm.numeric_of_invariant,
    ``STLTableau.Section4.Generated.recognizes_of_satisfied_closed_generator,
    ``STLTableau.Section4.Generated.recognizes_of_formula,
    ``STLTableau.Section3.FaithfulClosure.satisfied_closure_exists_free,
    ``STLTableau.Section3.SyntacticallySubsumed.nonPredicateHolds,
    ``STLTableau.Section3.ConcreteMixed.branch_freeClocks,
    ``STLTableau.Section3.TransitionForm.freeClocks_union_subset,
    ``STLTableau.Section3.TransitionForm.freeClocks_underReset_subset,
    ``STLTableau.Section4.Generated.generator_path_exists_with_closure,
    ``STLTableau.Section3.FaithfulClosure.satisfied_closure_exists,
    ``STLTableau.Section4.Generated.generator_path_exists,
    ``STLTableau.Section3.FaithfulClosure.preserving_step,
    ``STLTableau.Section3.ConcreteContextual.union_rank_decrease,
    ``STLTableau.Section3.SyntacticallySubsumed.evaluatedInvariant,
    ``STLTableau.Section3.Judgement.underlyingStable_plain,
    ``STLTableau.Section3.GeneratorStability.finite_branch_subformula,
    ``STLTableau.Section3.GeneratorStability.finite_branch_stable,
    ``STLTableau.Section3.GeneratorStability.infinite_branch_subformula,
    ``STLTableau.Section3.GeneratorStability.infinite_branch_stable,
    ``STLTableau.Section3.GeneratorStability.opening_branch_subformula,
    ``STLTableau.Section3.GeneratorStability.opening_branch_stable,
    ``STLTableau.Section4Counterexamples.same_variable_generator_closed_extension_counterexample,
    ``STLTableau.Section3.ConcreteInfinite.branch_normalization,
    ``STLTableau.Section3.ConcreteInfinite.opening_normalization,
    ``STLTableau.Section3.ConcreteMixed.closed_holds_of_atomicProjection,
    ``STLTableau.Section4Counterexamples.normalized_generator_closed_extension_counterexample,
    ``STLTableau.Section3.ConcreteFinite.branch_normalization,
    ``STLTableau.Section3.ConcreteFinite.closed_holds_of_atomicProjection,
    ``STLTableau.ConcreteRule.branch_current_subformula,
    ``STLTableau.AlphaBranchRepresentation.closure_preservesCurrentStability,
    ``STLTableau.AlphaBranchRepresentation.satisfied_alphaClosure_exists,
    ``STLTableau.Section3.SyntacticallySubsumed.sound,
    ``STLTableau.Section3.ClosureCatalogue.closed_holds_of_atomicProjection,
    ``STLTableau.Section4.Trace.holds_congr_of_agree,
    ``STLTableau.Section4.Trace.holdsWith_mono,
    ``STLTableau.Section4.Trace.holdsWith_congr,
    ``STLTableau.Section4.Trace.length_le_remaining,
    ``STLTableau.Section4.Tableau.recognizes_of_closed_trace,
    ``STLTableau.Section4Counterexamples.normalized_arbitrary_generator_stability_gap,
    ``STLTableau.branch_nonpast_parts,
    ``STLTableau.UnboundedClocked.branch_nonpast_preserves,
    ``STLTableau.UnboundedClocked.opening_nonpast_preserves,
    ``STLTableau.ConcreteRule.compatible_branch_preserving_current,
    ``STLTableau.AlphaBranchRepresentation.satisfied_pExpansion_of_rule_complete_up_to_alpha,
    ``STLTableau.AlphaBranchRepresentation.ruleClosed_alphaNext_iff,
    ``STLTableau.AlphaBranchRepresentation.rank_alphaNext] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
