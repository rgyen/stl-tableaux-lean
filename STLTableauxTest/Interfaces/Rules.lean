import STLTableaux.Compatibility

/-! Interface and axiom checks for the Section 3 rules and related results,
including Theorem 3.13 and Proposition 3.14. -/
#check STLTableau.HybridAutomaton.IsTrajectory
#check STLTableau.rule_correct
#check STLTableau.rule_sound_without_past
#check STLTableau.rule_correct_preserving
#check STLTableau.upper_decomposition_zero
#check STLTableau.satisfies_upper_iff_reset_bounded_and_plain
#check STLTableau.pastSeparated_iff_max
#check STLTableau.satisfies_upper_iff_reset_split_of_contains
#check STLTableau.always_interval_vacuous
#check STLTableau.interval_eventually
#check STLTableau.interval_eventually_stable
#check STLTableau.Section3.Predicate.predicate_merge_connected
#check STLTableau.Section3.Judgement.predicate_merge_connected
#check STLTableau.HorizonInput.compile_correct
#check STLTableau.HorizonInput.compile_ready
#check STLTableau.Claims.PrintedSplitFixedMarker
#check STLTableau.Claims.PrintedSplitChosenMarker
#check STLTableau.Counterexamples.not_printed_opening_fixed_marker
#check STLTableau.Counterexamples.not_printed_split_fixed_marker
#check STLTableau.Counterexamples.not_printed_split_chosen_marker

#print axioms STLTableau.conj_idem
#print axioms STLTableau.reset_conj_reset_equiv_union
#print axioms STLTableau.reset_conj_nested_equiv_union
#print axioms STLTableau.satisfies_plain_eventually_iff_reset_upper
#print axioms STLTableau.satisfies_plain_always_iff_reset_upper
#print axioms STLTableau.upper_decomposition_zero
#print axioms STLTableau.satisfies_upper_iff_reset_bounded_and_plain
#print axioms STLTableau.next_upper_implies_upper
#print axioms STLTableau.next_bounded_implies_bounded
#print axioms STLTableau.next_reset_bounded_implies_upper
#print axioms STLTableau.merge_at
#print axioms STLTableau.pastSeparated_iff_max
#print axioms STLTableau.satisfies_upper_iff_reset_split_of_contains
#print axioms STLTableau.always_interval_vacuous
#print axioms STLTableau.interval_eventually
#print axioms STLTableau.interval_eventually_stable
#print axioms STLTableau.HorizonInput.compile_correct
#print axioms STLTableau.HorizonInput.compile_ready
#print axioms STLTableau.predicate_iff_residual
#print axioms STLTableau.rule_sound
#print axioms STLTableau.rule_sound_without_past
#print axioms STLTableau.rule_complete
#print axioms STLTableau.rule_complete_preserving
#print axioms STLTableau.rule_correct_preserving
#print axioms STLTableau.Counterexamples.printed_upper_split_judgement_fails
#print axioms STLTableau.Counterexamples.next_reset_same_clock_fails
#print axioms STLTableau.Counterexamples.residual_always_is_strictly_weaker
#print axioms STLTableau.Counterexamples.not_printed_opening_fixed_marker
#print axioms STLTableau.Counterexamples.not_printed_split_fixed_marker
#print axioms STLTableau.Counterexamples.not_printed_split_chosen_marker

-- Allow only propositional extensionality, choice, and quotient soundness.
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``STLTableau.UnboundedClocked.rule_sound,
      ``STLTableau.predicate_merge_connected,
      ``STLTableau.UnboundedClocked.predicate_merge_connected,
      ``STLTableau.Section3.Predicate.predicate_merge_connected,
      ``STLTableau.Section3.Judgement.predicate_merge_connected,
      ``STLTableau.Section3.connectedMergeCondition_elapse_iff,
      ``STLTableau.Section3.Predicate.predicate_merge_connected_after_elapse,
      ``STLTableau.Section3.StateForm.merge_connected_pair_holds,
      ``STLTableau.Section3.ConnectedPrefix.holds_iff,
      ``STLTableau.predicate_merge_bounded_connected,
      ``STLTableau.UnboundedClocked.predicate_merge_bounded_connected,
      ``STLTableau.Section3.Predicate.predicate_merge_bounded_connected,
      ``STLTableau.Section3.StateForm.merge_connected_prefix_holds,
      ``STLTableau.Section3.StateForm.merge_connected_bounded_pair_holds,
      ``STLTableau.Section3.ConnectedDefer.predicates_merge,
      ``STLTableau.UnboundedClocked.rule_sound_without_past,
      ``STLTableau.UnboundedClocked.rule_complete,
      ``STLTableau.UnboundedClocked.rule_correct_preserving,
      ``STLTableau.UnboundedClocked.opening_correct,
      ``STLTableau.UnboundedClocked.opening_preserves,
      ``STLTableau.UnboundedClocked.reset_split_correct_of_contains,
      ``STLTableau.UnboundedClocked.merge_at,
      ``STLTableau.Section3.Judgement.holds_ofFinite,
      ``STLTableau.Section3.Judgement.holds_ofUnbounded,
      ``STLTableau.Section3.Judgement.holds_congr_of_agree,
      ``STLTableau.Section3.Judgement.reset_conj_reset_equiv_union,
      ``STLTableau.Section3.Judgement.reset_conj_nested_equiv_union,
      ``STLTableau.rule_sound,
      ``STLTableau.rule_sound_without_past,
      ``STLTableau.rule_complete,
      ``STLTableau.rule_correct,
      ``STLTableau.rule_complete_preserving,
      ``STLTableau.rule_correct_preserving,
      ``STLTableau.satisfies_upper_iff_reset_bounded_and_plain,
      ``STLTableau.satisfies_upper_iff_reset_split_of_contains,
      ``STLTableau.always_interval_vacuous,
      ``STLTableau.interval_eventually,
      ``STLTableau.interval_eventually_stable,
      ``STLTableau.HorizonInput.compile_correct,
      ``STLTableau.HorizonInput.compile_ready,
      ``STLTableau.Counterexamples.printed_upper_split_judgement_fails,
      ``STLTableau.Counterexamples.next_reset_same_clock_fails,
      ``STLTableau.Counterexamples.not_printed_opening_fixed_marker,
      ``STLTableau.Counterexamples.not_printed_split_fixed_marker,
      ``STLTableau.Counterexamples.not_printed_split_chosen_marker] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
