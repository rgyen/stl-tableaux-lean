import STLTableaux.Finiteness.Bounds.TruthIntervalCount

open STLTableau.Section4.Finiteness
#check finite_temporal_truth_blocks_bound
#check ended_truth_blocks_bound
#print axioms finite_temporal_truth_blocks_bound
#print axioms ended_truth_blocks_bound
#check endpoint_bound_le_conservative_budget
#print axioms endpoint_bound_le_conservative_budget

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finite_temporal_truth_blocks_bound, ``ended_truth_blocks_bound,
      ``endpoint_bound_le_conservative_budget] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
