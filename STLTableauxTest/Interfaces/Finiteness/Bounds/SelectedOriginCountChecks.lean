import STLTableaux.Finiteness.Bounds.SelectedOriginCount
open STLTableau.Section4.Finiteness
#check InputOrigins.connectedFamily_card_le_one
#check InputOrigins.endedFamily_endpoint_window
#check InputOrigins.endedFamily_card_bound
#check InputOrigins.boundedFamily_card_bound
#check InputOrigins.boundedFamily_card_floor_bound
#check TruthPartitionIntervals.unbounded_truthBlock_unique
#check InputOrigins.unboundedFamily_card_le_one
#check InputOrigins.unbounded_endedFamily_empty_of_truth
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``InputOrigins.connectedFamily_card_le_one, ``InputOrigins.endedFamily_endpoint_window,
    ``InputOrigins.endedFamily_card_bound, ``InputOrigins.boundedFamily_card_bound,
    ``InputOrigins.boundedFamily_card_floor_bound, ``TruthPartitionIntervals.unbounded_truthBlock_unique,
    ``InputOrigins.unboundedFamily_card_le_one, ``InputOrigins.unbounded_endedFamily_empty_of_truth] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
