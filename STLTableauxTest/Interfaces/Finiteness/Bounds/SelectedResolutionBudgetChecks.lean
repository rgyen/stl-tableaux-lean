import STLTableaux.Finiteness.Bounds.SelectedResolutionBudget
open STLTableau.Section4.Finiteness
#check root_inventory_card_le_literal_size
#check temporal_origin_cap_le_nine_resolution
#check root_origin_budget_le_nine_inventory_resolution
#check root_step_budget_le_eleven_inventory_resolution
#check root_origin_budget_le_nine_size_resolution
#check root_step_budget_le_eleven_size_resolution
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``root_inventory_card_le_literal_size, ``temporal_origin_cap_le_nine_resolution, ``root_origin_budget_le_nine_inventory_resolution, ``root_step_budget_le_eleven_inventory_resolution, ``root_origin_budget_le_nine_size_resolution, ``root_step_budget_le_eleven_size_resolution] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
