import STLTableaux.Finiteness.Inventory.RootSlotPalette
open STLTableau.Section4.Finiteness
#print axioms rootSlot_clockAt
#print axioms rootSlot_clockAt_injective
#print axioms rootSlot_family_card
#print axioms rootSlot_card
#print axioms rootSlot_card_budget
#print axioms rootSlot_card_le_resolution
#print axioms rootSlot_card_le_size_resolution
#print axioms rootSlot_clocks_card_le_resolution
#print axioms rootSlot_sparse_exponent_le_resolution
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``rootSlot_clockAt, ``rootSlot_clockAt_injective, ``rootSlot_family_card, ``rootSlot_card, ``rootSlot_card_budget, ``rootSlot_card_le_resolution, ``rootSlot_card_le_size_resolution, ``rootSlot_clocks_card_le_resolution, ``rootSlot_sparse_exponent_le_resolution] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
