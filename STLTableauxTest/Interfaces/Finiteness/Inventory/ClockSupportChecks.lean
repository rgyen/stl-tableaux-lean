import STLTableaux.Finiteness.Inventory.ClockSupport

open STLTableau.Section4.Finiteness.FiniteInventory

#check within_support
#check transition_allClocks_subset
#check transition_allClocks_card_le
#print axioms within_support
#print axioms transition_allClocks_subset
#print axioms transition_allClocks_card_le

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``within_support, ``transition_allClocks_subset,
      ``transition_allClocks_card_le] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
