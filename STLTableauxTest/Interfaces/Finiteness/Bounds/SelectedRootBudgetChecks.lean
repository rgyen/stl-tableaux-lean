import STLTableaux.Finiteness.Bounds.SelectedRootBudget
open STLTableau.Section4.Finiteness
#print axioms InputOrigins.bounded_domain_card_root
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``InputOrigins.bounded_domain_card_root do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
