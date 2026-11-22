import STLTableaux.Finiteness.Derivation.Selection.NextEntryConditions
open STLTableau.Section4.Finiteness
#check SelectedTree.ledger_upper_successor_conditions
#check endpoint_next_of_reset_agreement
#check SelectedTree.ledger_bounded_endpoint
#print axioms SelectedTree.ledger_upper_successor_conditions
#print axioms endpoint_next_of_reset_agreement
#print axioms SelectedTree.ledger_bounded_endpoint
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.ledger_upper_successor_conditions,
    ``endpoint_next_of_reset_agreement, ``SelectedTree.ledger_bounded_endpoint] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
