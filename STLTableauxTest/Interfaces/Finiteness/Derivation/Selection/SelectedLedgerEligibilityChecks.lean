import STLTableaux.Finiteness.Derivation.Selection.SelectedLedgerEligibility
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.ledger_source_not_eligible
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``SelectedTree.ledger_source_not_eligible do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
