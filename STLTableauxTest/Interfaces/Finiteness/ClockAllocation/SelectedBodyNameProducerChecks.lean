import STLTableaux.Finiteness.ClockAllocation.SelectedBodyNameProducer
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.ledger_body_name_producer
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``SelectedTree.ledger_body_name_producer do
    unless allowed.contains ax do
      throwError "unapproved axiom: {ax}"
