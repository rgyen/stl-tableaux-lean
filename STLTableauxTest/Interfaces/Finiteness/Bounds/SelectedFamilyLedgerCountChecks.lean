import STLTableaux.Finiteness.Bounds.SelectedFamilyLedgerCount
open STLTableau.Section4.Finiteness
#check SelectedTree.bounded_family_ledger_le_input
#check SelectedTree.upper_family_ledger_le_one
#check SelectedTree.plain_opening_ledger_le_one
#check SelectedTree.family_ledger_bounds
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.bounded_family_ledger_le_input, ``SelectedTree.upper_family_ledger_le_one, ``SelectedTree.plain_opening_ledger_le_one, ``SelectedTree.family_ledger_bounds] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
