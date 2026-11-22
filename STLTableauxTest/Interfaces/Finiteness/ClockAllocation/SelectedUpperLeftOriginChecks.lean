import STLTableaux.Finiteness.ClockAllocation.SelectedUpperLeftOrigin
open STLTableau.Section4.Finiteness
#check SelectedTree.clocked_ledger_left_origin
#check SelectedTree.upper_ledger_left_trace
#check SelectedTree.upper_ledger_left_origin
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.clocked_ledger_left_origin, ``SelectedTree.upper_ledger_left_trace, ``SelectedTree.upper_ledger_left_origin] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
