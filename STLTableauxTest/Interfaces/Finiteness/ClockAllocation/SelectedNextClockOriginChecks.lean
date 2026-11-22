import STLTableaux.Finiteness.ClockAllocation.SelectedNextClockOrigin
open STLTableau.Section4.Finiteness
#print axioms RawBranch.plain_next_clocks_empty
#print axioms SelectedTree.next_clock_ledger_origin
#print axioms SelectedTree.next_clock_clocked_ledger_origin
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.plain_next_clocks_empty, ``SelectedTree.next_clock_ledger_origin, ``SelectedTree.next_clock_clocked_ledger_origin] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
