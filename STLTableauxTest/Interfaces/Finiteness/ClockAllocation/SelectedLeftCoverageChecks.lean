import STLTableaux.Finiteness.ClockAllocation.SelectedLeftCoverage
open STLTableau.Section4.Finiteness
#check SelectedTree.ledger_sources_below
#check SelectedTree.opening_signature_mem
#check SelectedTree.opening_left_coverage
#check SelectedTree.ledger_clocked_left_coverage
#check SelectedTree.ledger_clocked_left_family
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.ledger_sources_below, ``SelectedTree.opening_signature_mem, ``SelectedTree.opening_left_coverage, ``SelectedTree.ledger_clocked_left_coverage, ``SelectedTree.ledger_clocked_left_family] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
