import STLTableaux.Finiteness.Bounds.SelectedRetainedCount
open STLTableau.Section4.Finiteness
#check SelectedTree.plain_ledger_sublist
#check rawLedger_length_decomposition
#check SelectedTree.bounded_ledger_length_bound
#check SelectedTree.rawLedger_length_bound
#check SelectedTree.current_locals_card_bound
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.plain_ledger_sublist, ``rawLedger_length_decomposition,
    ``SelectedTree.bounded_ledger_length_bound, ``SelectedTree.rawLedger_length_bound,
    ``SelectedTree.current_locals_card_bound] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
