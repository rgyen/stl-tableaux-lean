import STLTableaux.Finiteness.ClockAllocation.SelectedOpeningOwners
open STLTableau.Section4.Finiteness
#check SelectedTree.plain_ledger_event_unique
#check SelectedTree.opening_left_unique
#check SelectedTree.opening_family_unique
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.plain_ledger_event_unique, ``SelectedTree.opening_left_unique, ``SelectedTree.opening_family_unique] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
