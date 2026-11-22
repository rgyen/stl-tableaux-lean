import STLTableaux.Finiteness.ClockAllocation.SelectedSourceRoleTyping
open STLTableau.Section4.Finiteness
#check SlotFrame.PredicateTyped.mono
#check RetrospectiveLeft.toRole
#check SelectedTree.retrospective_ledger_source_typed
#check SelectedTree.retrospective_current_predicates_typed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SlotFrame.PredicateTyped.mono, ``RetrospectiveLeft.toRole, ``SelectedTree.retrospective_ledger_source_typed, ``SelectedTree.retrospective_current_predicates_typed] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
