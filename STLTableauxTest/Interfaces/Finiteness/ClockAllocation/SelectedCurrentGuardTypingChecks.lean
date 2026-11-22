import STLTableaux.Finiteness.ClockAllocation.SelectedCurrentGuardTyping
open STLTableau.Section4.Finiteness
#check SelectedTree.retrospective_current_guards_typed
#check SelectedTree.retrospective_current_predicates_guards_typed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.retrospective_current_guards_typed, ``SelectedTree.retrospective_current_predicates_guards_typed] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
