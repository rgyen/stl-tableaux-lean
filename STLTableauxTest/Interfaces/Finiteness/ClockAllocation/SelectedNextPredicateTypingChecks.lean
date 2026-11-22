import STLTableaux.Finiteness.ClockAllocation.SelectedNextPredicateTyping
open STLTableau.Section4.Finiteness
#check SelectedTree.retrospective_next_predicates_typed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let name := ``SelectedTree.retrospective_next_predicates_typed
  let axs ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axs}"
  for axiomName in axs do
    unless allowed.contains axiomName do
      throwError "{name} depends on unapproved axiom: {axiomName}"
