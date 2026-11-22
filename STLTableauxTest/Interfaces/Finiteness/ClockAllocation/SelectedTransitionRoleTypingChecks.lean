import STLTableaux.Finiteness.ClockAllocation.SelectedTransitionRoleTyping
open STLTableau.Section4.Finiteness
#check SelectedTree.retrospective_transition_typed
#print axioms SelectedTree.retrospective_transition_typed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.retrospective_transition_typed] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
