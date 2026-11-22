import STLTableaux.Finiteness.ClockAllocation.SelectedAnnotationRoleTyping
open STLTableau.Section4.Finiteness
#check SelectedTree.retrospective_output_role
#print axioms SelectedTree.retrospective_output_role
#check SelectedTree.retrospective_literal_constant_typed
#print axioms SelectedTree.retrospective_literal_constant_typed
#check SelectedTree.retrospective_current_resets_typed
#print axioms SelectedTree.retrospective_current_resets_typed
#check SelectedTree.retrospective_next_guards_typed
#print axioms SelectedTree.retrospective_next_guards_typed
#check SelectedTree.retrospective_next_resets_typed
#print axioms SelectedTree.retrospective_next_resets_typed
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.retrospective_output_role, ``SelectedTree.retrospective_literal_constant_typed, ``SelectedTree.retrospective_current_resets_typed, ``SelectedTree.retrospective_next_guards_typed, ``SelectedTree.retrospective_next_resets_typed] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
