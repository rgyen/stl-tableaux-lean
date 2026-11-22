import STLTableaux.Finiteness.ClockAllocation.SelectedRoleMap
open STLTableau.Section4.Finiteness
#check RetrospectiveLeft.functional_of_eq
#check RetrospectiveLeft.injective_of_eq
#check RetrospectiveRole.functional_of_eq
#check RetrospectiveRole.injective_of_eq
#print axioms RetrospectiveRole.functional_of_eq
#print axioms RetrospectiveRole.injective_of_eq
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``alternateRight_ne_zero, ``SlotFrame.alternateRight_unused,
    ``SelectedTree.used_event_outside_input, ``RetrospectiveRole.support,
    ``RetrospectiveLeft.functional_of_eq, ``RetrospectiveLeft.injective_of_eq,
    ``RetrospectiveRole.functional_of_eq, ``RetrospectiveRole.injective_of_eq] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
