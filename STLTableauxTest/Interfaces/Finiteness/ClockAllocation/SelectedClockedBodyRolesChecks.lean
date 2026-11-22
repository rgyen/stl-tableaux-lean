import STLTableaux.Finiteness.ClockAllocation.SelectedClockedBodyRoles
open STLTableau.Section4.Finiteness
#print axioms RetrospectiveLeft.role_zero
#print axioms RetrospectiveLeft.nonzero_ne_left
#print axioms SelectedTree.clocked_body_role_owner
#print axioms SelectedTree.clocked_body_nonzero_unique
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RetrospectiveLeft.role_zero, ``RetrospectiveLeft.nonzero_ne_left, ``SelectedTree.clocked_body_role_owner, ``SelectedTree.clocked_body_nonzero_unique] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
