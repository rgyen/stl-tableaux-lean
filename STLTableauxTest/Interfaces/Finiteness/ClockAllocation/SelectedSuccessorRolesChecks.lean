import STLTableaux.Finiteness.ClockAllocation.SelectedSuccessorRoles
open STLTableau.Section4.Finiteness
#print axioms selectedNextRole_iff
#print axioms selectedLedgerOwner_of_left
#print axioms SelectedTree.selectedNextRole_right_unique
#print axioms SelectedTree.selectedNextRole_owner_cover
#print axioms SelectedTree.selectedNextRole_occupied_bound
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``selectedNextRole_iff, ``selectedLedgerOwner_of_left, ``SelectedTree.selectedNextRole_right_unique, ``SelectedTree.selectedNextRole_owner_cover, ``SelectedTree.selectedNextRole_occupied_bound] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
