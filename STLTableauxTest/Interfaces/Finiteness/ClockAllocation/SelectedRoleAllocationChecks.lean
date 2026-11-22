import STLTableaux.Finiteness.ClockAllocation.SelectedRoleAllocation
open STLTableau.Section4.Finiteness
#check retrospectiveRoleMap_iff
#print axioms retrospectiveRoleMap_iff
#check retrospectiveRoleMap_input
#print axioms retrospectiveRoleMap_input
#check SelectedTree.retrospective_used_name_coverage
#print axioms SelectedTree.retrospective_used_name_coverage
#check SelectedTree.retrospective_domain
#print axioms SelectedTree.retrospective_domain
#check SelectedTree.roleAllocation
#print axioms SelectedTree.roleAllocation
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``retrospectiveRoleMap_iff, ``retrospectiveRoleMap_input, ``SelectedTree.retrospective_used_name_coverage, ``SelectedTree.retrospective_domain, ``SelectedTree.roleAllocation] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
