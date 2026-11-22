import STLTableaux.Finiteness.ClockAllocation.SelectedRolePermutation
open STLTableau.Section4.Finiteness
#check SelectedTree.role_domain_covers_output
#print axioms SelectedTree.role_domain_covers_output
#check SelectedTree.exists_role_permutation
#print axioms SelectedTree.exists_role_permutation
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.role_domain_covers_output, ``SelectedTree.exists_role_permutation] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
