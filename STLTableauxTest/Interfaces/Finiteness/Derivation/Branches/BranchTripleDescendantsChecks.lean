import STLTableaux.Finiteness.Derivation.Branches.BranchTripleDescendants
open STLTableau.Section4.Finiteness
#check OrdinaryChoice.exists_annotation_triple
#print axioms OrdinaryChoice.exists_annotation_triple
#check RawBranch.next_bounded_triple
#print axioms RawBranch.next_bounded_triple
#check OrdinaryChoice.upper_old_right_absent
#print axioms OrdinaryChoice.upper_old_right_absent
#check BoundaryChoice.forced_upper_old_right_absent
#print axioms BoundaryChoice.forced_upper_old_right_absent
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``OrdinaryChoice.exists_annotation_triple, ``RawBranch.next_bounded_triple, ``OrdinaryChoice.upper_old_right_absent, ``BoundaryChoice.forced_upper_old_right_absent] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
