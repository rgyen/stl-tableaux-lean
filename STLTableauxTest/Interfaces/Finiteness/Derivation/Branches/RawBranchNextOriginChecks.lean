import STLTableaux.Finiteness.Derivation.Branches.RawBranchNextOrigin
open STLTableau.Section4.Finiteness
#print axioms RawBranch.next_bounded_source
#print axioms RawBranch.next_bounded_frozen_of_upper
#print axioms RawBranch.next_bounded_origin
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.next_bounded_source, ``RawBranch.next_bounded_frozen_of_upper,
      ``RawBranch.next_bounded_origin] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
