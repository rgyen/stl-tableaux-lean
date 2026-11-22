import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalizedOrigin
open STLTableau.Section4.Finiteness
#print axioms RawBranch.normalized_next_predicate_origin
#print axioms RawBranch.normalized_next_bounded_origin
#print axioms RawBranch.normalized_next_bounded_unique
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.normalized_next_predicate_origin,
      ``RawBranch.normalized_next_bounded_origin, ``RawBranch.normalized_next_bounded_unique] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
