import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization

open STLTableau.Section4.Finiteness
#check RawBranch.safe_normalization
#check RawBranch.invariant_normalization
#print axioms RawBranch.safe_normalization
#print axioms RawBranch.invariant_normalization

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.safe_normalization, ``RawBranch.invariant_normalization] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
