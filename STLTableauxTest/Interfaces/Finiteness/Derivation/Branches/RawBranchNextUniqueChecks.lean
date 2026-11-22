import STLTableaux.Finiteness.Derivation.Branches.RawBranchNextUnique
open STLTableau.Section4.Finiteness
#print axioms RawBranch.next_bounded_unique
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``RawBranch.next_bounded_unique do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
