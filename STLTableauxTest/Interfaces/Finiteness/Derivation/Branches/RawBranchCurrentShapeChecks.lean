import STLTableaux.Finiteness.Derivation.Branches.RawBranchCurrentShape
open STLTableau.Section4.Finiteness
#print axioms RawBranch.no_current_bounded
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``RawBranch.no_current_bounded do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
