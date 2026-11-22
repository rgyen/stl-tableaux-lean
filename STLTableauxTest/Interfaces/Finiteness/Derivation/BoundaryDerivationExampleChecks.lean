import STLTableaux.Finiteness.Derivation.BoundaryDerivationExample

open STLTableau.Section4.Finiteness.BoundaryExample
#check input
#check full
#check erased
#check boundary_resolved
#print axioms boundary_resolved

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``boundary_resolved do
    unless allowed.contains axiomName do
      throwError "boundary_resolved depends on an unapproved axiom: {axiomName}"
