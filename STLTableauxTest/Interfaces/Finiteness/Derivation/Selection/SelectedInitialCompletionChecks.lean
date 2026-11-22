import STLTableaux.Finiteness.Derivation.Selection.SelectedInitialCompletion
open STLTableau.Section4.Finiteness
#check plainInitialOrigins
#print axioms plainInitialOrigins
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``plainInitialOrigins do
    unless allowed.contains axiomName do
      throwError "plainInitialOrigins depends on an unapproved axiom: {axiomName}"
