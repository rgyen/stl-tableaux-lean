import STLTableaux.Finiteness.Derivation.Selection.SelectedBranch

open STLTableau.Section4.Finiteness
#check exists_selected_branch
#print axioms exists_selected_branch

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``exists_selected_branch do
    unless allowed.contains axiomName do
      throwError "exists_selected_branch depends on an unapproved axiom: {axiomName}"
