import STLTableaux.Finiteness.Derivation.Selection.CombinedSelection
open STLTableau.Section4.Finiteness
#check combined_selection_exists
#check selected_output_exists
#print axioms combined_selection_exists
#print axioms selected_output_exists
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``combined_selection_exists, ``selected_output_exists] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
