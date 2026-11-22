import STLTableaux.Finiteness.Derivation.Selection.SelectedResetConstants
open STLTableau.Section4.Finiteness
#check currentResetMap_value_literal
#print axioms currentResetMap_value_literal
#check OrdinaryChoice.child_reset_provenance
#print axioms OrdinaryChoice.child_reset_provenance
#check SelectedTree.current_reset_provenance
#print axioms SelectedTree.current_reset_provenance
#check SelectedTree.normalized_current_reset_provenance
#print axioms SelectedTree.normalized_current_reset_provenance
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``currentResetMap_value_literal, ``OrdinaryChoice.child_reset_provenance, ``SelectedTree.current_reset_provenance, ``SelectedTree.normalized_current_reset_provenance] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
