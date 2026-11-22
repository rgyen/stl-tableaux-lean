import STLTableaux.Finiteness.Derivation.Selection.SelectedResetMap
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.raw_reset_agreement
#print axioms SelectedTree.normalized_reset_agreement
#print axioms SelectedTree.erased_reset_agreement
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.raw_reset_agreement, ``SelectedTree.normalized_reset_agreement,
      ``SelectedTree.erased_reset_agreement] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
