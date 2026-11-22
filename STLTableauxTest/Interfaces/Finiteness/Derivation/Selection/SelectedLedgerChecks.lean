import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger
open STLTableau.Section4.Finiteness
#check SelectedTree.rawLedger
#check SelectedTree.plainConsumed
#check SelectedTree.boundaryConsumed
#print axioms SelectedTree.raw_next_provenance
#print axioms SelectedTree.normalized_next_provenance
#print axioms SelectedTree.erased_next_provenance
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.raw_next_provenance, ``SelectedTree.normalized_next_provenance,
      ``SelectedTree.erased_next_provenance] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
