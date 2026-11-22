import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedConsumption
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.boundary_consumed_origin
#print axioms SelectedTree.boundary_sources_nodup
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.boundary_consumed_origin, ``SelectedTree.boundary_sources_nodup] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
