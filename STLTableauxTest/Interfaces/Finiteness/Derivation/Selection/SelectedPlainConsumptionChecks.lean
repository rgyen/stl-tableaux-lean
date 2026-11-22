import STLTableaux.Finiteness.Derivation.Selection.SelectedPlainConsumption
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.plain_consumption_barrier
#print axioms SelectedTree.plainConsumed_nodup
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.plain_consumption_barrier, ``SelectedTree.plainConsumed_nodup] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
