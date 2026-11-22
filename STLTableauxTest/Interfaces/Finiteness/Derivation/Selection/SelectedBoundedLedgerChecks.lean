import STLTableaux.Finiteness.Derivation.Selection.SelectedBoundedLedger
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.bounded_ledger_origin
#print axioms SelectedTree.bounded_ledger_nodup
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.bounded_ledger_origin, ``SelectedTree.bounded_ledger_nodup] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
