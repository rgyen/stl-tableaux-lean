import STLTableaux.Finiteness.Derivation.Selection.NextEntryProvenance
open STLTableau.Section4.Finiteness
#check SelectedTree.ledger_bounded_right_unreset
#check SelectedTree.ledger_upper_entry
#print axioms SelectedTree.ledger_bounded_right_unreset
#print axioms SelectedTree.ledger_upper_entry
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.ledger_bounded_right_unreset, ``SelectedTree.ledger_upper_entry] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
