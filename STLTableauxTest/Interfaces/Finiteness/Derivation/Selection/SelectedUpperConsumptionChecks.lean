import STLTableaux.Finiteness.Derivation.Selection.SelectedUpperConsumption
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.upperCredits_nodup
#print axioms SelectedTree.upperExpanded_eq_rawLedger
#print axioms SelectedTree.upper_ledger_formulas_nodup
#print axioms SelectedTree.upperExpanded_credit
#print axioms SelectedTree.upper_credit_source
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.upperCredits_nodup, ``SelectedTree.upperExpanded_eq_rawLedger,
      ``SelectedTree.upper_ledger_formulas_nodup, ``SelectedTree.upperExpanded_credit,
      ``SelectedTree.upper_credit_source] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
