import STLTableaux.Finiteness.Derivation.Selection.SelectedUpperTruth
open STLTableau.Section4.Finiteness
#print axioms SelectedTree.upper_credit_plain_truth
#print axioms SelectedTree.upper_ledger_plain_truth
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.upper_credit_plain_truth, ``SelectedTree.upper_ledger_plain_truth] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
