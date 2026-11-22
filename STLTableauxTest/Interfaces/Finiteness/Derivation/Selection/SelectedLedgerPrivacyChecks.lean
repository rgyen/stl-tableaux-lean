import STLTableaux.Finiteness.Derivation.Selection.SelectedLedgerPrivacy
open STLTableau.Section4.Finiteness
#check SelectedTree.ledger_sources_protected
#check SelectedTree.rawLedger_sources_pairwise_disjoint
#check SelectedTree.rawLedger_leftClocks_nodup
#check SelectedTree.rawLedger_same_left_unique
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SelectedTree.ledger_sources_protected, ``SelectedTree.rawLedger_sources_pairwise_disjoint, ``SelectedTree.rawLedger_leftClocks_nodup, ``SelectedTree.rawLedger_same_left_unique] do
    let axs ← Lean.collectAxioms name
    Lean.logInfo m!"{name}: {axs}"
    for axiomName in axs do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom: {axiomName}"
