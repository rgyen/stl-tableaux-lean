import STLTableaux.Finiteness.ClockAllocation.SelectedNextClockSupport
open STLTableau.Section4.Finiteness
#check SafeNormalization.nextClocks_eq_syntax
#check SelectedTree.ledger_body_fresh_support
#check SelectedTree.next_clock_ledger_support
#check SelectedTree.normalized_next_clock_card
#print axioms SafeNormalization.nextClocks_eq_syntax
#print axioms SelectedTree.normalized_next_clock_card
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SafeNormalization.nextClocks_eq_syntax, ``nextSyntaxClocks_payloads,
    ``SelectedTree.ledger_body_fresh_support, ``SelectedTree.next_clock_ledger_support,
    ``SelectedTree.normalized_next_clock_card] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
