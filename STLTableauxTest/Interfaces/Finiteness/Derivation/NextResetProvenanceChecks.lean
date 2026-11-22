import STLTableaux.Finiteness.Derivation.NextResetProvenance
open STLTableau.Section4.Finiteness
#check SafeNormalization.next_reset_value_of_separated_payloads
#check SelectedTree.finalNextInputs
#check SelectedTree.nextPayloads_final
#check SelectedTree.nextPayloads_separated
#check SelectedTree.nextPayloads_iff
#check SelectedTree.ledger_next_reset_value
#print axioms SafeNormalization.next_reset_value_of_separated_payloads
#print axioms SelectedTree.nextPayloads_final
#print axioms SelectedTree.nextPayloads_iff
#print axioms SelectedTree.ledger_next_reset_value
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SafeNormalization.next_reset_value_of_separated_payloads,
    ``SelectedTree.nextPayloads_final, ``SelectedTree.nextPayloads_separated,
    ``SelectedTree.nextPayloads_iff, ``SelectedTree.ledger_next_reset_value] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
