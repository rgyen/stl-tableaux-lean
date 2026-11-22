import STLTableaux.Finiteness.Derivation.NextPayloadLocals
open STLTableau.Section4.Finiteness
#check SafeNormalization.current_locals_eq
#check SafeNormalization.next_local_iff
#check SafeNormalization.next_local_of_payload
#check SelectedTree.ledger_next_local
#print axioms SafeNormalization.next_local_iff
#print axioms SelectedTree.ledger_next_local
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``SafeNormalization.current_locals_eq, ``SafeNormalization.next_local_iff,
    ``SafeNormalization.next_local_of_payload, ``SelectedTree.ledger_next_local] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
