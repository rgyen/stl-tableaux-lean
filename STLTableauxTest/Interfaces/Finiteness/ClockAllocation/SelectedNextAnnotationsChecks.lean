import STLTableaux.Finiteness.ClockAllocation.SelectedNextAnnotations
open STLTableau.Section4.Finiteness
#check SafeNormalization.next_guard_payload_origin
#check SafeNormalization.next_reset_payload_origin
#check SelectedTree.normalized_next_guard_provenance
#check SelectedTree.normalized_next_reset_provenance
#print axioms SelectedTree.normalized_next_guard_provenance
#print axioms SelectedTree.normalized_next_reset_provenance
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawGuardAt.of_payload, ``RawResetAt.of_payload,
    ``SafeNormalization.next_guard_payload_origin, ``SafeNormalization.next_reset_payload_origin,
    ``SelectedTree.normalized_next_guard_provenance, ``SelectedTree.normalized_next_reset_provenance] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
