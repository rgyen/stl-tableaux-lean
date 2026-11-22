import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath
open STLTableau.Section4.Finiteness
#print axioms ResolvedCertificate.freeDerives
#print axioms ResolvedCertificate.rename_freeDerives
#print axioms extend_supported_permutation
#print axioms ofState_support
#print axioms next_whole_support
#print axioms renamed_whole_support
#print axioms renamed_local_card
#print axioms allocated_path_of_resolved_steps
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ResolvedCertificate.freeDerives, ``ResolvedCertificate.rename_freeDerives, ``extend_supported_permutation, ``ofState_support, ``next_whole_support, ``renamed_whole_support, ``renamed_local_card, ``allocated_path_of_resolved_steps] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "unapproved axiom: {ax}"
