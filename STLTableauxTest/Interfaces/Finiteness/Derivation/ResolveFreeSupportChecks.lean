import STLTableaux.Finiteness.Derivation.ResolveFreeSupport

open STLTableau.Section4.Finiteness
#check RawBranch.freeClocks_subset
#check ACIdem.freeClocks_eq
#check Resolve.freeClocks_subset
#check Resolve.erased_freeClocks_subset
#check SafeNormalization.freeClocks_subset
#check SafeNormalization.freeClocks_eq
#check selected_resolution_free_subset
#print axioms SafeNormalization.freeClocks_eq
#print axioms selected_resolution_free_subset
#print axioms RawBranch.freeClocks_subset
#print axioms Resolve.freeClocks_outputs
#print axioms SafeNormalization.freeClocks_subset

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RawBranch.freeClocks_subset, ``ACIdem.freeClocks_eq,
      ``Resolve.freeClocks_outputs, ``Resolve.freeClocks_subset,
      ``Resolve.erased_freeClocks_subset, ``SafeNormalization.freeClocks_subset,
      ``SafeNormalization.freeClocks_eq, ``selected_resolution_free_subset] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
