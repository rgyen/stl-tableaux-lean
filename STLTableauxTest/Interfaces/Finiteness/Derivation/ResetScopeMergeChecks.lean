import STLTableaux.Finiteness.Derivation.ResetScopeMerge

open STLTableau.Section4.Finiteness
#check merge_reset_scopes
#check extract_unreset_guard
#print axioms merge_reset_scopes
#print axioms extract_unreset_guard

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``merge_reset_scopes, ``extract_unreset_guard] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
