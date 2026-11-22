import STLTableaux.Finiteness.Derivation.CanonicalResetMap
open STLTableau.Section4.Finiteness
#check OwnedPending.current_resets_of_safe
#print axioms OwnedPending.current_resets_of_safe
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``OwnedPending.current_resets_of_safe do
    unless allowed.contains axiomName do
      throwError "unapproved axiom: {axiomName}"
