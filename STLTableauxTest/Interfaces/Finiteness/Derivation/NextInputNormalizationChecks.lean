import STLTableaux.Finiteness.Derivation.NextInputNormalization

open STLTableau.Section4.Finiteness
#check nextStates_compatible
#check SafeNormalization.next_input
#print axioms nextStates_compatible
#print axioms SafeNormalization.next_input

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``nextStates_compatible, ``SafeNormalization.next_input] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
