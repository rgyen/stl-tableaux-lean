import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport

open STLTableau.Section4.Finiteness
#check ACIdem.invariant_iff
#check ACIdem.stable_iff
#check SafeNormalization.fullInvariant
#check SafeNormalization.stable
#print axioms ACIdem.invariant_iff
#print axioms ACIdem.stable_iff
#print axioms SafeNormalization.fullInvariant
#print axioms SafeNormalization.stable

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ACIdem.invariant_iff, ``ACIdem.underlyingFormulas_eq,
      ``ACIdem.stable_iff, ``union_fullInvariant_iff,
      ``SafeNormalization.fullInvariant, ``SafeNormalization.stable] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
