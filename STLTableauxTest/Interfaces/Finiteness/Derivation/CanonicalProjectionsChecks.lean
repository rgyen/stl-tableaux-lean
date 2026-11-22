import STLTableaux.Finiteness.Derivation.CanonicalProjections

open STLTableau.Section4.Finiteness
#check ACIdem.currentPredicates_eq
#check canonical_currentPredicates_iff
#check canonical_nextSyntaxClocks
#check canonical_local_support
#check canonical_payload_support
#check canonical_payload_safe
#print axioms canonical_currentPredicates_iff
#print axioms canonical_nextSyntaxClocks
#print axioms canonical_payload_safe

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ACIdem.currentPredicates_eq, ``canonical_currentPredicates_iff,
      ``canonical_nextSyntaxClocks, ``canonical_local_support,
      ``canonical_payload_support, ``canonical_payload_safe] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
