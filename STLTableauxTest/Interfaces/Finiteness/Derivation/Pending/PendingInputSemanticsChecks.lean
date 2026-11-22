import STLTableaux.Finiteness.Derivation.Pending.PendingInputSemantics

open STLTableau.Section4.Finiteness
#check canonical_body_facts
#check exposed_predicate_facts
#print axioms canonical_body_facts
#print axioms exposed_predicate_facts

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``canonical_body_facts, ``exposed_predicate_facts] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
