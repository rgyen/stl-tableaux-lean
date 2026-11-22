import STLTableaux.Finiteness.Correctness.LiteralSuccessor

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``LiteralDerives.ready, ``LiteralDerives.next_data,
      ``LiteralDerives.next_closure_exists,
      ``finiteLiteralRootTableau_exists_minimal_state_preserving] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
