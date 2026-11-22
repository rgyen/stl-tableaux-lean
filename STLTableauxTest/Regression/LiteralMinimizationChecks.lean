import STLTableaux.Finiteness.Correctness.LiteralRootTableau

open STLTableau.Section4.Finiteness

-- Minimization works in any finite inventory containing a satisfied closed extension.
#check FiniteInventory.Within.of_componentsIncluded
#check FiniteInventory.TransitionWithin.of_subsumed
#check FiniteInventory.exists_satisfied_minimal_within
#check finiteLiteralRootTableau_exists_minimal_state

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``FiniteInventory.Within.of_componentsIncluded,
      ``FiniteInventory.TransitionWithin.of_subsumed,
      ``FiniteInventory.exists_satisfied_minimal_within,
      ``finiteLiteralRootTableau_exists_minimal_state] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
