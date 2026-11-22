import STLTableaux.Finiteness.Correctness.RootIntervalNecessity

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteRootTableau_root_on_first_interval,
      ``finiteRootTableau_root_everywhere_of_one_piece] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
