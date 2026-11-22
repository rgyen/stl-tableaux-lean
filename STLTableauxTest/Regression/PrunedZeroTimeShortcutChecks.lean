import STLTableaux.Automata.Execution.PrunedZeroTimeShortcut

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteRootTableau_pruned_shortcut_overwritten_block,
      ``finiteRootTableau_pruned_shortcut_stationary_block] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
