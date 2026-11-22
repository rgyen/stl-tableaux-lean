import STLTableaux.Automata.Recognition.ExecutionObservedAtoms

open STLTableau.Section4

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ObservedPath.frame_atom,
      ``Tableau.ObservedPath.frame_atom_on_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
