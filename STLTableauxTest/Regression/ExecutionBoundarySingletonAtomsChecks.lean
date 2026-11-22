import STLTableaux.Automata.Recognition.ExecutionBoundarySingletonAtoms

open STLTableau.Section4.Tableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``reviewInducedPartition_beforeFlow_atoms,
      ``reviewInducedPartition_earlyFinal_atoms] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
