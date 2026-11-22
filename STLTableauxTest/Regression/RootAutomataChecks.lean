import STLTableaux.Automata.Translation.RootAutomata

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``rootVariables, ``atom_arguments_mem_rootVariables,
      ``FiniteInventory.atom_mem_plain_inventory,
      ``finiteRootTableau_incoming_guard_support,
      ``finiteRootTableau_incoming_reset_support,
      ``finiteRootTableau_translationReady, ``rootAutomaton, ``normalizedRootAutomaton] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
