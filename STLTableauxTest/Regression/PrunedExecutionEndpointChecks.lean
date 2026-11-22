import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``pruned_execution_initial_nonterminal,
      ``pruned_execution_original_accepting_run,
      ``pruned_execution_flow_nonterminal, ``pruned_execution_horizon_tail,
      ``pruned_execution_early_final_nonterminal, ``pruned_execution_terminal_labels] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
