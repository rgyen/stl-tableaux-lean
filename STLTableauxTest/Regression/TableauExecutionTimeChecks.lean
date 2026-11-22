import STLTableaux.Automata.Recognition.TableauExecutionTime

open STLTableau.Section4.Tableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execution_start_clock, ``execution_finish_clock,
      ``execution_final_clock, ``execution_curve_clock, ``execution_signal_clock,
      ``execution_final_clock_le_horizon, ``execution_nonterminal_start_lt,
      ``execution_final_terminal_time, ``execution_preflow_jump_nonterminal,
      ``execution_flow_nonterminal, ``execution_terminal_acceptance_exhausts] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
