import STLTableaux.Automata.Recognition.ExecutionObservation

open STLTableau.HybridAutomaton.Execution

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``start_time_mem_domain, ``startTime, ``signal_at_start,
      ``signal_at_initial, ``boundary_not_in_previous_piece,
      ``existsUnique_observed_piece, ``observedIndex, ``observedIndex_spec,
      ``signal_eq_observed_curve] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
