import STLTableaux.Automata.Execution.ExecutionObservedLabels

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``inputTableau_frame_normalizedReady, ``observed_frame_labels_hold,
      ``inputTableau_observed_frame_nonterminal,
      ``inputTableau_observed_terminal_last,
      ``inputTableau_observed_terminal_prefix,
      ``inputTableau_observed_terminal_prefix_last_ne_zero,
      ``inputTableau_observed_terminal_partition,
      ``STLTableau.Section4.Tableau.ObservedPath.total_duration,
      ``inputTableau_observed_trace_labels] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
