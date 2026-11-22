import STLTableaux.Automata.Execution.ExecutionTraceAssembly

open STLTableau.Section4.Finiteness

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``pruned_execution_accepting_path_with_trace_reduction,
      ``inputTableau_trace_holds_of_timedPath,
      ``inputTableau_trace_holds_on_observed_partition,
      ``inputTableau_terminal_trace_reduction,
      ``inputTableau_recognizes_of_timedPath] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
