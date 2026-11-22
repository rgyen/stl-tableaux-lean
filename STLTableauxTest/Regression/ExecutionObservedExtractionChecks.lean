import STLTableaux.Automata.Recognition.ExecutionObservedExtraction

open STLTableau.Section4

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.observed_early_final_steps,
      ``Tableau.pruned_last_flow_observed,
      ``Tableau.pruned_execution_observed_path,
      ``Tableau.pruned_execution_accepting_observed_path] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
