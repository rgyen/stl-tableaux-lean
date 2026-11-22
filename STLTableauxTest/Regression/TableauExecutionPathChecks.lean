import STLTableaux.Automata.Recognition.TableauExecutionPath

open STLTableau.Section4.Tableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``discreteStep_iff, ``discreteSteps_path,
      ``initial_discreteSteps_run, ``initial_discreteSteps_accepting_run,
      ``discreteSteps_modeSteps, ``modeSteps_path, ``execution_start_modeSteps, ``execution_modeSteps,
      ``execution_run, ``reaches_accepting_run] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
