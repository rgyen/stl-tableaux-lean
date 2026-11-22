import STLTableaux.Automata.Recognition.TableauClockValuations

open STLTableau.Section4.Tableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``clockCompatible_nonnegative, ``exists_clockCompatible_iff,
      ``reset_clockCompatible, ``reset_clocksNonnegative, ``flow_clockCompatible,
      ``continuousStep_clockCompatible, ``discreteStep_clockCompatible,
      ``discreteStep_clocksNonnegative, ``discreteSteps_clocksNonnegative,
      ``continuousStep_clocksNonnegative, ``execution_start_clocksNonnegative,
      ``execution_final_clocksNonnegative, ``discreteSteps_guardedClockSteps,
      ``discreteSteps_guardedClockSteps_nonempty,
      ``execution_between_flows_guardedClockSteps] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
