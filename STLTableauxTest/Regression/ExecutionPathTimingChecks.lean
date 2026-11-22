import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint

open STLTableau STLTableau.Section4

-- One positive flow, one stationary frame, and another positive flow.
example : (fun i : Fin 4 => Tableau.residenceBoundary [1, 0, 1] i.val) = ![0, 1, 1, 2] := by
  funext i
  fin_cases i <;> norm_num [Tableau.residenceBoundary]

-- The middle singleton changes no clock by elapse, but its incoming reset
-- is still present in TimedPath.step and is not erased.
example : Tableau.residenceBoundary [1, 0, 1] 2 -
    Tableau.residenceBoundary [1, 0, 1] 1 = 0 := by
  norm_num [Tableau.residenceBoundary]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ExecutionPathWitness.timing,
      ``Tableau.TimedPath.total_duration, ``Tableau.TimedPath.frame_count,
      ``Tableau.residenceBoundary_step, ``Tableau.residenceBoundary_monotone,
      ``Tableau.execution_accepting_timed_path,
      ``Finiteness.pruned_execution_original_accepting_timed_path] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
