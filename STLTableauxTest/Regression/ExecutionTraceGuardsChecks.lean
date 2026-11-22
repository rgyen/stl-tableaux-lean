import STLTableaux.Automata.Recognition.ExecutionTraceGuards

open STLTableau.Section4

-- Check the complete dependency closure: no admitted clock-transfer step.
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.TimedPath.realGuardsHold,
      ``Tableau.TimedPath.realGuardsHold_of_initialReset,
      ``Tableau.TimedPath.forall_trace_holds_of_initialReset] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
