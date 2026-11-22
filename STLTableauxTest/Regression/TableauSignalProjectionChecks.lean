import STLTableaux.Automata.Recognition.TableauSignalProjection

open STLTableau.Section4.Tableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ProjectsTo, ``ReachesSignal, ``state_atom,
      ``discreteSteps_realVariable_preserved, ``execution_curve_atom,
      ``execution_signal_atom, ``execution_projected_atom,
      ``discreteSteps_source_atom_at_destination, ``execution_start_value,
      ``execution_projected_preflow_atom, ``execution_projected_final_atom,
      ``execution_finish_realValue,
      ``execution_projected_finish_atom, ``execution_projected_closed_atom,
      ``reachesSignal_accepting_run] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
