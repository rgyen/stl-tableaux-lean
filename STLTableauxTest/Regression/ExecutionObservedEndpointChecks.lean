import STLTableaux.Automata.Recognition.ExecutionObservedEndpoint

open STLTableau STLTableau.Section4

#check Tableau.ObservedPath.frame_terminal_of_horizon_le
#check Path.pruned_frame_terminal_labels
#check Tableau.ObservedPath.frame_endpoint_labels

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.ObservedPath.frame_terminal_of_horizon_le,
      ``Path.pruned_frame_terminal_labels, ``Tableau.ObservedPath.frame_endpoint_labels] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
