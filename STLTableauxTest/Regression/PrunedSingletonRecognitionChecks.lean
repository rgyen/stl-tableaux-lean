import STLTableaux.Automata.Recognition.PrunedSingletonRecognition

open STLTableau STLTableau.Section4

-- The dwell theorem has no terminal-label or final-terminal premise:
-- the jump at the horizon and the restricted mode set discharge both.
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Finiteness.inputTableau_pruned_recognizes_singleton_path_at_horizon,
      ``Finiteness.inputTableau_pruned_recognizes_observed_dwells_at_horizon,
      ``Tableau.pruned_dwell_boundaries_lt_horizon,
      ``Tableau.dwell_boundaries_monotone,
      ``Tableau.pruned_discreteSteps_at_horizon,
      ``Tableau.pruned_discreteSteps_from_terminal_eq] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
