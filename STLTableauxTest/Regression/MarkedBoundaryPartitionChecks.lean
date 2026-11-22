import STLTableaux.Automata.Recognition.ExecutionFlowPartition

open STLTableau

/-- An open second left endpoint is owned by the first piece, not discarded. -/
example (b : Fin 3 → ℝ) (hb : StrictMono b) :
    ((IntervalPartition.ofMarkedBoundaries b hb ![●, ○, ●] rfl rfl).interval
      ⟨0, by change 0 < 2; decide⟩).rightBoundary = ● := rfl

example (b : Fin 3 → ℝ) (hb : StrictMono b) :
    ((IntervalPartition.ofMarkedBoundaries b hb ![●, ○, ●] rfl rfl).interval
      ⟨1, by change 1 < 2; decide⟩).leftBoundary = ○ := rfl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPartition.markedBoundaryPiece,
      ``IntervalPartition.markedBoundaryPiece_subset_closed,
      ``IntervalPartition.markedBoundaryPiece_disjoint,
      ``IntervalPartition.ofMarkedBoundaries,
      ``IntervalPartition.markedBoundaryPiece_last_subset_halfOpen,
      ``HybridAutomaton.Execution.markedFlowPartition,
      ``HybridAutomaton.Execution.markedFlowPartition_leftMarker,
      ``HybridAutomaton.Execution.markedFlowPartition_duration,
      ``Section4.Tableau.markedFlowPartition_projected_atom] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
