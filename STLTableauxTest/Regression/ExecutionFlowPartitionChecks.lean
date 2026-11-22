import STLTableaux.Automata.Recognition.ExecutionFlowPartition

open STLTableau

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPartition.exists_boundary_piece, ``IntervalPartition.ofBoundaries,
      ``HybridAutomaton.Execution.flowPartition, ``HybridAutomaton.Execution.mem_flowPartition,
      ``HybridAutomaton.Execution.flowPartition_covers_signal_iff,
      ``HybridAutomaton.Execution.fullFlowPartition,
      ``Section4.Tableau.flowPartition_projected_atom,
      ``IntervalPartition.pointOpenPiece_carrier,
      ``IntervalPartition.pointOpenPiece_subset_parent,
      ``IntervalPartition.pointOpenPartition,
      ``IntervalPartition.pointOpenPartition_finer,
      ``IntervalPartition.pointOpenPiece_leftMarker,
      ``HybridAutomaton.Execution.pointOpenFlowPartition,
      ``HybridAutomaton.Execution.pointOpenFlowPartition_finer,
      ``Section4.Tableau.pointOpenFlowPartition_projected_atom] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
