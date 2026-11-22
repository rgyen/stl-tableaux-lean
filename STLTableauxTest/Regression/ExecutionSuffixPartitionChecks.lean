import STLTableaux.Automata.Recognition.ExecutionSuffixPartition

open STLTableau.HybridAutomaton.Execution

-- Exposing the stopping point must not add elapsed time.
example {Mode Label Var : Type*} {H : STLTableau.HybridAutomaton Mode Label Var}
    {σ : STLTableau.FiniteSignal Var} (e : H.Execution σ)
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    STLTableau.Judgement.duration (e.completedPointOpenFlowPartition he)
      ⟨2 * e.count, by change 2 * e.count < 2 * (e.count + 1); omega⟩ = 0 := by
  apply Subtype.ext
  change ((e.completedPointOpenFlowPartition he).interval _).right -
    ((e.completedPointOpenFlowPartition he).interval _).left = 0
  rw [e.completedPointOpenFlowPartition_stop he]
  exact sub_self _

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``extendedBoundary_strictMono, ``completedFlowPartition,
      ``completedFlowPartition_old_piece, ``completedFlowPartition_suffix,
      ``exists_completed_raw_flow_partition,
      ``STLTableau.Section4.Tableau.exists_projected_flow_partition,
      ``completedFlowPartition_mem_old_piece, ``completedMarkedFlowPartition,
      ``completedMarkedFlowPartition_old_piece, ``completedMarkedFlowPartition_duration,
      ``completedMarkedFlowPartition_suffix, ``completedPointOpenFlowPartition,
      ``completedPointOpenFlowPartition_stop,
      ``STLTableau.IntervalPartition.appendPointSuffix,
      ``STLTableau.IntervalPartition.appendPointSuffix_old,
      ``STLTableau.IntervalPartition.appendPointSuffix_point,
      ``STLTableau.IntervalPartition.appendPointSuffix_suffix,
      ``completedMarkedPointFlowPartition, ``completedMarkedPointFlowPartition_old_piece,
      ``completedMarkedPointFlowPartition_stop, ``completedMarkedPointFlowPartition_duration] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
