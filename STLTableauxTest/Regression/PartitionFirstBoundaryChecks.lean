import STLTableaux.Semantics.Partitions.PartitionFirstBoundary
import STLTableaux.Semantics.Stability.Stability

open STLTableau

/-- The signal horizon supplies both nonemptiness and the first closed marker;
neither is assumed as an extra marker condition. -/
theorem first_signal_piece_closed {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) :
    ∃ hsize : 0 < P.size, (P.interval ⟨0, hsize⟩).leftBoundary = ● := by
  have hD : σ.domain.Nonempty := ⟨0, le_rfl, σ.horizon_pos⟩
  have hsize := P.size_pos_of_domain_nonempty hD
  exact ⟨hsize, P.first_leftBoundary_closed hsize σ.horizon_pos⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPartition.size_pos_of_domain_nonempty,
      ``IntervalPartition.left_endpoint_mem_first,
      ``IntervalPartition.first_left_eq_domain_left,
      ``IntervalPartition.first_leftBoundary_closed, ``first_signal_piece_closed] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
