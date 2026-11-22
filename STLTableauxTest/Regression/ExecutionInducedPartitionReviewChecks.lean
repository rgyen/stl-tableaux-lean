import STLTableaux.Automata.Recognition.ExecutionInducedPartitionReview

open STLTableau
open HybridAutomaton.Execution

-- An arbitrary partition supplies lty at every position, including its end.
example {Clock Var : Type*} (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    Section3.Judgement.holds σ P α k (.marker (P.positionMarker k)) :=
  Section3.Judgement.holds_positionMarker σ P α k

example {Clock Var : Type*} (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) :
    Section3.Judgement.holds σ P α ⟨P.size, by omega⟩ (.marker ●) := by
  simpa only [IntervalPartition.positionMarker_terminal] using
    Section3.Judgement.holds_positionMarker σ P α ⟨P.size, by omega⟩

-- No formula, path, atom observation or independently chosen marker is used.
example {Clock Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (α : ClockValuation Clock)
    (i : ℕ) (hi : 2 * i < e.reviewInducedPartition.size) :
    Section3.Judgement.holds σ e.reviewInducedPartition α
      ⟨2 * i, by omega⟩ (.marker ●) := by
  simpa using e.reviewInducedPartition_lty α ⟨2 * i, by omega⟩

example {Clock Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (α : ClockValuation Clock)
    (i : ℕ) (hi : 2 * i + 1 < e.reviewInducedPartition.size) :
    Section3.Judgement.holds σ e.reviewInducedPartition α
      ⟨2 * i + 1, by omega⟩ (.marker ○) := by
  simpa using e.reviewInducedPartition_lty α ⟨2 * i + 1, by omega⟩

example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) :
    (⋃ i, (e.reviewInducedPartition.interval i).carrier) = σ.domain :=
  e.reviewInducedPartition.covers

example {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (i : Fin e.reviewInducedPartition.size) :
    σ.horizon ∉ (e.reviewInducedPartition.interval i).carrier := by
  intro hi
  have hu : σ.horizon ∈ ⋃ j, (e.reviewInducedPartition.interval j).carrier :=
    Set.mem_iUnion.mpr ⟨i, hi⟩
  rw [e.reviewInducedPartition.covers] at hu
  exact (lt_irrefl _) hu.2

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``reviewInducedPartition, ``reviewInducedPartition_size,
      ``IntervalPartition.positionMarker_interval, ``IntervalPartition.positionMarker_terminal,
      ``Section3.Judgement.holds_positionMarker,
      ``reviewInducedPartition_leftMarker, ``reviewInducedPartition_positionMarker,
      ``reviewInducedPartition_lty,
      ``reviewInducedPartition_old_piece,
      ``completedPointOpenFlowPartition_stop_carrier,
      ``completedPointOpenFlowPartition_suffix,
      ``Section4.Tableau.reviewInducedPartition_projected_atom] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
