import STLTableaux.Automata.Recognition.ExecutionSuffixPartition
import STLTableaux.Semantics.Intervals.PartitionMarkerSemantics

/-! A partition refinement with a singleton at each execution boundary below
the horizon. A final open interval covers times after an early cut. -/
namespace STLTableau.HybridAutomaton.Execution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)

def fullPointOpenFlowPartition
    (he : e.boundary ⟨e.count, by omega⟩ = σ.horizon) :
    IntervalPartition σ.domain :=
  { e.pointOpenFlowPartition with
    covers := by
      rw [e.pointOpenFlowPartition.covers, he]
      rfl }

/-- No repeated boundary is inserted when the execution reaches the horizon. -/
noncomputable def reviewInducedPartition : IntervalPartition σ.domain := by
  classical
  exact if he : e.boundary ⟨e.count, by omega⟩ < σ.horizon then
    e.completedPointOpenFlowPartition he
  else e.fullPointOpenFlowPartition (le_antisymm e.last_le_horizon (le_of_not_gt he))

theorem reviewInducedPartition_of_early
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    e.reviewInducedPartition = e.completedPointOpenFlowPartition he := by
  simp only [reviewInducedPartition, dif_pos he]

theorem reviewInducedPartition_of_horizon
    (he : e.boundary ⟨e.count, by omega⟩ = σ.horizon) :
    e.reviewInducedPartition = e.fullPointOpenFlowPartition he := by
  simp [reviewInducedPartition, he]

theorem reviewInducedPartition_size :
    e.reviewInducedPartition.size =
      if e.boundary ⟨e.count, by omega⟩ < σ.horizon then
        2 * (e.count + 1) else 2 * e.count := by
  classical
  by_cases he : e.boundary ⟨e.count, by omega⟩ < σ.horizon
  · rw [e.reviewInducedPartition_of_early he, if_pos he]
    rfl
  · rw [e.reviewInducedPartition_of_horizon
      (le_antisymm e.last_le_horizon (le_of_not_gt he)), if_neg he]
    rfl

theorem completedPointOpenFlowPartition_old_piece
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) (i : Fin (2 * e.count)) :
    (e.completedPointOpenFlowPartition he).interval
      ⟨i.val, by change i.val < 2 * (e.count + 1); omega⟩ =
        e.pointOpenFlowPartition.interval i := by
  simp only [completedPointOpenFlowPartition, pointOpenFlowPartition,
    IntervalPartition.pointOpenPartition, IntervalPartition.pointOpenPiece]
  split_ifs <;>
    simp [extendedBoundary, show i.val / 2 < e.count + 1 by omega,
      show i.val / 2 + 1 < e.count + 1 by omega]

theorem completedPointOpenFlowPartition_stop_carrier
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    ((e.completedPointOpenFlowPartition he).interval
      ⟨2 * e.count, by change 2 * e.count < 2 * (e.count + 1); omega⟩).carrier =
        {e.boundary ⟨e.count, by omega⟩} := by
  rw [e.completedPointOpenFlowPartition_stop he]
  simp [MarkedInterval.carrier_eq]

theorem completedPointOpenFlowPartition_suffix
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    ((e.completedPointOpenFlowPartition he).interval
      ⟨2 * e.count + 1, by change 2 * e.count + 1 < 2 * (e.count + 1); omega⟩).carrier =
        Set.Ioo (e.boundary ⟨e.count, by omega⟩) σ.horizon := by
  change (IntervalPartition.pointOpenPiece e.extendedBoundary _).carrier = _
  rw [IntervalPartition.pointOpenPiece_carrier]
  simp [extendedBoundary, Nat.add_div]

theorem reviewInducedPartition_flow_size_le :
    2 * e.count ≤ e.reviewInducedPartition.size := by
  rw [e.reviewInducedPartition_size]
  split_ifs <;> omega

/-- Singleton pieces are closed on the left; open pieces are open on the left.
This also covers the two pieces completing an early-stop suffix. -/
theorem reviewInducedPartition_leftMarker (i : Fin e.reviewInducedPartition.size) :
    (e.reviewInducedPartition.interval i).leftBoundary =
      if i.val % 2 = 0 then ● else ○ := by
  by_cases he : e.boundary ⟨e.count, by omega⟩ < σ.horizon
  · revert i
    rw [e.reviewInducedPartition_of_early he]
    intro i
    exact IntervalPartition.pointOpenPiece_leftMarker e.extendedBoundary i
  · revert i
    rw [e.reviewInducedPartition_of_horizon
      (le_antisymm e.last_le_horizon (le_of_not_gt he))]
    intro i
    exact IntervalPartition.pointOpenPiece_leftMarker e.boundary i

/-- The same parity formula includes the terminal position, whose index is
even and whose marker is closed by convention. -/
theorem reviewInducedPartition_positionMarker
    (k : STLTableau.Judgement.Position e.reviewInducedPartition) :
    e.reviewInducedPartition.positionMarker k =
      if k.val % 2 = 0 then ● else ○ := by
  by_cases hk : k.val < e.reviewInducedPartition.size
  · simp only [IntervalPartition.positionMarker, dif_pos hk]
    exact e.reviewInducedPartition_leftMarker ⟨k.val, hk⟩
  · have hend : k.val = e.reviewInducedPartition.size := by have := k.isLt; omega
    have heven : k.val % 2 = 0 := by
      rw [hend, e.reviewInducedPartition_size]
      split_ifs <;> omega
    simp only [IntervalPartition.positionMarker, dif_neg hk, if_pos heven]

/-- The induced partition itself supplies a satisfied interval-type judgement
at every position. There is no marker choice or compatibility hypothesis. -/
theorem reviewInducedPartition_lty {Clock : Type*} (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position e.reviewInducedPartition) :
    Section3.Judgement.holds σ e.reviewInducedPartition α k
      (.marker (if k.val % 2 = 0 then ● else ○)) := by
  rw [← e.reviewInducedPartition_positionMarker k]
  exact Section3.Judgement.holds_positionMarker σ e.reviewInducedPartition α k

theorem reviewInducedPartition_old_piece (i : Fin (2 * e.count)) :
    ∃ j : Fin e.reviewInducedPartition.size, j.val = i.val ∧
      e.reviewInducedPartition.interval j = e.pointOpenFlowPartition.interval i := by
  by_cases he : e.boundary ⟨e.count, by omega⟩ < σ.horizon
  · rw [e.reviewInducedPartition_of_early he]
    exact ⟨⟨i.val, by change i.val < 2 * (e.count + 1); omega⟩, rfl,
      e.completedPointOpenFlowPartition_old_piece he i⟩
  · rw [e.reviewInducedPartition_of_horizon
      (le_antisymm e.last_le_horizon (le_of_not_gt he))]
    exact ⟨i, rfl, rfl⟩

end STLTableau.HybridAutomaton.Execution

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

/-- Only the actually executed pieces inherit flow-mode atomic obligations.
No assertion about a tableau path, markers, or an unexecuted suffix is made. -/
theorem reviewInducedPartition_projected_atom {ρ : FiniteSignal Var}
    (hp : T.ProjectsTo σ ρ) (j : Fin (2 * e.count))
    (t : σ.Time) (u : ρ.Time) (htu : t.val = u.val)
    (ht : t.val ∈ (e.reviewInducedPartition.interval
      ⟨j.val, lt_of_lt_of_le j.isLt e.reviewInducedPartition_flow_size_le⟩).carrier)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈
      T.label (e.start ⟨j.val / 2, by omega⟩).val.1.val) :
    a.Holds (ρ.value u) := by
  obtain ⟨k, hk, heq⟩ := e.reviewInducedPartition_old_piece j
  have hkj : k = ⟨j.val, lt_of_lt_of_le j.isLt e.reviewInducedPartition_flow_size_le⟩ :=
    Fin.ext hk
  rw [hkj] at heq
  rw [heq] at ht
  exact T.pointOpenFlowPartition_projected_atom h τ hτ e hp j t u htu ht a ha

end STLTableau.Section4.Tableau
