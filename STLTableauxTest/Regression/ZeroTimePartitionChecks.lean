import STLTableaux.Semantics.Partitions.PointOpenPartition
import STLTableaux.Syntax.Judgements

open STLTableau

/-- Preserving two consecutive zero dwell times at distinct trace positions
is impossible for a genuine partition of a connected time domain. -/
theorem no_adjacent_zero_durations {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) (hi : i.val + 1 < P.size)
    (hz : Judgement.duration P i = 0) :
    Judgement.duration P ⟨i.val + 1, hi⟩ ≠ 0 := by
  intro hz'
  have he := congrArg (fun d : NNReal => (d : ℝ)) hz
  have he' := congrArg (fun d : NNReal => (d : ℝ)) hz'
  change (P.interval i).right - (P.interval i).left = 0 at he
  change (P.interval ⟨i.val + 1, hi⟩).right - (P.interval ⟨i.val + 1, hi⟩).left = 0 at he'
  exact P.adjacent_not_both_zero_width i hi (sub_eq_zero.mp he) (sub_eq_zero.mp he')

/-- Positive geometric alternative: one singleton followed by an open flow
piece. No claim of trace refinement or repeated state validity is made. -/
theorem one_point_then_open_flow :
    ∃ P : IntervalPartition (Set.Ico (0 : ℝ) 1), ∃ hsize : P.size = 2,
      (P.interval ⟨0, by omega⟩).carrier = {0} ∧
      (P.interval ⟨1, by omega⟩).carrier = Set.Ioo 0 1 := by
  let b : Fin 2 → ℝ := fun i => i.val
  have hb : StrictMono b := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    change i.val < j.val at hij
    exact_mod_cast hij
  let Q := IntervalPartition.pointOpenPartition (n := 1) b hb
  let P : IntervalPartition (Set.Ico (0 : ℝ) 1) :=
    { Q with covers := by simpa [b] using Q.covers }
  refine ⟨P, rfl, ?_, ?_⟩ <;>
    simp [P, Q, IntervalPartition.pointOpenPartition, IntervalPartition.pointOpenPiece,
      b, MarkedInterval.carrier_eq]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPartition.carrier_eq_singleton_of_endpoints_eq,
      ``IntervalPartition.eq_of_shared_point, ``IntervalPartition.adjacent_not_both_zero_width,
      ``no_adjacent_zero_durations, ``one_point_then_open_flow] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
