import STLTableaux.Syntax.Section3Judgements

/-! A partition determines its positional interval-type judgement.
The terminal position uses the closed-marker convention. -/
namespace STLTableau

namespace IntervalPartition

/-- The left marker supplied by the partition, including its terminal position. -/
def positionMarker {domain : Set ℝ} (P : IntervalPartition domain)
    (k : Judgement.Position P) : Marker :=
  if h : k.val < P.size then (P.interval ⟨k.val, h⟩).leftBoundary else ●

@[simp] theorem positionMarker_interval {domain : Set ℝ} (P : IntervalPartition domain)
    (i : Fin P.size) : P.positionMarker i.castSucc = (P.interval i).leftBoundary := by
  simp only [positionMarker, Fin.val_castSucc, dif_pos i.isLt]

@[simp] theorem positionMarker_terminal {domain : Set ℝ} (P : IntervalPartition domain) :
    P.positionMarker ⟨P.size, by omega⟩ = ● := by
  simp only [positionMarker, dif_neg (Nat.lt_irrefl P.size)]

end IntervalPartition

/-- No independently supplied marker or marker-agreement premise is needed. -/
theorem Section3.Judgement.holds_positionMarker
    {Clock Var : Type*} (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    STLTableau.Section3.Judgement.holds σ P α k (.marker (P.positionMarker k)) := by
  by_cases hk : k.val < P.size <;>
    simp only [STLTableau.Section3.Judgement.holds, IntervalPartition.positionMarker,
      hk, ↓reduceDIte]

end STLTableau
