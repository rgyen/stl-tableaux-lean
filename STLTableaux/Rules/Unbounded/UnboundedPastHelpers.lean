import STLTableaux.Rules.Unbounded.UnboundedClockedRules
import STLTableaux.Rules.Finite.Preservation

/-! Lower-endpoint-only past-cover transport for literal infinite bounds.
No finite upper cap or branch-preservation premise is used here. -/
namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

theorem pastSeparated_of_lower (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (h : (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] (a : ℝ)) :
    PastSeparated σ P α k hk c b a φ :=
  STLTableau.pastSeparated_of_lower σ P α k hk c b (lowerInterval a) φ h

theorem pastSeparated_next_of_not_plain (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hc : (P.interval ⟨k.1 + 1, hn⟩).left - (β c : ℝ) =
      (P.interval ⟨k.1, by omega⟩).left - (α c : ℝ))
    (hp : PastSeparated σ P α k (by omega) c b a φ)
    (hnot : ¬ Node.holds σ P α k (.plain φ)) :
    PastSeparated σ P β ⟨k.1 + 1, by omega⟩ hn c b a φ := by
  apply STLTableau.pastSeparated_next_of_not_plain σ P α β k hn c b (lowerInterval a) φ hc hp
  exact hnot

/-- A check/reset scope starts at the next interval minus the lower bound;
this geometry excludes every earlier true cover, independently of satisfaction. -/
theorem pastSeparated_of_clock_eq_lower (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (m : Marker) (a : NNReal) (φ : Formula Var)
    (hc : α c = a) (hm : (P.interval ⟨k.1, hk⟩).leftBoundary = m) :
    PastSeparated σ P α k hk c m a φ := by
  apply pastSeparated_of_lower σ P α k hk c m a φ
  rw [hc, hm]
  exact Or.inr ⟨rfl, (Marker.includes_imp _ _).2 id⟩

/-- Preferred deferral preserves past separation: either the current piece
is not uniformly true, or the propagated lower witness bound starts beyond it. -/
theorem pastSeparated_deferred (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hc : β c = ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c)
    (hp : PastSeparated σ P α k (by omega) c b a φ)
    (hcond : ¬ Node.holds σ P α k (.plain φ) ∨
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
        <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] (a : ℝ)) :
    PastSeparated σ P β ⟨k.1 + 1, by omega⟩ hn c b a φ := by
  rcases hcond with hnot | hlo
  · apply pastSeparated_next_of_not_plain σ P α β k hn c b a φ ?_ hp hnot
    rw [hc]
    exact Judgement.next_left_sub_elapse_eq P α ⟨k.1, by omega⟩ hn c
  · apply pastSeparated_of_lower σ P β ⟨k.1 + 1, by omega⟩ hn c b a φ
    simpa only [hc] using hlo

abbrev deferred_past := @pastSeparated_deferred
abbrev reset_lower_past := @pastSeparated_of_clock_eq_lower

theorem pastSeparated_of_clock_zero (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (m : Marker) (a : NNReal) (φ : Formula Var)
    (hc : α c = 0) (hm : (P.interval ⟨k.1, hk⟩).leftBoundary = m) :
    PastSeparated σ P α k hk c m a φ := by
  apply pastSeparated_of_lower σ P α k hk c m a φ
  rw [hc, hm]
  rcases a.coe_nonneg.eq_or_lt with hz | hp
  · exact Or.inr ⟨hz, (Marker.includes_imp _ _).2 id⟩
  · exact Or.inl hp

end STLTableau.UnboundedClocked
