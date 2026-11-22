import STLTableaux.Syntax.Section3Judgements

/-! Connected merge remains valid after uniform clock elapse. Resetting an
anchor is a separate operation and requires checking the conditions again. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}

/-- The two clock conditions required by connected interval merging. -/
def ConnectedMergeCondition (α : ClockValuation Clock)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) : Prop :=
  (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ) ∧
  (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)

/-- Uniform elapse preserves both order and endpoint equality. -/
theorem connectedMergeCondition_elapse_iff (α : ClockValuation Clock) (δ : NNReal)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) :
    ConnectedMergeCondition (ClockResetSet.elapse α δ) c₁ d₁ c₂ b₁ q₁ b₂ ↔
      ConnectedMergeCondition α c₁ d₁ c₂ b₁ q₁ b₂ := by
  simp only [ConnectedMergeCondition, ClockResetSet.elapse, NNReal.coe_add,
    MarkedLT, add_lt_add_iff_right, add_left_inj]

/-- The same merge can be used at any later interval if its anchor clocks
have only elapsed since the conditions were established. -/
theorem Predicate.predicate_merge_connected_after_elapse
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (δ : NNReal) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty)
    (h : ConnectedMergeCondition α c₁ d₁ c₂ b₁ q₁ b₂) :
    (Predicate.holds σ J (ClockResetSet.elapse α δ)
        (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      Predicate.holds σ J (ClockResetSet.elapse α δ)
        (.upper c₂ b₂ kind I φ)) ↔
      Predicate.holds σ J (ClockResetSet.elapse α δ)
        (.upper c₁ b₁ kind I φ) := by
  have h' := (connectedMergeCondition_elapse_iff α δ c₁ d₁ c₂ b₁ q₁ b₂).mpr h
  exact Predicate.predicate_merge_connected σ J _ c₁ d₁ c₂ b₁ q₁ b₂ kind I φ
    hne h'.1 h'.2

end STLTableau.Section3
