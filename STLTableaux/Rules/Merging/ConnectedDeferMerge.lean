import STLTableaux.Rules.Merging.ConnectedBoundedMerge

/-! Clock arithmetic for two successive opening/defer reset sequences.
This proves a semantic merge, not membership in a normalized closure graph. -/
open STLTableau
open scoped STL

namespace STLTableau.Section3.ConnectedDefer
variable {Var : Type*}

def twoDefer (α : ClockValuation (Fin 4)) (δ₀ δ₁ : NNReal) : ClockValuation (Fin 4) :=
  (ClockResetSet.singleton (3 : Fin 4) 0).apply
    (ClockResetSet.elapse
      ((ClockResetSet.singleton (2 : Fin 4) 0).apply
        ((ClockResetSet.singleton (1 : Fin 4) 0).apply
          (ClockResetSet.elapse ((ClockResetSet.singleton (0 : Fin 4) 0).apply α) δ₀))) δ₁)

theorem twoDefer_endpoints (α : ClockValuation (Fin 4)) (δ₀ δ₁ : NNReal) :
    twoDefer α δ₀ δ₁ 0 = δ₀+δ₁ ∧ twoDefer α δ₀ δ₁ 1 = δ₁ ∧
    twoDefer α δ₀ δ₁ 2 = δ₁ ∧ twoDefer α δ₀ δ₁ 3 = 0 := by
  simp [twoDefer,ClockResetSet.elapse,ClockResetSet.apply_singleton_self,
    ClockResetSet.apply_singleton_of_ne]

theorem adjacent_join (α : ClockValuation (Fin 4)) (δ₀ δ₁ : NNReal) (m : Marker) :
    (twoDefer α δ₀ δ₁ 1 : ℝ) <[Marker.disj m.complement m] (twoDefer α δ₀ δ₁ 2 : ℝ) := by
  have he := twoDefer_endpoints α δ₀ δ₁
  rw [he.2.1,he.2.2.1]
  right
  constructor
  · rfl
  · cases m <;> trivial

theorem adjacent_left_containment (α : ClockValuation (Fin 4)) (δ₀ δ₁ : NNReal)
    (b₀ b₁ : Marker) (hne : 0 < δ₀ ∨ b₀ = Marker.closed) :
    (twoDefer α δ₀ δ₁ 2 : ℝ) <[Marker.imp b₁ b₀] (twoDefer α δ₀ δ₁ 0 : ℝ) := by
  have he := twoDefer_endpoints α δ₀ δ₁
  rw [he.1,he.2.2.1]
  push_cast
  rcases hne with h | h
  · left
    exact lt_add_of_pos_left _ (by exact_mod_cast h)
  · subst b₀
    by_cases hd : δ₀ = 0
    · right
      exact ⟨by simp [hd],by cases b₁ <;> trivial⟩
    · left
      have hposNN : (0 : NNReal) < δ₀ := lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ δ₀) (Ne.symm hd)
      have hpos : (0 : ℝ) < δ₀ := by exact_mod_cast hposNN
      linarith

theorem adjacent_right_containment (α : ClockValuation (Fin 4)) (δ₀ δ₁ : NNReal)
    (m₁ m₂ : Marker) (hne : 0 < δ₁ ∨ m₁ = Marker.closed) :
    (twoDefer α δ₀ δ₁ 3 : ℝ) <[Marker.imp m₁.complement m₂.complement]
      (twoDefer α δ₀ δ₁ 1 : ℝ) := by
  have he := twoDefer_endpoints α δ₀ δ₁
  rw [he.2.2.2,he.2.1]
  rcases hne with h | h
  · left
    exact_mod_cast h
  · subst m₁
    by_cases hd : δ₁ = 0
    · right
      exact ⟨by simp [hd],by cases m₂ <;> trivial⟩
    · left
      have hposNN : (0 : NNReal) < δ₁ := lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ δ₁) (Ne.symm hd)
      exact_mod_cast hposNN
theorem duration_pos_or_left_closed {D : Set ℝ} (P : IntervalPartition D) (i : Fin P.size) :
    0 < STLTableau.Judgement.duration P i ∨ (P.interval i).leftBoundary = Marker.closed := by
  rcases (MarkedInterval.nonempty_iff _).1 (P.nonempty i) with h | ⟨_,hm⟩
  · left
    change (0 : ℝ) < (P.interval i).right - (P.interval i).left
    linarith
  · right
    have hl := ((Marker.includes_conj _ _).1 hm).1
    cases he : (P.interval i).leftBoundary with
    | closed => rfl
    | «open» => rw [he] at hl; exact hl.elim

theorem partition_generated_merge_conditions {D : Set ℝ} (P : IntervalPartition D)
    (i j : Fin P.size) (α : ClockValuation (Fin 4)) (m₂ : Marker) :
    let γ := twoDefer α (STLTableau.Judgement.duration P i) (STLTableau.Judgement.duration P j)
    (γ 2 : ℝ) <[Marker.imp (P.interval j).leftBoundary (P.interval i).leftBoundary] (γ 0 : ℝ) ∧
    (γ 1 : ℝ) <[Marker.disj (P.interval j).leftBoundary.complement (P.interval j).leftBoundary] (γ 2 : ℝ) ∧
    (γ 3 : ℝ) <[Marker.imp (P.interval j).leftBoundary.complement m₂.complement] (γ 1 : ℝ) := by
  exact ⟨adjacent_left_containment α _ _ _ _ (duration_pos_or_left_closed P i),
    adjacent_join α _ _ _, adjacent_right_containment α _ _ _ _ (duration_pos_or_left_closed P j)⟩
/-- The reset sequence establishes the connected merge conditions itself;
no independent clock-comparison hypothesis remains. -/
theorem predicates_merge (σ : FiniteSignal Var) (J : MarkedInterval)
    {D : Set ℝ} (P : IntervalPartition D) (i j : Fin P.size)
    (α : ClockValuation (Fin 4)) (m₂ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    let γ := twoDefer α (STLTableau.Judgement.duration P i) (STLTableau.Judgement.duration P j)
    (Predicate.holds σ J γ (.bounded 0 1 (P.interval i).leftBoundary
        (P.interval j).leftBoundary.complement kind I φ) ∧
      Predicate.holds σ J γ (.bounded 2 3 (P.interval j).leftBoundary
        m₂.complement kind I φ)) ↔
      Predicate.holds σ J γ (.bounded 0 3 (P.interval i).leftBoundary
        m₂.complement kind I φ) := by
  have h := partition_generated_merge_conditions P i j α m₂
  exact Predicate.predicate_merge_bounded_connected σ J _ 0 1 2 3
    (P.interval i).leftBoundary (P.interval j).leftBoundary.complement
    (P.interval j).leftBoundary m₂.complement kind I φ h.1 h.2.1 h.2.2

end STLTableau.Section3.ConnectedDefer
