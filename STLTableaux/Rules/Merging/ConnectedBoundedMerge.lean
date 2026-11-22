import STLTableaux.Syntax.Section3Judgements

/-! Merging two `↑↓` predicates with the same temporal formula when
their scopes overlap or meet without a gap. This extends Lemma 3.12. -/
namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

private theorem bounded_union (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker) (l r : ℝ)
    (hl : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ))
    (hj : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hr : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ))
    (hwidth : l ≤ r) :
    (⟨b₁, J.left - α c₁ + l, J.left - α d₁ + r, q₁⟩ : Scope).carrier ∪
      (⟨b₂, J.left - α c₂ + l, J.left - α d₂ + r, q₂⟩ : Scope).carrier =
      (⟨b₁, J.left - α c₁ + l, J.left - α d₂ + r, q₂⟩ : Scope).carrier := by
  apply MarkedInterval.carrier_union_connected
  · rcases hl with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm⟩
  · rcases hj with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · by_cases hw : l < r
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, (Marker.includes_disj _ _).1 hm⟩
  · rcases hr with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm⟩

/-- Connected merging of two `↑↓` scopes, with both outer endpoints retained.
No nonemptiness, invariant, or signal stability hypothesis is required. -/
theorem predicate_merge_bounded_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hright : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ)) :
    (predicateSatisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      predicateSatisfies σ J α (.bounded c₂ d₂ b₂ q₂ kind I φ)) ↔
      predicateSatisfies σ J α (.bounded c₁ d₂ b₁ q₂ kind I φ) := by
  rw [bounded_temporal, bounded_temporal, bounded_temporal]
  apply temporal_union σ kind I φ
  · simpa only [scope, add_zero] using
      bounded_union J α c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂ 0 0 hleft hjoin hright le_rfl
  · simpa only [scope, alwaysRegion] using
      bounded_union J α c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂ I.lower I.upper
        hleft hjoin hright (le_of_lt I.nonSingular)

namespace UnboundedClocked

/-- Infinite-timing bounded-plus-bounded merge with the same connected endpoint conditions. -/
theorem predicate_merge_bounded_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hright : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ)) :
    (satisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind a φ) ∧
      satisfies σ J α (.bounded c₂ d₂ b₂ q₂ kind a φ)) ↔
      satisfies σ J α (.bounded c₁ d₂ b₁ q₂ kind a φ) := by
  cases kind with
  | always =>
    change ((∀ u : σ.Time, J.left - (α c₁ : ℝ) + (a : ℝ) <[b₁] u.1 → (σ, u) ⊨ φ) ∧
      (∀ u : σ.Time, J.left - (α c₂ : ℝ) + (a : ℝ) <[b₂] u.1 → (σ, u) ⊨ φ)) ↔
      (∀ u : σ.Time, J.left - (α c₁ : ℝ) + (a : ℝ) <[b₁] u.1 → (σ, u) ⊨ φ)
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      intro u hu
      apply h u
      rcases hleft with hl | ⟨hl, hm⟩
      · rcases hu with hu | ⟨hu, _⟩ <;> exact Or.inl (by linarith)
      · rcases hu with hu | ⟨hu, hb⟩
        · exact Or.inl (by linarith)
        · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩
  | eventually =>
    have hu := bounded_union J α c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂ 0 0
      hleft hjoin hright le_rfl
    simp only [add_zero] at hu
    change ((∀ t : ℝ, t ∈ (⟨b₁, J.left - α c₁, J.left - α d₁, q₁⟩ : Scope) → _) ∧
      (∀ t : ℝ, t ∈ (⟨b₂, J.left - α c₂, J.left - α d₂, q₂⟩ : Scope) → _)) ↔
      (∀ t : ℝ, t ∈ (⟨b₁, J.left - α c₁, J.left - α d₂, q₂⟩ : Scope) → _)
    constructor
    · rintro ⟨h₁, h₂⟩ t ht
      have hm : t ∈ (⟨b₁, J.left - α c₁, J.left - α d₁, q₁⟩ : Scope).carrier ∪
          (⟨b₂, J.left - α c₂, J.left - α d₂, q₂⟩ : Scope).carrier := by
        rw [hu]
        exact ht
      exact hm.elim (h₁ t) (h₂ t)
    · intro h
      constructor
      · intro t ht
        apply h t
        change t ∈ (⟨b₁, J.left - α c₁, J.left - α d₂, q₂⟩ : Scope).carrier
        rw [← hu]
        exact Or.inl ht
      · intro t ht
        apply h t
        change t ∈ (⟨b₁, J.left - α c₁, J.left - α d₂, q₂⟩ : Scope).carrier
        rw [← hu]
        exact Or.inr ht

end UnboundedClocked

namespace Section3.Predicate

/-- Mixed-timing form of the additional bounded-plus-bounded connected merge. -/
theorem predicate_merge_bounded_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hright : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ)) :
    (holds σ J α (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      holds σ J α (.bounded c₂ d₂ b₂ q₂ kind I φ)) ↔
      holds σ J α (.bounded c₁ d₂ b₁ q₂ kind I φ) := by
  cases I with
  | bounded I =>
    exact STLTableau.predicate_merge_bounded_connected σ J α c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂
      kind I φ hleft hjoin hright
  | unbounded a =>
    exact UnboundedClocked.predicate_merge_bounded_connected σ J α c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂
      kind a φ hleft hjoin hright

end Section3.Predicate

end STLTableau
