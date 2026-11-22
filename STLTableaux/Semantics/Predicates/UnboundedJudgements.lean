import STLTableaux.Semantics.Predicates.UnboundedProperties
import STLTableaux.Rules.Unbounded.UnboundedClockedRules

/-! The Section 3 judgement implications and corrected reset decomposition
for unbounded timing. The clocked syntax and interpretation are independent
of the finite proof-local caps used in structural lemmas. -/
namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

/-- Implication (1), including the terminal position. -/
theorem upper_implies_bounded_at (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Node.holds σ P α k (.predicate (.upper c b kind a φ)) →
      Node.holds σ P α k (.predicate (.bounded c d b q kind a φ)) := by
  by_cases hk : k.1 < P.size
  · simp only [Node.holds, dif_pos hk]
    exact upper_implies_bounded σ _ α c d b q kind a φ (P.nonempty _)
  · simp [Node.holds, hk]

/-- Implication (2), for both operators. -/
theorem next_upper_implies_upper (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (b : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Node.holds σ P α k (.next (.predicate (.upper c b kind a φ))) →
      Node.holds σ P α k (.predicate (.upper c b kind a φ)) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · simp only [Node.holds, dif_pos hk, dif_pos hn]
      exact upper_of_adjacent σ _ _ α _ c b kind a φ
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn c).symm
        (P.adjacent_right_eq_left ⟨k.1, hk⟩ hn) (P.nonempty _)
    · simp [Node.holds, hk, hn]
  · simp [Node.holds, hk]

/-- Implication (3), preserving both tracked endpoints. -/
theorem next_bounded_implies_bounded (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Node.holds σ P α k (.next (.predicate (.bounded c d b q kind a φ))) →
      Node.holds σ P α k (.predicate (.bounded c d b q kind a φ)) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · simp only [Node.holds, dif_pos hk, dif_pos hn]
      exact (bounded_transport σ _ _ α _ c d b q kind a φ
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn c).symm
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn d).symm).2
    · simp [Node.holds, hk, hn]
  · simp [Node.holds, hk]

/-- Implication (4); the reset clock is fresh. -/
theorem next_reset_bounded_implies_upper [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) :
    Node.holds σ P α k
      (.next (.reset (ClockResetSet.singleton d 0)
        (.conj (.predicate (.bounded c d b (¬ₘ m) kind a φ)) (.marker m)))) →
      Node.holds σ P α k (.predicate (.upper c b kind a φ)) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · intro hs
      simp only [Node.holds, dif_pos hk, dif_pos hn] at hs ⊢
      exact (upper_frozen_transport σ P α k hn c d b m kind a φ hcd hs.2).2 hs.1
    · simp [Node.holds, hk, hn]
  · simp [Node.holds, hk]

/-- Proposition 3.10 (1) for unbounded timing and a fixed marker. -/
theorem opening_correct_of_marker [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary) :
    Node.holds σ P α k (.plain (formula kind a φ)) ↔
      Node.holds σ P α k (opening c m kind a φ) := by
  by_cases hk : k.1 < P.size
  · let J := P.interval ⟨k.1,hk⟩
    have hD : J.carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1,hk⟩,ht⟩
    have h := plain_iff_upper_zero σ J ((ClockResetSet.singleton c 0).apply α)
      c m kind a φ (P.nonempty _) hD (by simp) (hm hk)
    simpa only [Node.holds, opening, dif_pos hk, ← hm hk, and_true, J] using h
  · simp [Node.holds, opening, hk]

/-- Proposition 3.10 (2) for unbounded timing, with the unclocked predicate
under the reset. -/
theorem reset_split_correct [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hmarker : (α c : ℝ) = 0 → m.Includes → b.Includes) :
    Node.holds σ P α k (.predicate (.upper c b kind a φ)) ↔
      Node.holds σ P α k
        (.reset (ClockResetSet.singleton d 0)
          (.conj (.conj (.predicate (.bounded c d b (¬ₘ m) kind a φ)) (.marker m))
            (.plain (formula kind a φ)))) := by
  by_cases hk : k.1 < P.size
  · let J := P.interval ⟨k.1, hk⟩
    let β := (ClockResetSet.singleton d 0).apply α
    have hβc : β c = α c := ClockResetSet.apply_singleton_of_ne 0 α hcd
    have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 α
    have hD : J.carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1, hk⟩, ht⟩
    have hs := upper_split σ J β c d b kind a φ (P.nonempty _) hD
      (by simp only [hβd, NNReal.coe_zero])
      (by rw [hβc, ← hm hk]; exact hmarker)
    have he : satisfies σ J β (.upper c b kind a φ) ↔
        satisfies σ J α (.upper c b kind a φ) := by
      cases kind <;> simp only [satisfies, temporalSatisfies, scope, hβc]
    rw [he, ← hm hk] at hs
    simpa only [Node.holds, dif_pos hk, ← hm hk, and_true, J, β] using hs
  · simp [Node.holds, hk]

/-- The unbounded split under current-interval containment, including terminal. -/
theorem reset_split_correct_of_contains [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hm : ∀ hk : k.1 < P.size, m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hcontains : ∀ hk : k.1 < P.size,
      (P.interval ⟨k.1, hk⟩).carrier ⊆
        (scope (P.interval ⟨k.1, hk⟩) α (.upper c b kind a φ)).carrier) :
    Node.holds σ P α k (.predicate (.upper c b kind a φ)) ↔
      Node.holds σ P α k
        (.reset (ClockResetSet.singleton d 0)
          (.conj (.conj (.predicate (.bounded c d b (¬ₘ m) kind a φ)) (.marker m))
            (.plain (formula kind a φ)))) := by
  by_cases hk : k.1 < P.size
  · apply reset_split_correct σ P α k c d b m kind a φ hcd hm
    rw [hm hk]
    exact (IntervalPredicate.current_subset_upperScope_iff _ α c b (P.nonempty _)).1
      (hcontains hk)
  · simp [Node.holds, hk]

/-- Merge, including terminal positions. -/
theorem merge_at (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var)
    (hjoin : (α d₁ : ℝ) <[Marker.conj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    Node.holds σ P α k
      (.conj (.predicate (.bounded c₁ d₁ b₁ q₁ kind a φ))
        (.predicate (.upper c₂ b₂ kind a φ))) ↔
      Node.holds σ P α k (.predicate (.upper c₁ b₁ kind a φ)) := by
  by_cases hk : k.1 < P.size
  · simp only [Node.holds, dif_pos hk]
    exact predicate_merge σ _ α c₁ d₁ c₂ b₁ q₁ b₂ kind a φ (P.nonempty _) hjoin hleft
  · simp [Node.holds, hk]

end STLTableau.UnboundedClocked
