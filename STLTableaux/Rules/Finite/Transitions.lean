import STLTableaux.Semantics.Predicates.Predicates

namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

/-- Advancing across adjacent pieces enlarges an `↑` scope and its shifted
checking region. Nonempty singleton next pieces are included. -/
theorem upper_of_adjacent (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hadj : J.right = K.left) (hne : K.carrier.Nonempty) :
    predicateSatisfies σ K β (.upper c b kind I φ) →
      predicateSatisfies σ J α (.upper c b kind I φ) := by
  have hr : ∀ (x a : ℝ), x <[J.rightBoundary] (J.right + a) →
      x <[K.rightBoundary] (K.right + a) := by
    intro x a hx
    have hle : J.right ≤ K.right := hadj ▸
      (MarkedInterval.nonempty_iff K).1 hne |>.elim le_of_lt (fun h => h.1.le)
    rcases hle.lt_or_eq with hlt | heq
    · left; rcases hx with hx | ⟨hx, _⟩ <;> linarith
    · have heK : K.left = K.right := hadj.symm.trans heq
      have hinc : K.rightBoundary.Includes := by
        rcases (MarkedInterval.nonempty_iff K).1 hne with hlt | ⟨_, hm⟩
        · exact (not_lt_of_ge heK.ge hlt).elim
        · exact ((Marker.includes_conj _ _).1 hm).2
      rcases hx with hx | ⟨hx, _⟩
      · exact Or.inl (heq ▸ hx)
      · exact Or.inr ⟨heq ▸ hx, hinc⟩
  rw [upper_temporal, upper_temporal]
  apply temporal_mono σ kind I φ
  · cases kind <;> intro t ht <;>
      change (J.left - (α c : ℝ) <[b] t) ∧ (t <[J.rightBoundary] J.right) at ht <;>
      change (K.left - (β c : ℝ) <[b] t) ∧ (t <[K.rightBoundary] K.right) <;>
      exact ⟨hc ▸ ht.1, by simpa only [add_zero] using hr t 0 (by simpa only [add_zero] using ht.2)⟩
  · cases kind <;> intro t ht <;>
      change (J.left - (α c : ℝ) + I.lower <[b] t) ∧
        (t <[J.rightBoundary] (J.right + I.upper)) at ht <;>
      change (K.left - (β c : ℝ) + I.lower <[b] t) ∧
        (t <[K.rightBoundary] (K.right + I.upper)) <;>
      exact ⟨by simpa only [hc] using ht.1, hr t I.upper ht.2⟩

/-- Equal tracked endpoints give equal `↑↓` predicates at different positions. -/
theorem bounded_of_equal_endpoints (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.left - (α d : ℝ) = K.left - (β d : ℝ)) :
    predicateSatisfies σ J α (.bounded c d b q kind I φ) ↔
      predicateSatisfies σ K β (.bounded c d b q kind I φ) := by
  cases kind <;> simp only [predicateSatisfies, scope, alwaysRegion, hc, hd]

/-- Lemma 3, implication (1), universally quantified judgement form. -/
theorem upper_implies_bounded_judgement (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.upper c b kind I φ)) ⇒ₚ
      Judgement.predicate (.bounded c d b q kind I φ) := by
  intro σ P α k hs
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk] at hs ⊢
    exact upper_implies_bounded σ _ α c d b q kind I φ (P.nonempty _) hs
  · simpa only [satisfies, dif_neg hk] using hs

/-- Lemma 3.11 (2), both operators, with no suffix guards. -/
theorem next_upper_implies_upper (c : Clock) (b : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    Xⱼ (Judgement.predicate (.upper c b kind I φ)) ⇒ₚ
      Judgement.predicate (.upper c b kind I φ) := by
  intro σ P α k hs
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · simp only [satisfies, dif_pos hk, dif_pos hn] at hs ⊢
      exact upper_of_adjacent σ _ _ α _ c b kind I φ
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn c).symm
        (P.adjacent_right_eq_left ⟨k.1, hk⟩ hn) (P.nonempty _) hs
    · simp [satisfies, hk, hn] at hs
  · simp [satisfies, hk] at hs

/-- Lemma 3.11 (3), both operators. In fact the two predicates
have identical meanings whenever the next interval exists. -/
theorem next_bounded_implies_bounded (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    Xⱼ (Judgement.predicate (.bounded c d b q kind I φ)) ⇒ₚ
      Judgement.predicate (.bounded c d b q kind I φ) := by
  intro σ P α k hs
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · simp only [satisfies, dif_pos hk, dif_pos hn] at hs ⊢
      exact (bounded_of_equal_endpoints σ _ _ α _ c d b q kind I φ
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn c).symm
        (Judgement.next_left_sub_elapse_eq P α ⟨k.1, hk⟩ hn d).symm).2 hs
    · simp [satisfies, hk, hn] at hs
  · simp [satisfies, hk] at hs

/-- Lemma 3.11 (4); freshness of the reset clock is explicit. -/
theorem next_reset_bounded_implies_upper [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    Xⱼ (⟦d ↦ᶜ 0⟧ ·ⱼ (Judgement.predicate (.bounded c d b (¬ₘ m) kind I φ) ∧ⱼ lty[m])) ⇒ₚ
      Judgement.predicate (.upper c b kind I φ) := by
  intro σ P α k hs
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let γ := ClockResetSet.elapse α (Judgement.duration P i)
      let β := (⟦d ↦ᶜ 0⟧).apply γ
      have hβc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
      have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
      simp only [satisfies, dif_pos hk, dif_pos hn] at hs ⊢
      have hc : (P.interval i).left - (α c : ℝ) =
          (P.interval j).left - (β c : ℝ) := by
        rw [hβc]; exact (Judgement.next_left_sub_elapse_eq P α i hn c).symm
      have hd : (P.interval i).right = (P.interval j).left - (β d : ℝ) := by
        simpa [hβd] using P.adjacent_right_eq_left i hn
      have hm : (P.interval i).rightBoundary = ¬ₘ m :=
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hs.2)
      have hp : predicateSatisfies σ (P.interval j) β
          (.bounded c d b (¬ₘ m) kind I φ) := hs.1
      change predicateSatisfies σ (P.interval i) α (.upper c b kind I φ)
      rw [upper_temporal]
      rw [bounded_temporal] at hp
      have he : scope (P.interval i) α (.upper c b kind I φ) =
          scope (P.interval j) β (.bounded c d b (¬ₘ m) kind I φ) := by
        cases kind <;> simp only [scope, hc, hd, hm]
      exact (temporal_congr σ kind I φ he).2 hp
    · simp [satisfies, hk, hn] at hs
  · simp [satisfies, hk] at hs

/-- Original overlap specialization, including the terminal position.
The extended manuscript statement is `Section3.Judgement.predicate_merge_connected`. -/
theorem merge_at (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hjoin : (α d₁ : ℝ) <[Marker.conj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    satisfies σ P α k
      (.conj (.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ))
        (.predicate (.upper c₂ b₂ kind I φ))) ↔
      satisfies σ P α k (.predicate (.upper c₁ b₁ kind I φ)) := by
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk]
    exact predicate_merge σ _ α c₁ d₁ c₂ b₁ q₁ b₂ kind I φ (P.nonempty _) hjoin hleft
  · simp [satisfies, hk]

end STLTableau
