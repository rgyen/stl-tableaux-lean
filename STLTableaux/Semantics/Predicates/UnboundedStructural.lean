import STLTableaux.Rules.Unbounded.UnboundedClockedRules

namespace STLTableau.UnboundedClocked.Node
variable {Clock Var : Type*}

def freeClocks : Node Clock Var → Set Clock
  | .terminal | .plain _ | .marker _ => ∅
  | .clock c _ _ => {c}
  | .predicate (.upper c _ _ _ _) => {c}
  | .predicate (.bounded c d _ _ _ _ _) => {c, d}
  | .next Ψ => freeClocks Ψ
  | .reset Λ Ψ => freeClocks Ψ \ Λ.clocks
  | .conj Φ Ψ => freeClocks Φ ∪ freeClocks Ψ

/-- Irrelevant-reset lemma for judgements containing unbounded predicates. -/
theorem holds_congr_of_agree {Ψ : Node Clock Var} {α β : ClockValuation Clock}
    (h : ∀ c ∈ freeClocks Ψ, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (k : Judgement.Position P) :
    holds σ P α k Ψ ↔ holds σ P β k Ψ := by
  induction Ψ generalizing α β k with
  | terminal => rfl
  | plain φ => rfl
  | marker m => rfl
  | clock c r a =>
      have hc := h c (by simp [freeClocks])
      simp [holds, hc]
  | predicate p =>
      by_cases hk : k.1 < P.size
      · simp only [holds, dif_pos hk]
        cases p with
        | upper c b kind a φ =>
            have hc := h c (by simp [freeClocks])
            cases kind <;> simp only [satisfies, temporalSatisfies, scope, hc]
        | bounded c d b q kind a φ =>
            have hc := h c (by simp [freeClocks])
            have hd := h d (by simp [freeClocks])
            cases kind <;> simp only [satisfies, temporalSatisfies, scope, hc, hd]
      · simp [holds, hk]
  | next Ψ ih =>
      simp only [holds]
      split
      · apply ih
        intro c hc
        simp [ClockResetSet.elapse, h c (by simpa [freeClocks] using hc)]
      · rfl
  | reset Λ Ψ ih =>
      apply ih
      intro c hc
      cases hΛ : Λ.value c with
      | some a => simp [ClockResetSet.apply, hΛ]
      | none =>
          have hcnot : c ∉ Λ.clocks := by
            rintro ⟨a, ha⟩
            rw [hΛ] at ha
            cases ha
          simpa only [ClockResetSet.apply, hΛ] using h c ⟨hc, hcnot⟩
  | conj Φ Ψ ihΦ ihΨ =>
      exact and_congr (ihΦ (fun c hc => h c (Or.inl hc)) k)
        (ihΨ (fun c hc => h c (Or.inr hc)) k)

def Equivalent (Φ Ψ : Node Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P),
    holds σ P α k Φ ↔ holds σ P α k Ψ

theorem conj_idem (Ψ : Node Clock Var) : Equivalent (.conj Ψ Ψ) Ψ := by
  intro σ P α k
  exact and_self_iff

theorem conj_comm (Φ Ψ : Node Clock Var) : Equivalent (.conj Φ Ψ) (.conj Ψ Φ) := by
  intro σ P α k
  exact and_comm

theorem next_conj (Φ Ψ : Node Clock Var) :
    Equivalent (.next (.conj Φ Ψ)) (.conj (.next Φ) (.next Ψ)) := by
  intro σ P α k
  simp only [holds]
  split <;> simp_all

theorem reset_conj_reset_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Node Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (.reset Λ₁ Φ)))
    (h₂₁ : Disjoint Λ₁.clocks (freeClocks (.reset Λ₂ Ψ))) :
    Equivalent (.conj (.reset Λ₁ Φ) (.reset Λ₂ Ψ))
      (.reset (Λ₁.union Λ₂) (.conj Φ Ψ)) := by
  intro σ P α k
  have hagree₁ : ∀ c ∈ freeClocks Φ, (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := fun hc₂ => Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  have hagree₂ : ∀ c ∈ freeClocks Ψ, (Λ₁.union Λ₂).apply α c = Λ₂.apply α c := by
    intro c hc
    by_cases hc₂ : c ∈ Λ₂.clocks
    · exact ClockResetSet.apply_union_eq_right_of_consistent Λ₁ Λ₂ hcon α hc₂
    · have hc₁ : c ∉ Λ₁.clocks := fun hc₁ => Set.disjoint_left.1 h₂₁ hc₁ ⟨hc, hc₂⟩
      exact ClockResetSet.apply_union_eq_right_of_not_mem Λ₁ Λ₂ α hc₁
  exact and_congr (holds_congr_of_agree hagree₁ σ P k).symm
    (holds_congr_of_agree hagree₂ σ P k).symm

theorem reset_conj_nested_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Node Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (.reset Λ₁ Φ))) :
    Equivalent (.reset Λ₁ (.conj Φ (.reset Λ₂ Ψ)))
      (.reset (Λ₁.union Λ₂) (.conj Φ Ψ)) := by
  intro σ P α k
  have hagree : ∀ c ∈ freeClocks Φ, (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := fun hc₂ => Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  change (holds σ P (Λ₁.apply α) k Φ ∧ holds σ P (Λ₂.apply (Λ₁.apply α)) k Ψ) ↔ _
  rw [ClockResetSet.apply_apply_eq_union Λ₁ Λ₂ hcon α]
  exact and_congr (holds_congr_of_agree hagree σ P k).symm Iff.rfl

end STLTableau.UnboundedClocked.Node
