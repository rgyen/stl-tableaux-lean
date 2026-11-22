import STLTableaux.Syntax.Judgements

/-! Satisfaction of interval predicates and interval sequence judgements (Section 3).
Always checking points and eventuality witnesses range over the signal domain. -/
namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

def predicateSatisfies (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) : IntervalPredicate Clock Var → Prop
  | .plain φ => ∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ φ
  | .upper c b .always I φ =>
      ∀ t : σ.Time, t.1 ∈ alwaysRegion (scope J α (.upper c b .always I φ)) I →
        (σ, t) ⊨ φ
  | .upper c b .eventually I φ =>
      ∀ t : ℝ, t ∈ scope J α (.upper c b .eventually I φ) →
        ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧ (σ, u) ⊨ φ
  | .bounded c d b q .always I φ =>
      ∀ t : σ.Time, t.1 ∈ alwaysRegion (scope J α (.bounded c d b q .always I φ)) I →
        (σ, t) ⊨ φ
  | .bounded c d b q .eventually I φ =>
      ∀ t : ℝ, t ∈ scope J α (.bounded c d b q .eventually I φ) →
        ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧ (σ, u) ⊨ φ

notation:45 "(" σ ", " J ", " α ")" "⊨ₚᵢ" p =>
  STLTableau.predicateSatisfies σ J α p

def satisfies (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Judgement Clock Var → Prop
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .leftMarker m =>
      if h : k.1 < P.size then (P.interval ⟨k.1, h⟩).leftBoundary = m else m = ●
  | k, .predicate p =>
      if h : k.1 < P.size then (σ, P.interval ⟨k.1, h⟩, α) ⊨ₚᵢ p else False
  | k, .next Ψ =>
      if h : k.1 < P.size then
        satisfies σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, h⟩))
          ⟨k.1 + 1, by omega⟩ Ψ
      else False
  | k, .reset Λ Ψ => satisfies σ P (Λ.apply α) k Ψ
  | k, .conj Ψ₁ Ψ₂ => satisfies σ P α k Ψ₁ ∧ satisfies σ P α k Ψ₂


notation:45 "(" σ ", " P ", " α ", " k ")" "⊨ₚ" Ψ =>
  STLTableau.satisfies σ P α k Ψ

def Equivalent (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P),
    satisfies σ P α k Φ ↔ satisfies σ P α k Ψ

def Implies (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P),
    satisfies σ P α k Φ → satisfies σ P α k Ψ

infix:50 " ≡ₚ " => STLTableau.Equivalent
infix:50 " ⇒ₚ " => STLTableau.Implies

open STLTableau.Judgement
@[simp] theorem satisfies_terminal (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) :
    ((σ, P, α, k) ⊨ₚ (∗ : Judgement Clock Var)) ↔ k.1 = P.size := Iff.rfl

@[simp] theorem satisfies_conj (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (Φ Ψ : Judgement Clock Var) :
    ((σ, P, α, k) ⊨ₚ (Φ ∧ⱼ Ψ)) ↔
      ((σ, P, α, k) ⊨ₚ Φ) ∧ ((σ, P, α, k) ⊨ₚ Ψ) := Iff.rfl

/-- Interval-predicate satisfaction depends only on its occurring clocks. -/
private theorem predicate_satisfies_congr {p : IntervalPredicate Clock Var}
    {α β : ClockValuation Clock} (h : ∀ c ∈ predicateClocks p, α c = β c)
    (σ : FiniteSignal Var) (J : MarkedInterval) :
    ((σ, J, α) ⊨ₚᵢ p) ↔ ((σ, J, β) ⊨ₚᵢ p) := by
  cases p with
  | plain φ => rfl
  | upper c b kind I φ =>
      have hc : α c = β c := h c (by simp [predicateClocks])
      cases kind <;> simp [predicateSatisfies, IntervalPredicate.scope, hc]
  | bounded c d b b' kind I φ =>
      have hc : α c = β c := h c (by simp [predicateClocks])
      have hd : α d = β d := h d (by simp [predicateClocks])
      cases kind <;> simp [predicateSatisfies, IntervalPredicate.scope, hc, hd]

/-- Satisfaction depends only on the free clocks of a judgement. -/
theorem satisfies_congr_of_agree {Ψ : Judgement Clock Var}
    {α β : ClockValuation Clock} (h : ∀ c ∈ freeClocks Ψ, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (k : Position P) :
    ((σ, P, α, k) ⊨ₚ Ψ) ↔ ((σ, P, β, k) ⊨ₚ Ψ) := by
  induction Ψ generalizing α β k with
  | terminal => rfl
  | clock c r a =>
      have hc := h c (by simp [freeClocks])
      simp [satisfies, hc]
  | leftMarker m => rfl
  | predicate p =>
      simp only [satisfies]
      split
      · exact predicate_satisfies_congr h σ _
      · rfl
  | next Ψ ih =>
      simp only [satisfies]
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
          have hcfree : c ∈ freeClocks (.reset Λ Ψ) := ⟨hc, hcnot⟩
          have hα : Λ.apply α c = α c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          have hβ : Λ.apply β c = β c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          rw [hα, hβ]
          exact h c hcfree
  | conj Φ Ψ ihΦ ihΨ =>
      constructor
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).1 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).1 hΨ
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).2 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).2 hΨ

/-- Proposition 3.9 (1), idempotence. -/
theorem conj_idem (Ψ : Judgement Clock Var) : Ψ ∧ⱼ Ψ ≡ₚ Ψ := by
  intro σ P α k
  simp

/-- Proposition 3.9 (1), commutativity. -/
theorem conj_comm (Φ Ψ : Judgement Clock Var) : Φ ∧ⱼ Ψ ≡ₚ Ψ ∧ⱼ Φ := by
  intro σ P α k
  exact and_comm

/-- Proposition 3.9 (1), distribution of next over conjunction. -/
theorem next_conj (Φ Ψ : Judgement Clock Var) : Xⱼ (Φ ∧ⱼ Ψ) ≡ₚ (Xⱼ Φ) ∧ⱼ (Xⱼ Ψ) := by
  intro σ P α k
  simp only [satisfies]
  split <;> simp_all

/-- Proposition 3.9 (2), merging two parallel reset judgements. -/
theorem reset_conj_reset_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (Λ₁ ·ⱼ Φ)))
    (h₂₁ : Disjoint Λ₁.clocks (freeClocks (Λ₂ ·ⱼ Ψ))) :
    (Λ₁ ·ⱼ Φ) ∧ⱼ (Λ₂ ·ⱼ Ψ) ≡ₚ (Λ₁.union Λ₂) ·ⱼ (Φ ∧ⱼ Ψ) := by
  intro σ P α k
  have hagree₁ : ∀ c ∈ freeClocks Φ,
      (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := by
        intro hc₂
        exact Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  have hagree₂ : ∀ c ∈ freeClocks Ψ,
      (Λ₁.union Λ₂).apply α c = Λ₂.apply α c := by
    intro c hc
    by_cases hc₂ : c ∈ Λ₂.clocks
    · exact ClockResetSet.apply_union_eq_right_of_consistent Λ₁ Λ₂ hcon α hc₂
    · have hc₁ : c ∉ Λ₁.clocks := by
        intro hc₁
        exact Set.disjoint_left.1 h₂₁ hc₁ ⟨hc, hc₂⟩
      exact ClockResetSet.apply_union_eq_right_of_not_mem Λ₁ Λ₂ α hc₁
  have hΦ := satisfies_congr_of_agree hagree₁ σ P k
  have hΨ := satisfies_congr_of_agree hagree₂ σ P k
  change
    (((σ, P, Λ₁.apply α, k) ⊨ₚ Φ) ∧ ((σ, P, Λ₂.apply α, k) ⊨ₚ Ψ)) ↔
      ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ₚ Φ) ∧
        ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ₚ Ψ)
  exact and_congr hΦ.symm hΨ.symm

/-- Proposition 3.9 (2), pulling a nested reset out of a
conjunction. The manuscript states the same symmetric side conditions as for
`reset_conj_reset_equiv_union`; only the condition protecting `Φ` is needed
for this orientation. -/
theorem reset_conj_nested_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (Λ₁ ·ⱼ Φ))) :
    Λ₁ ·ⱼ (Φ ∧ⱼ (Λ₂ ·ⱼ Ψ)) ≡ₚ (Λ₁.union Λ₂) ·ⱼ (Φ ∧ⱼ Ψ) := by
  intro σ P α k
  have hagree : ∀ c ∈ freeClocks Φ,
      (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := by
        intro hc₂
        exact Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  have hΦ := satisfies_congr_of_agree hagree σ P k
  have hreset := ClockResetSet.apply_apply_eq_union Λ₁ Λ₂ hcon α
  change
    (((σ, P, Λ₁.apply α, k) ⊨ₚ Φ) ∧
        ((σ, P, Λ₂.apply (Λ₁.apply α), k) ⊨ₚ Ψ)) ↔
      ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ₚ Φ) ∧
        ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ₚ Ψ)
  rw [hreset]
  exact and_congr hΦ.symm Iff.rfl


end STLTableau
