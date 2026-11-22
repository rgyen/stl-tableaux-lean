import STLTableaux.Semantics.Predicates.UnboundedStructural
import STLTableaux.Semantics.IntervalSemantics
import STLTableaux.Semantics.Predicates.UnboundedProperties

/-! Interval predicates and interval sequence judgements with bounded or
unbounded timing intervals (Definitions 3.1 and 3.5). -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}

inductive Predicate (Clock Var : Type*) where
  | plain (φ : Formula Var)
  | upper (c : Clock) (b : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
  | bounded (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)

namespace Predicate

def ofFinite : IntervalPredicate Clock Var → Predicate Clock Var
  | .plain φ => .plain φ
  | .upper c b kind I φ => .upper c b kind (.bounded I) φ
  | .bounded c d b q kind I φ => .bounded c d b q kind (.bounded I) φ

def ofUnbounded : UnboundedClocked.Predicate Clock Var → Predicate Clock Var
  | .upper c b kind a φ => .upper c b kind (.unbounded a) φ
  | .bounded c d b q kind a φ => .bounded c d b q kind (.unbounded a) φ

def holds (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock) :
    Predicate Clock Var → Prop
  | .plain φ => STLTableau.predicateSatisfies σ J α (.plain φ)
  | .upper c b kind (.bounded I) φ => STLTableau.predicateSatisfies σ J α (.upper c b kind I φ)
  | .bounded c d b q kind (.bounded I) φ =>
      STLTableau.predicateSatisfies σ J α (.bounded c d b q kind I φ)
  | .upper c b kind (.unbounded a) φ => UnboundedClocked.satisfies σ J α (.upper c b kind a φ)
  | .bounded c d b q kind (.unbounded a) φ =>
      UnboundedClocked.satisfies σ J α (.bounded c d b q kind a φ)

@[simp] theorem holds_ofFinite (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (p : IntervalPredicate Clock Var) :
    holds σ J α (ofFinite p) ↔ STLTableau.predicateSatisfies σ J α p := by cases p <;> rfl
@[simp] theorem holds_ofUnbounded (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (p : UnboundedClocked.Predicate Clock Var) :
    holds σ J α (ofUnbounded p) ↔ UnboundedClocked.satisfies σ J α p := by cases p <;> rfl

/-- Merge an `↑↓` predicate and an `↑` predicate with connected scopes.
The timing interval may be bounded or unbounded. -/
theorem predicate_merge_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty)
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    (holds σ J α (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      holds σ J α (.upper c₂ b₂ kind I φ)) ↔
      holds σ J α (.upper c₁ b₁ kind I φ) := by
  cases I with
  | bounded I => exact STLTableau.predicate_merge_connected σ J α c₁ d₁ c₂ b₁ q₁ b₂ kind I φ hne hjoin hleft
  | unbounded a => exact UnboundedClocked.predicate_merge_connected σ J α c₁ d₁ c₂ b₁ q₁ b₂ kind a φ hne hjoin hleft

end Predicate

inductive Judgement (Clock Var : Type*) where
  | terminal
  | clock (c : Clock) (r : ClockRelation) (a : NNReal)
  | marker (m : Marker)
  | predicate (p : Predicate Clock Var)
  | next (body : Judgement Clock Var)
  | reset (resets : ClockResetSet Clock) (body : Judgement Clock Var)
  | conj (left right : Judgement Clock Var)

namespace Judgement

def holds (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : STLTableau.Judgement.Position P) → Judgement Clock Var → Prop
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .marker m => if h : k.1 < P.size then
      (P.interval ⟨k.1,h⟩).leftBoundary = m else m = ●
  | k, .predicate p => if h : k.1 < P.size then Predicate.holds σ (P.interval ⟨k.1,h⟩) α p else False
  | k, .next Ψ => if h : k.1 < P.size then
      holds σ P (ClockResetSet.elapse α (STLTableau.Judgement.duration P ⟨k.1,h⟩))
        ⟨k.1 + 1,by omega⟩ Ψ else False
  | k, .reset Λ Ψ => holds σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => holds σ P α k Φ ∧ holds σ P α k Ψ

/-- Extended Lemma 3.12 in mixed judgements, including the terminal position. -/
theorem predicate_merge_connected (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    holds σ P α k (.conj (.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ))
      (.predicate (.upper c₂ b₂ kind I φ))) ↔
      holds σ P α k (.predicate (.upper c₁ b₁ kind I φ)) := by
  by_cases hk : k.1 < P.size
  · simpa only [holds, dif_pos hk] using
      Predicate.predicate_merge_connected σ (P.interval ⟨k.1,hk⟩) α
        c₁ d₁ c₂ b₁ q₁ b₂ kind I φ (P.nonempty _) hjoin hleft
  · simp only [holds, dif_neg hk, and_self]

def ofFinite : STLTableau.Judgement Clock Var → Judgement Clock Var
  | .terminal => .terminal
  | .clock c r a => .clock c r a
  | .leftMarker m => .marker m
  | .predicate p => .predicate (Predicate.ofFinite p)
  | .next Ψ => .next (ofFinite Ψ)
  | .reset Λ Ψ => .reset Λ (ofFinite Ψ)
  | .conj Φ Ψ => .conj (ofFinite Φ) (ofFinite Ψ)

def ofUnbounded : UnboundedClocked.Node Clock Var → Judgement Clock Var
  | .terminal => .terminal
  | .clock c r a => .clock c r a
  | .marker m => .marker m
  | .plain φ => .predicate (.plain φ)
  | .predicate p => .predicate (Predicate.ofUnbounded p)
  | .next Ψ => .next (ofUnbounded Ψ)
  | .reset Λ Ψ => .reset Λ (ofUnbounded Ψ)
  | .conj Φ Ψ => .conj (ofUnbounded Φ) (ofUnbounded Ψ)

@[simp] theorem holds_ofFinite (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (Ψ : STLTableau.Judgement Clock Var) :
    holds σ P α k (ofFinite Ψ) ↔ STLTableau.satisfies σ P α k Ψ := by
  induction Ψ generalizing α k with
  | next Ψ ih => simp only [ofFinite, holds, STLTableau.satisfies]; split <;> simp_all
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | predicate p => simp only [ofFinite, holds, STLTableau.satisfies, Predicate.holds_ofFinite]
  | terminal => rfl
  | clock c r a => rfl
  | leftMarker m => rfl

@[simp] theorem holds_ofUnbounded (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (Ψ : UnboundedClocked.Node Clock Var) :
    holds σ P α k (ofUnbounded Ψ) ↔ UnboundedClocked.Node.holds σ P α k Ψ := by
  induction Ψ generalizing α k with
  | next Ψ ih => simp only [ofUnbounded, holds, UnboundedClocked.Node.holds]; split <;> simp_all
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | predicate p => simp only [ofUnbounded, holds, UnboundedClocked.Node.holds, Predicate.holds_ofUnbounded]
  | plain φ => rfl
  | terminal => rfl
  | clock c r a => rfl
  | marker m => rfl

def freeClocks : Judgement Clock Var → Set Clock
  | .terminal | .marker _ | .predicate (.plain _) => ∅
  | .clock c _ _ => {c}
  | .predicate (.upper c _ _ _ _) => {c}
  | .predicate (.bounded c d _ _ _ _ _) => {c, d}
  | .next Ψ => freeClocks Ψ
  | .reset Λ Ψ => freeClocks Ψ \ Λ.clocks
  | .conj Φ Ψ => freeClocks Φ ∪ freeClocks Ψ

/-- Irrelevant-reset lemma for judgements containing unbounded predicates. -/
theorem holds_congr_of_agree {Ψ : Judgement Clock Var} {α β : ClockValuation Clock}
    (h : ∀ c ∈ freeClocks Ψ, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (k : STLTableau.Judgement.Position P) :
    holds σ P α k Ψ ↔ holds σ P β k Ψ := by
  induction Ψ generalizing α β k with
  | terminal => rfl
  | marker m => rfl
  | clock c r a =>
      have hc := h c (by simp [freeClocks])
      simp [holds, hc]
  | predicate p =>
      by_cases hk : k.1 < P.size
      · simp only [holds, dif_pos hk]
        cases p with
        | plain φ => rfl
        | upper c b kind I φ =>
            have hc := h c (by simp [freeClocks])
            cases I <;> cases kind <;>
              simp only [Predicate.holds, STLTableau.predicateSatisfies, IntervalPredicate.scope,
                UnboundedClocked.satisfies, UnboundedClocked.temporalSatisfies,
                UnboundedClocked.scope, hc]
        | bounded c d b q kind I φ =>
            have hc := h c (by simp [freeClocks])
            have hd := h d (by simp [freeClocks])
            cases I <;> cases kind <;>
              simp only [Predicate.holds, STLTableau.predicateSatisfies, IntervalPredicate.scope,
                UnboundedClocked.satisfies, UnboundedClocked.temporalSatisfies,
                UnboundedClocked.scope, hc, hd]
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

def Equivalent (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
    holds σ P α k Φ ↔ holds σ P α k Ψ

theorem conj_idem (Ψ : Judgement Clock Var) : Equivalent (.conj Ψ Ψ) Ψ := by
  intro σ P α k
  exact and_self_iff

theorem conj_comm (Φ Ψ : Judgement Clock Var) : Equivalent (.conj Φ Ψ) (.conj Ψ Φ) := by
  intro σ P α k
  exact and_comm

theorem next_conj (Φ Ψ : Judgement Clock Var) :
    Equivalent (.next (.conj Φ Ψ)) (.conj (.next Φ) (.next Ψ)) := by
  intro σ P α k
  simp only [holds]
  split <;> simp_all

theorem reset_conj_reset_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
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
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
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

end STLTableau.Section3.Judgement
