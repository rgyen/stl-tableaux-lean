import STLTableaux.Semantics.Predicates.UnboundedClocked
import STLTableaux.Rules.Finite.Equivalences

/-! Structural properties of the original clocked predicates for `[a,∞)`.
A common finite cap is used only inside each proof. The statements themselves
quantify over arbitrary clock values and do not restrict tracked scopes. -/
namespace STLTableau.UnboundedClocked
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

private def commonInterval (σ : FiniteSignal Var) (J : MarkedInterval)
    (L : ℝ) (hL : 0 ≤ L) (a : NNReal) : BoundedTimeInterval :=
  ⟨a, (a : ℝ) + σ.horizon + |J.left| + L + 1, a.coe_nonneg, by
    have := σ.horizon_pos
    have := abs_nonneg J.left
    linarith⟩

private theorem capped_scope (σ : FiniteSignal Var) (J : MarkedInterval)
    (L : ℝ) (hL : 0 ≤ L) (a : NNReal) (kind : TemporalKind)
    (φ : Formula Var) (S : Scope)
    (hl : J.left - L ≤ S.left) (hr : J.left - L ≤ S.right) :
    temporalSatisfies σ kind a φ S ↔
      STLTableau.temporalSatisfies σ kind (commonInterval σ J L hL a) φ S := by
  apply temporal_iff_finite σ kind _ a φ S rfl
  · dsimp [commonInterval]
    have := neg_le_abs J.left
    have := a.coe_nonneg
    linarith
  · dsimp [commonInterval]
    have := neg_le_abs J.left
    have := a.coe_nonneg
    linarith

private theorem finite_upper (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (L : ℝ) (hL : 0 ≤ L) (hc : (α c : ℝ) ≤ L) (hJ : J.left ≤ J.right) :
    satisfies σ J α (.upper c b kind a φ) ↔
      STLTableau.predicateSatisfies σ J α
        (.upper c b kind (commonInterval σ J L hL a) φ) := by
  have h := capped_scope σ J L hL a kind φ
    (scope J α (.upper c b kind a φ)) (by dsimp [scope]; linarith)
    (by dsimp [scope]; linarith)
  simpa only [satisfies, STLTableau.upper_temporal, scope, IntervalPredicate.scope] using h

private theorem finite_bounded (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (L : ℝ) (hL : 0 ≤ L) (hc : (α c : ℝ) ≤ L) (hd : (α d : ℝ) ≤ L) :
    satisfies σ J α (.bounded c d b q kind a φ) ↔
      STLTableau.predicateSatisfies σ J α
        (.bounded c d b q kind (commonInterval σ J L hL a) φ) := by
  have h := capped_scope σ J L hL a kind φ
    (scope J α (.bounded c d b q kind a φ)) (by dsimp [scope]; linarith)
    (by dsimp [scope]; linarith)
  simpa only [satisfies, STLTableau.bounded_temporal, scope, IntervalPredicate.scope] using h

/-- Lemma 3.11 (1), both operators and arbitrary clock values. -/
theorem upper_implies_bounded (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (hne : J.carrier.Nonempty) :
    satisfies σ J α (.upper c b kind a φ) →
      satisfies σ J α (.bounded c d b q kind a φ) := by
  let L : ℝ := (α c : ℝ) + (α d : ℝ)
  have hL : 0 ≤ L := add_nonneg (α c).coe_nonneg (α d).coe_nonneg
  have hc : (α c : ℝ) ≤ L := by dsimp [L]; linarith [(α d).coe_nonneg]
  have hd : (α d : ℝ) ≤ L := by dsimp [L]; linarith [(α c).coe_nonneg]
  have hJ : J.left ≤ J.right := by
    obtain ⟨t, ht⟩ := hne
    exact (MarkedInterval.left_le_of_mem ht).trans (MarkedInterval.le_right_of_mem ht)
  intro h
  exact (finite_bounded σ J α c d b q kind a φ L hL hc hd).2
    (STLTableau.upper_implies_bounded σ J α c d b q kind _ φ hne
      ((finite_upper σ J α c b kind a φ L hL hc hJ).1 h))

/-- Connected-scope merge for infinite timing, allowing a joint endpoint
when at least one side includes it. -/
theorem predicate_merge_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    (satisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind a φ) ∧
      satisfies σ J α (.upper c₂ b₂ kind a φ)) ↔
      satisfies σ J α (.upper c₁ b₁ kind a φ) := by
  let L : ℝ := (α c₁ : ℝ) + (α d₁ : ℝ) + (α c₂ : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hc₁ : (α c₁ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α d₁).coe_nonneg, (α c₂).coe_nonneg]
  have hd₁ : (α d₁ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α c₁).coe_nonneg, (α c₂).coe_nonneg]
  have hc₂ : (α c₂ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α c₁).coe_nonneg, (α d₁).coe_nonneg]
  have hJ : J.left ≤ J.right := by
    obtain ⟨t, ht⟩ := hne
    exact (MarkedInterval.left_le_of_mem ht).trans (MarkedInterval.le_right_of_mem ht)
  rw [finite_bounded σ J α c₁ d₁ b₁ q₁ kind a φ L hL hc₁ hd₁,
    finite_upper σ J α c₂ b₂ kind a φ L hL hc₂ hJ,
    finite_upper σ J α c₁ b₁ kind a φ L hL hc₁ hJ]
  exact STLTableau.predicate_merge_connected σ J α c₁ d₁ c₂ b₁ q₁ b₂ kind _ φ hne hjoin hleft


/-- Original overlap specialization for unbounded timing.
The extended connected statement is `predicate_merge_connected`. -/
theorem predicate_merge (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hjoin : (α d₁ : ℝ) <[Marker.conj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    (satisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind a φ) ∧
      satisfies σ J α (.upper c₂ b₂ kind a φ)) ↔
      satisfies σ J α (.upper c₁ b₁ kind a φ) := by
  let L : ℝ := (α c₁ : ℝ) + (α d₁ : ℝ) + (α c₂ : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hc₁ : (α c₁ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α d₁).coe_nonneg, (α c₂).coe_nonneg]
  have hd₁ : (α d₁ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α c₁).coe_nonneg, (α c₂).coe_nonneg]
  have hc₂ : (α c₂ : ℝ) ≤ L := by
    dsimp [L]; linarith [(α c₁).coe_nonneg, (α d₁).coe_nonneg]
  have hJ : J.left ≤ J.right := by
    obtain ⟨t, ht⟩ := hne
    exact (MarkedInterval.left_le_of_mem ht).trans (MarkedInterval.le_right_of_mem ht)
  rw [finite_bounded σ J α c₁ d₁ b₁ q₁ kind a φ L hL hc₁ hd₁,
    finite_upper σ J α c₂ b₂ kind a φ L hL hc₂ hJ,
    finite_upper σ J α c₁ b₁ kind a φ L hL hc₁ hJ]
  exact STLTableau.predicate_merge σ J α c₁ d₁ c₂ b₁ q₁ b₂ kind _ φ hne hjoin hleft

/-- The unbounded instance of propagation across adjacent partition pieces. -/
theorem upper_of_adjacent (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b : Marker) (kind : TemporalKind)
    (a : NNReal) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hadj : J.right = K.left) (hne : K.carrier.Nonempty) :
    satisfies σ K β (.upper c b kind a φ) →
      satisfies σ J α (.upper c b kind a φ) := by
  have hr : ∀ x : ℝ, x <[J.rightBoundary] J.right → x <[K.rightBoundary] K.right := by
    intro x hx
    have hle : J.right ≤ K.right := hadj ▸
      (MarkedInterval.nonempty_iff K).1 hne |>.elim le_of_lt (fun h => h.1.le)
    rcases hle.lt_or_eq with hlt | heq
    · left
      rcases hx with hx | ⟨hx, _⟩ <;> linarith
    · have heK : K.left = K.right := hadj.symm.trans heq
      have hinc : K.rightBoundary.Includes := by
        rcases (MarkedInterval.nonempty_iff K).1 hne with hlt | ⟨_, hm⟩
        · exact (not_lt_of_ge heK.ge hlt).elim
        · exact ((Marker.includes_conj _ _).1 hm).2
      rcases hx with hx | ⟨hx, _⟩
      · exact Or.inl (heq ▸ hx)
      · exact Or.inr ⟨heq ▸ hx, hinc⟩
  cases kind with
  | always =>
      intro h u hu
      apply h u
      change K.left - (β c : ℝ) + (a : ℝ) <[b] u.1
      change J.left - (α c : ℝ) + (a : ℝ) <[b] u.1 at hu
      simpa only [hc] using hu
  | eventually =>
      intro h t ht
      apply h t
      change (J.left - (α c : ℝ) <[b] t) ∧ (t <[J.rightBoundary] J.right) at ht
      change (K.left - (β c : ℝ) <[b] t) ∧ (t <[K.rightBoundary] K.right)
      exact ⟨hc ▸ ht.1, hr t ht.2⟩

/-- Proposition 3.10 (2) for unbounded timing, at a valuation after resetting the
fresh right clock. Both unbounded temporal operators are included. -/
theorem upper_split (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hd : (α d : ℝ) = 0)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes) :
    satisfies σ J α (.upper c b kind a φ) ↔
      satisfies σ J α (.bounded c d b (¬ₘ J.leftBoundary) kind a φ) ∧
        (∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ formula kind a φ) := by
  let L : ℝ := (α c : ℝ) + (α d : ℝ)
  have hL : 0 ≤ L := add_nonneg (α c).coe_nonneg (α d).coe_nonneg
  have hc : (α c : ℝ) ≤ L := by dsimp [L]; linarith [(α d).coe_nonneg]
  have hdL : (α d : ℝ) ≤ L := by dsimp [L]; linarith [(α c).coe_nonneg]
  have hJ : J.left ≤ J.right := by
    obtain ⟨t, ht⟩ := hne
    exact (MarkedInterval.left_le_of_mem ht).trans (MarkedInterval.le_right_of_mem ht)
  let I := commonInterval σ J L hL a
  have hB : σ.horizon ≤ I.upper := by
    dsimp [I, commonInterval]
    have := a.coe_nonneg
    have := abs_nonneg J.left
    linarith
  have hplain : (∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ formula kind a φ) ↔
      STLTableau.predicateSatisfies σ J α (.plain (match kind with
        | .always => □[(I : TimeInterval)] φ
        | .eventually => ◇[(I : TimeInterval)] φ)) := by
    constructor
    · intro h t ht
      exact (formula_iff_finite σ kind I a φ rfl hB t).1 (h t ht)
    · intro h t ht
      exact (formula_iff_finite σ kind I a φ rfl hB t).2 (h t ht)
  rw [finite_upper σ J α c b kind a φ L hL hc hJ,
    finite_bounded σ J α c d b (¬ₘ J.leftBoundary) kind a φ L hL hc hdL, hplain]
  have h := STLTableau.upper_decomposition_zero σ J α c d b kind I φ hd hne hD
    hmarker
  cases kind <;> exact h

end STLTableau.UnboundedClocked
