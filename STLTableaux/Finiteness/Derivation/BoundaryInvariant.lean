import STLTableaux.Rules.Merging.ConnectedMergeInvariant
import STLTableaux.Semantics.Invariants.NumericInvariant
import STLTableaux.Finiteness.Derivation.BoundaryExtension

/-! Boundary bounded-to-upper invariant transfer for actual mixed predicates.
Invariant transfer is stronger than the semantic boundary equivalence: it does
not need right-zero, complementary boundary markers, or satisfaction of the unclocked
temporal predicate.
The full result retains the actual eventuality condition for no past satisfaction unchanged. -/
namespace STLTableau.Section4.Finiteness.BoundaryInvariant
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- For `◇`, nonemptiness of the scope in the `↑↓` form implies
nonemptiness in the `↑` form. For a singleton current interval, the
right marker is closed. A zero left age also requires a closed left marker. -/
theorem upper_nonempty_of_bounded (J : MarkedInterval) (c d : NNReal)
    (b q : Marker) (hne : J.carrier.Nonempty)
    (h : (d : ℝ) <[Marker.conj b q] (c : ℝ)) :
    (0 : ℝ) <[Marker.conj b J.rightBoundary] ((c : ℝ) + J.right - J.left) := by
  rcases (MarkedInterval.nonempty_iff J).1 hne with hw | ⟨he,hm⟩
  · exact Or.inl (by have := c.coe_nonneg; linarith)
  · rcases h with h | ⟨hd,hbq⟩
    · exact Or.inl (by have := d.coe_nonneg; linarith)
    · by_cases hc : 0 < (c : ℝ)
      · exact Or.inl (by linarith)
      · have hc0 : (c : ℝ) = 0 := le_antisymm (le_of_not_gt hc) c.coe_nonneg
        refine Or.inr ⟨by linarith,?_⟩
        exact (Marker.includes_conj _ _).2
          ⟨((Marker.includes_conj _ _).1 hbq).1,((Marker.includes_conj _ _).1 hm).2⟩

/-- The genuine forward-soundness numeric invariant, without assuming or
manufacturing any condition for no past satisfaction. Both temporal kinds and timing types
are covered. The left positional clauses survive literally. -/
theorem numeric_bounded_to_upper (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hne : J.carrier.Nonempty)
    (h : Predicate.Numeric J α (.bounded c d b q kind I φ)) :
    Predicate.Numeric J α (.upper c b kind I φ) := by
  cases I with
  | bounded I =>
    cases kind with
    | always => exact ⟨trivial,h.2⟩
    | eventually =>
      refine ⟨⟨h.1.1,?_⟩,trivial⟩
      simpa only [add_sub_assoc] using
        upper_nonempty_of_bounded J (α c) (α d) b q hne h.1.2
  | unbounded a =>
    cases kind with
    | always => exact h
    | eventually => exact upper_nonempty_of_bounded J (α c) (α d) b q hne h

/-- The complete signal/partition-dependent invariant already has a stronger
bounded-to-upper theorem in the existing API. Its eventuality PastSeparated
conjunct uses the same c,b,I,φ and is retained, rather than rederived or dropped. -/
theorem invariant_bounded_to_upper (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var)
    (h : Predicate.Invariant σ P α k hk (.bounded c d b q kind I φ)) :
    Predicate.Invariant σ P α k hk (.upper c b kind I φ) :=
  Predicate.invariant_merge_upper_connected σ P α k hk c d b q kind I φ h

/-- Boundary instance inside the inherited reset scope. Right-zero is needed
by the semantic merger, but is unnecessary for this numeric implication. -/
theorem boundary_numeric_under_reset (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (b ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var)
    (h : Section3.Judgement.EvaluatedNumeric σ P α k
      (.reset R (.predicate (.bounded c d b (¬ₘ ℓ) kind I φ)))) :
    Section3.Judgement.EvaluatedNumeric σ P α k
      (.reset R (.predicate (.upper c b kind I φ))) := by
  intro hk
  exact numeric_bounded_to_upper _ (R.apply α) c d b (¬ₘ ℓ) kind I φ
    (P.nonempty _) (h hk)

/-- Full boundary invariant under those same actual inherited resets. -/
theorem boundary_invariant_under_reset (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (b ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var)
    (h : Section3.Judgement.EvaluatedInvariant σ P α k
      (.reset R (.predicate (.bounded c d b (¬ₘ ℓ) kind I φ)))) :
    Section3.Judgement.EvaluatedInvariant σ P α k
      (.reset R (.predicate (.upper c b kind I φ))) := by
  intro hk
  exact invariant_bounded_to_upper σ P (R.apply α) k hk c d b (¬ₘ ℓ) kind I φ (h hk)

/-- Actual state-form boundary rewrite preserves the numeric invariant of
every local under the unchanged state reset map. This is invariant preservation;
semantic equivalence and membership conditions for the unclocked predicate are separate
obligations. -/
theorem replace_boundary_numeric (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c d : Clock) (b ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var)
    (hp : Local.predicate (.bounded c d b (¬ₘ ℓ) kind I φ) ∈ S.locals)
    (hS : S.EvaluatedNumeric σ P α k) :
    (S.replacePredicatePair (.bounded c d b (¬ₘ ℓ) kind I φ)
      (.plain (timedFormula kind I φ)) (.upper c b kind I φ)).EvaluatedNumeric σ P α k := by
  intro l hl
  rcases hl with ⟨hl,_⟩ | hl
  · exact hS l hl
  · have he : l = .predicate (.upper c b kind I φ) := hl
    subst l
    intro hk
    exact numeric_bounded_to_upper _ (S.resets.apply α) c d b (¬ₘ ℓ) kind I φ
      (P.nonempty _) (hS (.predicate _) hp hk)

/-- The same actual boundary rewrite retains full invariants, including every
eventuality clause for no past satisfaction, inside the state's original reset scope. -/
theorem replace_boundary_invariant (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c d : Clock) (b ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var)
    (hp : Local.predicate (.bounded c d b (¬ₘ ℓ) kind I φ) ∈ S.locals)
    (hS : S.EvaluatedInvariant σ P α k) :
    (S.replacePredicatePair (.bounded c d b (¬ₘ ℓ) kind I φ)
      (.plain (timedFormula kind I φ)) (.upper c b kind I φ)).EvaluatedInvariant σ P α k := by
  apply Section3.StateForm.replacePredicatePair_invariant S _ _ _ σ P α k hS
  intro hk
  exact invariant_bounded_to_upper σ P (S.resets.apply α) k hk c d b (¬ₘ ℓ) kind I φ
    (hS (.predicate _) hp hk)

end STLTableau.Section4.Finiteness.BoundaryInvariant
