import STLTableaux.Rules.Merging.ConnectedMergeInvariant

/-! Predicate invariant preservation for a merge of two predicates in the
`↑↓` form for `□[I] φ` with bounded `I`. The proof uses the first
predicate's invariant and the right endpoint comparison. -/
namespace STLTableau.DirectTracking.AlwaysCheckingMergeInvariant
open scoped STL
variable {Clock Var : Type*}

/-- Only the first source invariant and the marker-aware right comparison
are needed for invariant preservation. -/
theorem invariant_merge
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c₁ d₁ d₂ : Clock) (b₁ q₁ q₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hright : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ))
    (hfirst : STLTableau.Invariant σ P α k hk
      (.bounded c₁ d₁ b₁ q₁ .always I φ)) :
    STLTableau.Invariant σ P α k hk (.bounded c₁ d₂ b₁ q₂ .always I φ) := by
  exact Section3.Predicate.invariant_merge_bounded_connected
    σ P α k hk c₁ d₁ d₂ b₁ q₁ q₂ .always (.bounded I) φ hright hfirst

/-- The concrete state rewrite evaluates the right comparison after all
state resets, exactly as its source and result invariants are evaluated. -/
theorem state_invariant_merge
    (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hfirst : Section3.Local.predicate
      (.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ) ∈ S.locals)
    (hright : (S.resets.apply α d₂ : ℝ) <[Marker.imp q₁ q₂]
      (S.resets.apply α d₁ : ℝ))
    (hS : S.EvaluatedInvariant σ P α k) :
    (S.replacePredicatePair
      (.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ)
      (.bounded c₂ d₂ b₂ q₂ .always (.bounded I) φ)
      (.bounded c₁ d₂ b₁ q₂ .always (.bounded I) φ)).EvaluatedInvariant σ P α k := by
  exact Section3.StateForm.merge_connected_bounded_pair_invariant
    S σ P α k c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂ .always (.bounded I) φ hfirst hright hS

#print axioms invariant_merge
#print axioms state_invariant_merge

end STLTableau.DirectTracking.AlwaysCheckingMergeInvariant
