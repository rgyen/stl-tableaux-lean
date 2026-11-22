import STLTableaux.Rules.Merging.ConnectedGeneratorMerge
import STLTableaux.Semantics.Invariants.EvaluatedInvariant

/-! Full invariant preservation for connected generator merges. Conditions for no past
satisfaction are retained literally at the surviving left endpoint; they are
neither dropped nor replaced by numeric-only invariants. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}

private theorem right_bound_weaken (x y z : ℝ) (b q₁ q₂ : Marker)
    (hr : x <[Marker.imp q₁ q₂] y) (hy : y <[Marker.conj b q₁] z) :
    x <[Marker.conj b q₂] z := by
  rcases hr with hr | ⟨he,hm⟩
  · exact Or.inl (by rcases hy with hy | ⟨hy,_⟩ <;> linarith)
  · rcases hy with hy | ⟨hy,hby⟩
    · exact Or.inl (by linarith)
    · refine Or.inr ⟨he.trans hy,?_⟩
      obtain ⟨hb,hq⟩ := (Marker.includes_conj _ _).1 hby
      exact (Marker.includes_conj _ _).2 ⟨hb,(Marker.includes_imp _ _).1 hm hq⟩

private theorem upper_nonempty_of_bounded (J : MarkedInterval) (c d : NNReal)
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

namespace Predicate

/-- The merged `↑↓` predicate keeps the first predicate's complete
invariant; the marker-aware right-endpoint condition only weakens its bound. -/
theorem invariant_merge_bounded_connected
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c₁ d₁ d₂ : Clock) (b₁ q₁ q₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hright : (α d₂ : ℝ) <[Marker.imp q₁ q₂] (α d₁ : ℝ))
    (h : Invariant σ P α k hk (.bounded c₁ d₁ b₁ q₁ kind I φ)) :
    Invariant σ P α k hk (.bounded c₁ d₂ b₁ q₂ kind I φ) := by
  cases I with
  | bounded I =>
      cases kind with
      | always => exact ⟨h.1,right_bound_weaken _ _ _ _ _ _ hright h.2⟩
      | eventually => exact ⟨h.1,right_bound_weaken _ _ _ _ _ _ hright h.2.1,h.2.2⟩
  | unbounded a =>
      cases kind with
      | always => exact h
      | eventually => exact ⟨right_bound_weaken _ _ _ _ _ _ hright h.1,h.2⟩

/-- Merging the `↑↓` and `↑` predicates keeps the original left
endpoint's full condition for no past satisfaction. Current-piece nonemptiness supplies
the new `↑` predicate's nonempty-scope conjunct. -/
theorem invariant_merge_upper_connected
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (h : Invariant σ P α k hk (.bounded c d b q kind I φ)) :
    Invariant σ P α k hk (.upper c b kind I φ) := by
  cases I with
  | bounded I =>
      cases kind with
      | always => exact h.1
      | eventually =>
          refine ⟨h.1,?_,h.2.2⟩
          simpa only [add_sub_assoc] using
            (upper_nonempty_of_bounded (P.interval ⟨k.1,hk⟩) (α c) (α d)
              b q (P.nonempty _) h.2.1)
  | unbounded a =>
      cases kind with
      | always => exact h
      | eventually =>
          exact ⟨upper_nonempty_of_bounded (P.interval ⟨k.1,hk⟩) (α c) (α d)
            b q (P.nonempty _) h.1,h.2⟩
end Predicate

namespace StateForm

theorem replacePredicatePair_invariant (S : StateForm Clock Var) (p q r : Predicate Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hS : S.EvaluatedInvariant σ P α k)
    (hr : (Local.predicate r).EvaluatedInvariant σ P (S.resets.apply α) k) :
    (S.replacePredicatePair p q r).EvaluatedInvariant σ P α k := by
  intro l hl
  rcases hl with ⟨hl,_⟩ | hl
  · exact hS l hl
  · have heq : l = .predicate r := hl
    subst l
    exact hr

/-- Full invariant preservation of the actual two-bounded generator rewrite.
The semantic equivalence has additional left/join premises; invariant
preservation itself requires only the surviving right-endpoint comparison. -/
theorem merge_connected_bounded_pair_invariant (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hright : (S.resets.apply α d₂ : ℝ) <[Marker.imp q₁ q₂] (S.resets.apply α d₁ : ℝ))
    (hS : S.EvaluatedInvariant σ P α k) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.bounded c₂ d₂ b₂ q₂ kind I φ) (.bounded c₁ d₂ b₁ q₂ kind I φ)).EvaluatedInvariant σ P α k := by
  apply replacePredicatePair_invariant S _ _ _ σ P α k hS
  intro hk
  exact Predicate.invariant_merge_bounded_connected σ P (S.resets.apply α) k hk
    c₁ d₁ d₂ b₁ q₁ q₂ kind I φ hright (hS (.predicate _) hp hk)

theorem merge_connected_upper_pair_invariant (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hS : S.EvaluatedInvariant σ P α k) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.upper c₂ b₂ kind I φ) (.upper c₁ b₁ kind I φ)).EvaluatedInvariant σ P α k := by
  apply replacePredicatePair_invariant S _ _ _ σ P α k hS
  intro hk
  exact Predicate.invariant_merge_upper_connected σ P (S.resets.apply α) k hk
    c₁ d₁ b₁ q₁ kind I φ (hS (.predicate _) hp hk)

end StateForm
end STLTableau.Section3
