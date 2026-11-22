import STLTableaux.Rules.Merging.ConnectedMergeInvariant
import STLTableaux.Closure.Normalization.NormalizedStability
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Formula stability and normalized syntax through actual connected generator
rewrites. Bound-clock distinctness is explicit when a bounded result is formed. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace StateForm

/-- Replacing a selected family by a formula already in the source introduces
no new underlying formula. Endpoint names and markers may change. -/
theorem replacePredicates_underlyingFormulas_subset (S : StateForm Clock Var)
    (ps : List (Predicate Clock Var)) (r p : Predicate Clock Var)
    (hp : Local.predicate p ∈ S.locals) (he : r.formula = p.formula) :
    (S.replacePredicates ps r).underlyingFormulas ⊆ S.underlyingFormulas := by
  rintro φ ⟨q,hq,hφ⟩
  rcases hq with ⟨hq,_⟩ | hq
  · exact ⟨q,hq,hφ⟩
  · have hqr : q = r := Local.predicate.inj hq
    subst q
    exact ⟨p,hp,hφ.trans he⟩

theorem replacePredicatePair_underlyingFormulas_subset (S : StateForm Clock Var)
    (p q r : Predicate Clock Var) (hp : Local.predicate p ∈ S.locals)
    (he : r.formula = p.formula) :
    (S.replacePredicatePair p q r).underlyingFormulas ⊆ S.underlyingFormulas := by
  rintro φ ⟨u,hu,hφ⟩
  rcases hu with ⟨hu,_⟩ | hu
  · exact ⟨u,hu,hφ⟩
  · have hur : u = r := Local.predicate.inj hu
    subst u
    exact ⟨p,hp,hφ.trans he⟩

theorem merge_connected_pair_stable (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hS : S.UnderlyingStable σ P) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.upper c₂ b₂ kind I φ) (.upper c₁ b₁ kind I φ)).UnderlyingStable σ P := by
  intro ψ hψ
  exact hS ψ (replacePredicatePair_underlyingFormulas_subset S _ _ _ hp
    (by cases kind <;> rfl) hψ)

theorem merge_connected_bounded_pair_stable (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hS : S.UnderlyingStable σ P) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.bounded c₂ d₂ b₂ q₂ kind I φ)
      (.bounded c₁ d₂ b₁ q₂ kind I φ)).UnderlyingStable σ P := by
  intro ψ hψ
  exact hS ψ (replacePredicatePair_underlyingFormulas_subset S _ _ _ hp
    (by cases kind <;> rfl) hψ)

theorem merge_connected_prefix_stable (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (lastClock c : Clock) (lastMarker b : Marker) (ps : List (Predicate Clock Var))
    (hp : Local.predicate (.upper lastClock lastMarker kind I φ) ∈ S.locals)
    (hS : S.UnderlyingStable σ P) :
    (S.replacePredicates (ps ++ [.upper lastClock lastMarker kind I φ])
      (.upper c b kind I φ)).UnderlyingStable σ P := by
  intro ψ hψ
  exact hS ψ (replacePredicates_underlyingFormulas_subset S _ _ _ hp
    (by cases kind <;> rfl) hψ)

private theorem replacePredicatePair_ready (S : StateForm Clock Var)
    (p q r : Predicate Clock Var) (hS : S.Ready) (hr : r.Ready) :
    (S.replacePredicatePair p q r).Ready := by
  intro l hl
  rcases hl with ⟨hl,_⟩ | hl
  · exact hS l hl
  · have he : l = Local.predicate r := hl
    subst l
    exact hr

private theorem replacePredicates_ready (S : StateForm Clock Var)
    (ps : List (Predicate Clock Var)) (r : Predicate Clock Var)
    (hS : S.Ready) (hr : r.Ready) : (S.replacePredicates ps r).Ready := by
  intro l hl
  rcases hl with ⟨hl,_⟩ | hl
  · exact hS l hl
  · have he : l = Local.predicate r := hl
    subst l
    exact hr

theorem merge_connected_pair_ready (S : StateForm Clock Var)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hS : S.Ready) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.upper c₂ b₂ kind I φ) (.upper c₁ b₁ kind I φ)).Ready := by
  exact replacePredicatePair_ready S _ _ _ hS (hS _ hp).2

/-- Freshness of the retained endpoints is a syntactic condition, independent
of the semantic connectedness comparisons. -/
theorem merge_connected_bounded_pair_ready (S : StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hdistinct : c₁ ≠ d₂) (hS : S.Ready) :
    (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
      (.bounded c₂ d₂ b₂ q₂ kind I φ)
      (.bounded c₁ d₂ b₁ q₂ kind I φ)).Ready := by
  exact replacePredicatePair_ready S _ _ _ hS ⟨hdistinct,(hS _ hp).2⟩

theorem merge_connected_prefix_ready (S : StateForm Clock Var)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (lastClock c : Clock) (lastMarker b : Marker) (ps : List (Predicate Clock Var))
    (hp : Local.predicate (.upper lastClock lastMarker kind I φ) ∈ S.locals)
    (hS : S.Ready) :
    (S.replacePredicates (ps ++ [.upper lastClock lastMarker kind I φ])
      (.upper c b kind I φ)).Ready := by
  exact replacePredicates_ready S _ _ hS (hS _ hp)

/-- Full invariant preservation for the actual whole-prefix replacement. -/
theorem merge_connected_prefix_invariant (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (lastClock c : Clock) (lastMarker b : Marker) (ps : List (Predicate Clock Var))
    (hprefix : ConnectedPrefix (S.resets.apply α) kind I φ lastClock lastMarker ps c b)
    (hp : ∀ p ∈ ps ++ [.upper lastClock lastMarker kind I φ],
      Local.predicate p ∈ S.locals)
    (hS : S.EvaluatedInvariant σ P α k) :
    (S.replacePredicates (ps ++ [.upper lastClock lastMarker kind I φ])
      (.upper c b kind I φ)).EvaluatedInvariant σ P α k := by
  have hr : (Local.predicate (.upper c b kind I φ)).EvaluatedInvariant
      σ P (S.resets.apply α) k := by
    intro hk
    cases hprefix with
    | nil =>
      exact hS _ (hp _ (by simp)) hk
    | @cons ps c₂ b₂ c₁ d₁ b₁ q₁ tail hj hl =>
      exact Predicate.invariant_merge_upper_connected σ P (S.resets.apply α) k hk
        c d₁ b q₁ kind I φ (hS _ (hp _ (by simp)) hk)
  intro l hl
  rcases hl with ⟨hl,_⟩ | hl
  · exact hS l hl
  · have he : l = Local.predicate (.upper c b kind I φ) := hl
    subst l
    exact hr

/-- One actual family rewrite simultaneously preserves truth, full invariant,
and stability. It does not assert that the old graph's edges are unchanged. -/
theorem merge_connected_prefix_preserving (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (lastClock c : Clock) (lastMarker b : Marker) (ps : List (Predicate Clock Var))
    (hprefix : ConnectedPrefix (S.resets.apply α) kind I φ lastClock lastMarker ps c b)
    (hp : ∀ p ∈ ps ++ [.upper lastClock lastMarker kind I φ],
      Local.predicate p ∈ S.locals)
    (hi : S.EvaluatedInvariant σ P α k) (hst : S.UnderlyingStable σ P) :
    let T := S.replacePredicates (ps ++ [.upper lastClock lastMarker kind I φ])
      (.upper c b kind I φ)
    (S.holds σ P α k ↔ T.holds σ P α k) ∧
      T.EvaluatedInvariant σ P α k ∧ T.UnderlyingStable σ P := by
  refine ⟨merge_connected_prefix_holds S σ P α k hk kind I φ
    lastClock c lastMarker b ps hprefix hp, ?_, ?_⟩
  · exact merge_connected_prefix_invariant S σ P α k kind I φ
      lastClock c lastMarker b ps hprefix hp hi
  · exact merge_connected_prefix_stable S σ P kind I φ
      lastClock c lastMarker b ps (hp _ (by simp)) hst

end StateForm
end STLTableau.Section3
