import STLTableaux.Rules.Merging.ConnectedMergeStability
import STLTableaux.Finiteness.Derivation.Merging.AlwaysAgeShape

/-!
Local checking-region merge for bounded G, using the interval semantics.
The join comparison contains I.upper - I.lower; raw source scopes need not join.
No assertion about whole representative paths or a finite tableau is made here.
-/
namespace STLTableau.Section4.Finiteness.DirectTracking

open scoped STL
open STLTableau.IntervalPredicate

variable {Clock Var : Type*}

/-- The actual endpoint-expanded G checking interval, before horizon restriction. -/
def checking (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (l r : Marker) (I : BoundedTimeInterval) : MarkedInterval :=
  ⟨J.left - (α c : ℝ) + I.lower, J.left - (α d : ℝ) + I.upper, l, r⟩

/-- Ordered checking intervals may join even when their original scopes have a gap.
Endpoint implications retain exactly the correct marker on coincident endpoints. -/
theorem checking_union (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker) (I : BoundedTimeInterval)
    (hleft : (α c₂ : ℝ) <[Marker.imp l₂ l₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) - (α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (α d₂ : ℝ) <[Marker.imp r₁ r₂] (α d₁ : ℝ)) :
    (checking J α c₁ d₁ l₁ r₁ I).carrier ∪
        (checking J α c₂ d₂ l₂ r₂ I).carrier =
      (checking J α c₁ d₂ l₁ r₂ I).carrier := by
  apply MarkedInterval.carrier_union_connected
  · rcases hleft with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm⟩
  · rcases hjoin with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_disj _ _).1 hm⟩
  · rcases hright with h | ⟨h, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm⟩

/-- The three marked comparisons identify the merged checking interval with
the union of the two checking intervals. This gives equivalence of the
conjunction with the merged always predicate. -/
theorem bounded_always_merge (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ d₂ : Clock)
    (l₁ r₁ l₂ r₂ : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) <[Marker.imp l₂ l₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) - (α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (α d₂ : ℝ) <[Marker.imp r₁ r₂] (α d₁ : ℝ)) :
    (STLTableau.predicateSatisfies σ J α (.bounded c₁ d₁ l₁ r₁ .always I φ) ∧
      STLTableau.predicateSatisfies σ J α (.bounded c₂ d₂ l₂ r₂ .always I φ)) ↔
      STLTableau.predicateSatisfies σ J α (.bounded c₁ d₂ l₁ r₂ .always I φ) := by
  have hu := checking_union J α c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I hleft hjoin hright
  change ((∀ t : σ.Time, t.1 ∈ (checking J α c₁ d₁ l₁ r₁ I).carrier →
      σ.Satisfies φ t) ∧
    (∀ t : σ.Time, t.1 ∈ (checking J α c₂ d₂ l₂ r₂ I).carrier →
      σ.Satisfies φ t)) ↔
    (∀ t : σ.Time, t.1 ∈ (checking J α c₁ d₂ l₁ r₂ I).carrier →
      σ.Satisfies φ t)
  constructor
  · rintro ⟨h₁, h₂⟩ t ht
    rw [← hu] at ht
    exact ht.elim (h₁ t) (h₂ t)
  · intro h
    constructor
    · intro t ht
      exact h t (hu ▸ Set.mem_union_left _ ht)
    · intro t ht
      exact h t (hu ▸ Set.mem_union_right _ ht)

/-- Mixed judgement API, including the terminal position. -/
theorem bounded_always_merge_at (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c₁ d₁ c₂ d₂ : Clock)
    (l₁ r₁ l₂ r₂ : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) <[Marker.imp l₂ l₁] (α c₁ : ℝ))
    (hjoin : (α d₁ : ℝ) - (α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (α d₂ : ℝ) <[Marker.imp r₁ r₂] (α d₁ : ℝ)) :
    Section3.Judgement.holds σ P α k
      (.conj (.predicate (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ))
        (.predicate (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ))) ↔
    Section3.Judgement.holds σ P α k
      (.predicate (.bounded c₁ d₂ l₁ r₂ .always (.bounded I) φ)) := by
  by_cases hk : k.1 < P.size
  · simpa only [Section3.Judgement.holds, dif_pos hk, Section3.Predicate.holds] using
      bounded_always_merge σ (P.interval ⟨k.1, hk⟩) α c₁ d₁ c₂ d₂
        l₁ r₁ l₂ r₂ I φ hleft hjoin hright
  · simp only [Section3.Judgement.holds, dif_neg hk, and_self]

/-- Reset-aware form: the comparisons must hold at the post-reset valuation.
The theorem does not replace them with conditions at the incoming valuation. -/
theorem bounded_always_merge_under_reset (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (Λ : ClockResetSet Clock)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (Λ.apply α c₂ : ℝ) <[Marker.imp l₂ l₁] (Λ.apply α c₁ : ℝ))
    (hjoin : (Λ.apply α d₁ : ℝ) - (Λ.apply α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (Λ.apply α d₂ : ℝ) <[Marker.imp r₁ r₂] (Λ.apply α d₁ : ℝ)) :
    Section3.Judgement.holds σ P α k
      (.reset Λ (.conj (.predicate (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ))
        (.predicate (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ)))) ↔
    Section3.Judgement.holds σ P α k
      (.reset Λ (.predicate (.bounded c₁ d₂ l₁ r₂ .always (.bounded I) φ))) :=
  bounded_always_merge_at σ P (Λ.apply α) k c₁ d₁ c₂ d₂
    l₁ r₁ l₂ r₂ I φ hleft hjoin hright

/-- The actual ordinary-or-checked age shape survives retention of a later
right endpoint. No semantic representative hypothesis is introduced. -/
theorem merge_preserves_age_shape (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ d₂ : Clock) (l₁ r₁ r₂ : Marker) (a : NNReal)
    (hright : (α d₂ : ℝ) <[Marker.imp r₁ r₂] (α d₁ : ℝ))
    (hshape : AlwaysAgeShape.Holds J α c₁ d₁ l₁ a) :
    AlwaysAgeShape.Holds J α c₁ d₂ l₁ a := by
  have hle : α d₂ ≤ α d₁ := by
    exact_mod_cast hright.elim le_of_lt (fun h => h.1.le)
  rcases hshape with hordinary | hchecked
  · exact Or.inl (hle.trans hordinary)
  · exact Or.inr hchecked

/-- Actual state-form replacement, retaining the existing guards and resets. -/
def mergeState (S : Section3.StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) : Section3.StateForm Clock Var :=
  S.replacePredicatePair (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ)
    (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ)
    (.bounded c₁ d₂ l₁ r₂ .always (.bounded I) φ)

/-- State-form equivalence uses the actual post-reset comparisons. -/
theorem state_merge_holds (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hp : Section3.Local.predicate
      (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ) ∈ S.locals)
    (hq : Section3.Local.predicate
      (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ) ∈ S.locals)
    (hleft : (S.resets.apply α c₂ : ℝ) <[Marker.imp l₂ l₁]
      (S.resets.apply α c₁ : ℝ))
    (hjoin : (S.resets.apply α d₁ : ℝ) - (S.resets.apply α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (S.resets.apply α d₂ : ℝ) <[Marker.imp r₁ r₂]
      (S.resets.apply α d₁ : ℝ)) :
    S.holds σ P α k ↔ (mergeState S c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ).holds σ P α k := by
  apply Section3.StateForm.replacePredicatePair_holds S _ _ _ hp hq σ P α k
  exact bounded_always_merge_at σ P (S.resets.apply α) k c₁ d₁ c₂ d₂
    l₁ r₁ l₂ r₂ I φ hleft hjoin hright

/-- No local endpoint clock is introduced by retaining the outer endpoints. -/
theorem state_merge_localClocks_subset (S : Section3.StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hp : Section3.Local.predicate
      (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ) ∈ S.locals)
    (hq : Section3.Local.predicate
      (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ) ∈ S.locals) :
    (mergeState S c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ).localClocks ⊆ S.localClocks := by
  rintro c ⟨l, hl, hc⟩
  rcases hl with ⟨hl, _⟩ | hl
  · exact ⟨l, hl, hc⟩
  · have he : l = Section3.Local.predicate
        (.bounded c₁ d₂ l₁ r₂ .always (.bounded I) φ) := hl
    subst l
    change c ∈ ({c₁, d₂} : Set Clock) at hc
    rcases hc with hc | hc
    · exact ⟨_, hp, by change c ∈ ({c₁, d₁} : Set Clock); exact Or.inl hc⟩
    · exact ⟨_, hq, by change c ∈ ({c₂, d₂} : Set Clock); exact Or.inr hc⟩

/-- Syntactic readiness needs retained endpoint distinctness explicitly.
It is not a consequence of semantic connectedness. -/
theorem state_merge_ready (S : Section3.StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hp : Section3.Local.predicate
      (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ) ∈ S.locals)
    (hdistinct : c₁ ≠ d₂) (hS : S.Ready) :
    (mergeState S c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ).Ready :=
  Section3.StateForm.merge_connected_bounded_pair_ready S c₁ d₁ c₂ d₂
    l₁ r₁ l₂ r₂ .always (.bounded I) φ hp hdistinct hS

/-- The unchanged formula inventory preserves the given stable partition. -/
theorem state_merge_stable (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hp : Section3.Local.predicate
      (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ) ∈ S.locals)
    (hS : S.UnderlyingStable σ P) :
    (mergeState S c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ).UnderlyingStable σ P :=
  Section3.StateForm.merge_connected_bounded_pair_stable S σ P c₁ d₁ c₂ d₂
    l₁ r₁ l₂ r₂ .always (.bounded I) φ hp hS

/-- Lifting through an unchanged next part is sound because current resets
are unchanged. This is contextual equivalence, not old-closure membership. -/
theorem transition_current_merge_holds (Φ : Section3.TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c₁ d₁ c₂ d₂ : Clock) (l₁ r₁ l₂ r₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hp : Section3.Local.predicate
      (.bounded c₁ d₁ l₁ r₁ .always (.bounded I) φ) ∈ Φ.current.locals)
    (hq : Section3.Local.predicate
      (.bounded c₂ d₂ l₂ r₂ .always (.bounded I) φ) ∈ Φ.current.locals)
    (hleft : (Φ.current.resets.apply α c₂ : ℝ) <[Marker.imp l₂ l₁]
      (Φ.current.resets.apply α c₁ : ℝ))
    (hjoin : (Φ.current.resets.apply α d₁ : ℝ) - (Φ.current.resets.apply α c₂ : ℝ)
      <[Marker.disj r₁ l₂] (I.upper - I.lower))
    (hright : (Φ.current.resets.apply α d₂ : ℝ) <[Marker.imp r₁ r₂]
      (Φ.current.resets.apply α d₁ : ℝ)) :
    Φ.holds σ P α k ↔
      ({ Φ with current := mergeState Φ.current c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ } :
        Section3.TransitionForm Clock Var).holds σ P α k := by
  have hcur := state_merge_holds Φ.current σ P α k c₁ d₁ c₂ d₂
    l₁ r₁ l₂ r₂ I φ hp hq hleft hjoin hright
  exact and_congr hcur Iff.rfl

#print axioms checking_union
#print axioms bounded_always_merge
#print axioms bounded_always_merge_at
#print axioms bounded_always_merge_under_reset
#print axioms merge_preserves_age_shape
#print axioms state_merge_holds
#print axioms state_merge_localClocks_subset
#print axioms state_merge_ready
#print axioms state_merge_stable
#print axioms transition_current_merge_holds

end STLTableau.Section4.Finiteness.DirectTracking
