import STLTableaux.Finiteness.Derivation.Merging.EndpointExclusivityCore
import STLTableaux.Rules.Merging.ConnectedGeneratorMerge

namespace STLTableau.DirectTracking.AlwaysCheckingMergeExclusive
open Section3 Section4.Finiteness
variable {Clock Var : Type*}

/-- Distinct exclusive source predicates cannot share the retained endpoints. -/
theorem retained_endpoints_ne (S : Section3.StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hS : ExclusiveState S)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ) ∈ S.locals)
    (hq : Local.predicate (.bounded c₂ d₂ b₂ q₂ .always (.bounded I) φ) ∈ S.locals)
    (hne : (Predicate.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ) ≠
      .bounded c₂ d₂ b₂ q₂ .always (.bounded I) φ) : c₁ ≠ d₂ := by
  exact hS.endpoints_ne hp hq hne (by simp [endpointClocks]) (by simp [endpointClocks])

private theorem replace_exclusive (S : Section3.StateForm Clock Var) (p q r : Predicate Clock Var)
    (hS : ExclusiveState S)
    (hp : Local.predicate p ∈ S.locals) (hq : Local.predicate q ∈ S.locals)
    (hr : endpointClocks r ⊆ endpointClocks p ∪ endpointClocks q) :
    ExclusiveState (S.replacePredicatePair p q r) := by
  have old_new : ∀ a, Local.predicate a ∈ S.locals →
      Local.predicate a ∉ ({Local.predicate p, Local.predicate q} : Set (Local Clock Var)) →
      Disjoint (endpointClocks a) (endpointClocks r) := by
    intro a ha hnot
    have hap : a ≠ p := by intro he; subst a; exact hnot (Or.inl rfl)
    have haq : a ≠ q := by intro he; subst a; exact hnot (Or.inr rfl)
    apply Set.disjoint_left.mpr
    intro c hca hcr
    rcases hr hcr with hcp | hcq
    · exact Set.disjoint_left.mp (hS a ha p hp hap) hca hcp
    · exact Set.disjoint_left.mp (hS a ha q hq haq) hca hcq
  intro a ha b hb hab
  rcases ha with ⟨ha, hna⟩ | ha <;> rcases hb with ⟨hb, hnb⟩ | hb
  · exact hS a ha b hb hab
  · have he : b = r := Local.predicate.inj hb
    subst b
    exact old_new a ha hna
  · have he : a = r := Local.predicate.inj ha
    subst a
    exact (old_new b hb hnb).symm
  · exact (hab ((Local.predicate.inj ha).trans (Local.predicate.inj hb).symm)).elim

/-- The merged predicate only uses endpoints from the two removed sources. -/
theorem merge_exclusive (S : Section3.StateForm Clock Var)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hS : ExclusiveState S)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ) ∈ S.locals)
    (hq : Local.predicate (.bounded c₂ d₂ b₂ q₂ .always (.bounded I) φ) ∈ S.locals) :
    ExclusiveState (S.replacePredicatePair
      (.bounded c₁ d₁ b₁ q₁ .always (.bounded I) φ)
      (.bounded c₂ d₂ b₂ q₂ .always (.bounded I) φ)
      (.bounded c₁ d₂ b₁ q₂ .always (.bounded I) φ)) := by
  apply replace_exclusive S _ _ _ hS hp hq
  intro c hc
  simp only [endpointClocks, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact Or.inl (by simp [endpointClocks])
  · exact Or.inr (by simp [endpointClocks])

#print axioms retained_endpoints_ne
#print axioms merge_exclusive
end STLTableau.DirectTracking.AlwaysCheckingMergeExclusive
