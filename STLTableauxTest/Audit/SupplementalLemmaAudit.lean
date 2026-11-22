import STLTableaux

namespace STLTableau.SupplementalLemmaChecks
open scoped STL

theorem falsity_has_no_rule (R : ExpansionRule Nat Unit) :
    ¬ ConcreteRule (.plain Formula.falsity) R := by
  intro h
  cases h

theorem falsity_is_atomic :
    (IntervalPredicate.plain (Formula.falsity : Formula Unit) :
      IntervalPredicate Nat Unit).IsAtomic := IntervalPredicate.atomic_plain_falsity

theorem falsity_complexity_zero :
    (IntervalPredicate.plain (Formula.falsity : Formula Unit) :
      IntervalPredicate Nat Unit).complexity = 0 := rfl

def falseForm : TransitionForm Nat Unit :=
  TransitionForm.ofState (StateForm.ofLocal
    (.predicate (.plain Formula.falsity)) trivial)

theorem falseForm_closed (A : BranchTransitionForms Nat Unit) :
    A.expansionRules.IsClosed falseForm := by
  intro p hp
  have heq : p = .plain Formula.falsity := by
    simpa [falseForm, TransitionForm.ofState, StateForm.ofLocal] using hp
  subst p
  refine ⟨hp, Or.inl ?_⟩
  rintro ⟨R, hR⟩
  exact falsity_has_no_rule R hR

theorem falseForm_is_own_closure (A : BranchTransitionForms Nat Unit) :
    A.expansionRules.IsClosure falseForm falseForm := by
  refine ⟨?_, falseForm_closed A, ?_⟩
  · exact syntacticallySubsumed_refl ∅ falseForm (by simp)
  · intro Θ h _ _
    exact h

theorem falseForm_unsatisfied (σ : FiniteSignal Unit)
    (P : IntervalPartition σ.domain) (α : ClockValuation Nat)
    (k : Judgement.Position P) (hk : k.1 < P.size) :
    ¬ falseForm.Satisfies σ P α k := by
  intro h
  have hp : Judgement.Satisfies σ P α k (.predicate (.plain Formula.falsity)) := by
    simpa only [falseForm, TransitionForm.satisfies_ofState,
      StateForm.satisfies_ofLocal] using h
  simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at hp
  obtain ⟨t, ht⟩ := P.nonempty ⟨k.1, hk⟩
  have htd : t ∈ σ.domain := by
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨⟨k.1, hk⟩, ht⟩
  exact FiniteSignal.not_satisfies_falsity σ ⟨t, htd⟩ (hp ⟨t, htd⟩ ht)


theorem same_clock_bounded_has_no_rule
    (c : Nat) (m q : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Unit) (R : ExpansionRule Nat Unit) :
    ¬ ConcreteRule (.bounded c c m q kind I φ) R := by
  intro h
  cases h <;> simp_all

/-- Ignoring all predicates also ignores atomic falsity. This is not the
non-atomic erasure used by closure soundness, which retains falsity. -/
theorem falseForm_nonPredicate_satisfied (σ : FiniteSignal Unit)
    (P : IntervalPartition σ.domain) (α : ClockValuation Nat)
    (k : Judgement.Position P) :
    falseForm.NonPredicateSatisfies σ P α k := by
  simp [falseForm, TransitionForm.ofState, StateForm.ofLocal,
    TransitionForm.NonPredicateSatisfies, Judgement.NonPredicateSatisfies]

#print axioms same_clock_bounded_has_no_rule
#print axioms falseForm_nonPredicate_satisfied
#print axioms falsity_has_no_rule
#print axioms falseForm_is_own_closure
#print axioms falseForm_unsatisfied
#print axioms ConcreteRule.branch_normalization_properties
#print axioms ConcreteRule.branch_representation_exists
#print axioms ConcreteRule.branch_normalization_in_context
#print axioms BranchTransitionForms.concrete_closure_preservesInvariantAt
end STLTableau.SupplementalLemmaChecks
