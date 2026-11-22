import STLTableaux.ModelChecking.Preprocessing.Admissibility

namespace STLTableau.CurrentAudit
open scoped STL

/-- Semantic simplification is valid for every signal and time. -/
theorem triple_neg_truth_iff_false {Var : Type*} (σ : FiniteSignal Var)
    (t : σ.Time) :
    σ.Satisfies (.neg (.neg (.neg .truth))) t ↔
      σ.Satisfies Formula.falsity t := by
  simp [FiniteSignal.Satisfies, Formula.falsity]

/-- Formula constructors retain syntax; they do not normalize negations. -/
theorem triple_neg_truth_syntax_ne_false {Var : Type*} :
    (Formula.neg (.neg (.neg .truth)) : Formula Var) ≠ Formula.falsity := by
  simp [Formula.falsity]

/-- The new input boundary converts this raw syntax to atomic falsity. -/
theorem normalized_triple_truth_atomic :
    (IntervalPredicate.plain
      ((Formula.neg (.neg (.neg .truth)) : Formula Unit).normalizeNegation false) :
      IntervalPredicate Nat Unit).IsAtomic := by
  exact IntervalPredicate.atomic_plain_falsity

/-- Arbitrary negation of a supported Boolean expression is accepted. -/
theorem negated_conjunction_prepares (a : AtomicProposition Unit) :
    ∃ input, (Formula.neg (.and (.atom a) .truth)).prepare? = some input := by
  apply (Formula.prepare?_exists_iff _).2
  exact (Formula.TableauReady.and (.atom a) .truth).normalizeNegation true

/-- Shifted unbounded until is rejected, rather than using the false rewrite. -/
theorem shifted_until_not_prepared :
    (Formula.until (.unbounded 2) .truth .truth : Formula Unit).prepare? = none := by
  classical
  have hn : ¬ (Formula.until (.unbounded 2) .truth .truth : Formula Unit).TableauReady := by
    intro h
    generalize he : (Formula.until (.unbounded 2) .truth .truth : Formula Unit) = φ at h
    cases h <;> simp [Formula.falsity, Formula.or, Formula.untimedUntil,
      Formula.release, Formula.eventually, Formula.always] at he
  simp [Formula.prepare?, Formula.normalizeNegation, hn]

/-- The unbounded-until elimination fails when a exceeds the horizon. -/
def shortSignal : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩
def initialTime : shortSignal.Time := ⟨0, by constructor <;> norm_num [shortSignal]⟩
def zeroTwo : BoundedTimeInterval := ⟨0, 2, by norm_num, by norm_num⟩

theorem delayed_until_false :
    ¬ shortSignal.Satisfies
      (.until (.unbounded 2) .truth .truth) initialTime := by
  rintro ⟨u, hu, _, _⟩
  have hdelay : (2 : ℝ) ≤ u.1 - 0 := hu
  have hend : u.1 < 1 := u.2.2
  linarith

theorem proposed_until_rewrite_true :
    shortSignal.Satisfies
      (Formula.always zeroTwo (Formula.untimedUntil .truth .truth)) initialTime := by
  apply (FiniteSignal.satisfies_always_iff _ _ _ _).2
  intro u _
  exact FiniteSignal.satisfies_untimedUntil_of_and _ _ _ u trivial trivial

/-- Without an admissibility boundary, no-rule does not mean atomic. -/
def unsupported : IntervalPredicate Nat Unit := .plain (.neg (.neg (.neg .truth)))

theorem unsupported_not_atomic : ¬ unsupported.IsAtomic := by
  simp [unsupported, IntervalPredicate.IsAtomic]

theorem unsupported_no_rule (R : ExpansionRule Nat Unit) :
    ¬ ConcreteRule unsupported R := by
  intro h
  cases h

def unsupportedForm : TransitionForm Nat Unit :=
  TransitionForm.ofState (StateForm.ofLocal (.predicate unsupported) trivial)

theorem unsupported_closed (A : BranchTransitionForms Nat Unit) :
    A.expansionRules.IsClosed unsupportedForm := by
  intro p hp
  have heq : p = unsupported := by
    simpa [unsupportedForm, TransitionForm.ofState, StateForm.ofLocal] using hp
  subst p
  refine ⟨hp, Or.inl ?_⟩
  rintro ⟨R, hR⟩
  exact unsupported_no_rule R hR

theorem unsupported_is_own_closure (A : BranchTransitionForms Nat Unit) :
    A.expansionRules.IsClosure unsupportedForm unsupportedForm := by
  refine ⟨syntacticallySubsumed_refl ∅ unsupportedForm (by simp),
    unsupported_closed A, ?_⟩
  intro Θ h _ _
  exact h

theorem unsupported_complexity_zero : unsupported.complexity = 0 := rfl

theorem unsupported_invariant (J : MarkedInterval) (α : ClockValuation Nat) :
    IntervalPredicate.Invariant J α unsupported := trivial

theorem unsupportedForm_unsatisfied (σ : FiniteSignal Unit)
    (P : IntervalPartition σ.domain) (α : ClockValuation Nat)
    (k : Judgement.Position P) (hk : k.1 < P.size) :
    ¬ unsupportedForm.Satisfies σ P α k := by
  intro h
  have hp : Judgement.Satisfies σ P α k (.predicate unsupported) := by
    simpa only [unsupportedForm, TransitionForm.satisfies_ofState,
      StateForm.satisfies_ofLocal] using h
  simp only [Judgement.Satisfies, dif_pos hk, unsupported,
    IntervalPredicate.Satisfies] at hp
  obtain ⟨t, ht⟩ := P.nonempty ⟨k.1, hk⟩
  have htd : t ∈ σ.domain := by
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨⟨k.1, hk⟩, ht⟩
  have hfalse := hp ⟨t, htd⟩ ht
  simp [FiniteSignal.Satisfies] at hfalse

#print axioms delayed_until_false
#print axioms triple_neg_truth_iff_false
#print axioms triple_neg_truth_syntax_ne_false
#print axioms proposed_until_rewrite_true
#print axioms unsupported_closed
#print axioms unsupported_is_own_closure
#print axioms unsupportedForm_unsatisfied
#print axioms Formula.satisfies_normalizeNegation
#print axioms Formula.prepare?_sound
#print axioms ConcreteRule.branch_tableauReady
#print axioms BranchTransitionForms.not_hasRule_iff_atomic
#print axioms Formula.TableauInput.closure_nonatomic_has_branch
#print axioms shifted_until_not_prepared
end STLTableau.CurrentAudit
