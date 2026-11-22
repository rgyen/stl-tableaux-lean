import STLTableaux.Closure.Correctness.ConcreteClosure
import STLTableaux.Closure.Counterexamples.Section4Counterexamples

/-! A counterexample to the existence of a satisfied rule-closed extension
for a generator unrelated to the formula used for partition stability. -/
namespace STLTableau.Section4Counterexamples
open scoped STL
open Section3

def normalizedSource : Section3.Predicate Nat Unit :=
  .plain (Formula.or atom otherAtom)

private theorem branch_for_source_not_satisfied
    (Λ : ClockResetSet Nat) (B : Section3.TransitionForm Nat Unit)
    (hB : ConcreteFinite.Branch normalizedSource Λ B) :
    ¬ B.holds signal partition clocks position := by
  obtain ⟨p, R, Ψ, F, hp, hr, hΨ, hF, rfl⟩ := hB
  cases p with
  | upper c b kind I φ => cases hp
  | bounded c d b q kind I φ => cases hp
  | plain φ =>
      have hφ : φ = Formula.or atom otherAtom := by
        simpa only [normalizedSource, Predicate.ofFinite, Predicate.plain.injEq] using hp.symm
      subst φ
      cases hr
      intro hs
      obtain ⟨G, hG, he⟩ := ConcreteFinite.branch_normalization
        (STLTableau.ConcreteRule.plainOr atom otherAtom) hΨ Λ
      have hFG : F = G := Option.some.inj (hF.symm.trans hG)
      subst G
      have hraw := (he signal partition clocks position).1 hs
      simp only [ExpansionRule.plainOr, List.mem_cons, List.not_mem_nil, or_false] at hΨ
      rcases hΨ with rfl | rfl
      · exact positive_branch_not_satisfied hraw
      · exact other_branch_not_satisfied hraw

/-- Any concrete rule-closed form containing this normalized generator
is unsatisfied, even with arbitrary guards, reset sets and next obligations. -/
theorem no_satisfied_rule_closed_form (Φ : Section3.TransitionForm Nat Unit)
    (hmem : Section3.Local.predicate normalizedSource ∈ Φ.current.locals)
    (hc : ConcreteFinite.catalogue.IsClosed Φ) :
    ¬ Φ.holds signal partition clocks position := by
  intro hs
  have hclosed := hc normalizedSource hmem
  have hadmit : ConcreteFinite.Admitted normalizedSource :=
    Or.inr ⟨.plain (Formula.or atom otherAtom), ExpansionRule.plainOr atom otherAtom,
      rfl, STLTableau.ConcreteRule.plainOr atom otherAtom⟩
  have hna : ¬ normalizedSource.IsAtomic := by
    simp [normalizedSource, Predicate.IsAtomic, Formula.or]
  obtain ⟨B, hB⟩ := ConcreteFinite.catalogue.branch_exists normalizedSource hadmit hna Φ.current.resets
  rcases hclosed with hno | ⟨C, hC, hsub⟩
  · exact hno ⟨B, hB⟩
  · exact branch_for_source_not_satisfied Φ.current.resets C hC
      (hsub.sound signal partition clocks position hs)

def normalizedGenerator : Section3.TransitionForm Nat Unit :=
  Section3.TransitionForm.ofState (Section3.StateForm.ofLocal (.predicate normalizedSource))

theorem normalizedGenerator_holds : normalizedGenerator.holds signal partition clocks position := by
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · intro g hg
    cases hg
  · intro l hl
    have he : l = Local.predicate normalizedSource := Set.mem_singleton_iff.mp hl
    subst l
    exact normalized_generator_satisfied

theorem normalizedGenerator_invariant :
    ∀ p, Local.predicate p ∈ normalizedGenerator.current.locals →
      ∀ hk : position.1 < partition.size,
        p.Invariant signal partition (normalizedGenerator.current.resets.apply clocks) position hk := by
  intro p hp hk
  have he : p = normalizedSource := Local.predicate.inj (Set.mem_singleton_iff.mp hp)
  subst p
  trivial

/-- Therefore the fully stable unrelated root and supported, satisfied
generator have no satisfied closed extension in the actual finite catalogue. -/
theorem no_satisfied_closed_extension (Φ : Section3.TransitionForm Nat Unit)
    (hext : Section3.SyntacticallySubsumed normalizedGenerator Φ)
    (hc : ConcreteFinite.catalogue.IsClosed Φ) :
    ¬ Φ.holds signal partition clocks position := by
  apply no_satisfied_rule_closed_form Φ ?_ hc
  apply hext.current.locals
  exact Set.mem_singleton _

theorem normalized_generator_has_no_satisfied_closed_extension :
    ¬ ∃ Φ : Section3.TransitionForm Nat Unit,
      Section3.SyntacticallySubsumed normalizedGenerator Φ ∧
      ConcreteFinite.catalogue.IsClosed Φ ∧ Φ.holds signal partition clocks position := by
  rintro ⟨Φ, hext, hc, hs⟩
  exact no_satisfied_closed_extension Φ hext hc hs

/-- All the arbitrary-generator lemma's input premises hold, while even
its necessary satisfied closed-extension conclusion fails. Stability is
for the unrelated root `true`; the generator itself is admitted syntax. -/
theorem normalized_generator_closed_extension_counterexample :
    signal.StablePartition (.truth : Formula Unit) partition ∧
    (Formula.or atom otherAtom).TableauReady ∧
    normalizedGenerator.holds signal partition clocks position ∧
    (∀ p, Local.predicate p ∈ normalizedGenerator.current.locals →
      ∀ hk : position.1 < partition.size,
        p.Invariant signal partition (normalizedGenerator.current.resets.apply clocks) position hk) ∧
    (∀ Φ : Section3.TransitionForm Nat Unit,
      Section3.SyntacticallySubsumed normalizedGenerator Φ →
      ConcreteFinite.catalogue.IsClosed Φ → ¬ Φ.holds signal partition clocks position) :=
  ⟨root_truth_fully_stable, normalized_generator_ready, normalizedGenerator_holds,
    normalizedGenerator_invariant, no_satisfied_closed_extension⟩

/-- The same obstruction with a primitive root using the same variable as
the normalized generator, so no extension of the variable universe is used. -/
theorem same_variable_generator_closed_extension_counterexample :
    signal.StablePartition rootSameVariable partition ∧
    (Formula.or atom otherAtom).TableauReady ∧
    normalizedGenerator.holds signal partition clocks position ∧
    (∀ p, Local.predicate p ∈ normalizedGenerator.current.locals →
      ∀ hk : position.1 < partition.size,
        p.Invariant signal partition (normalizedGenerator.current.resets.apply clocks) position hk) ∧
    (∀ Φ : Section3.TransitionForm Nat Unit,
      Section3.SyntacticallySubsumed normalizedGenerator Φ →
      ConcreteFinite.catalogue.IsClosed Φ → ¬ Φ.holds signal partition clocks position) :=
  ⟨rootSameVariable_fully_stable, normalized_generator_closed_extension_counterexample.2⟩

end STLTableau.Section4Counterexamples
