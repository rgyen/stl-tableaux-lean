import STLTableaux.Tableau.Correctness.GeneratorPathCompleteness
import STLTableaux.Closure.Correctness.FaithfulClosureSoundness
import STLTableaux.Closure.Correctness.NumericFromInvariant
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Tableau soundness (Theorem 4.32). Satisfaction of the trace gives
satisfaction of the initial generator via the full trace. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Generated
variable [DecidableEq Clock]

private theorem current_nonPredicate_of_atomic (s : ClosureState Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : (∀ g ∈ s.form.current.guards, g.holds α) ∧
      ∀ l ∈ labels s, l.holds σ P (s.form.current.resets.apply α) k) :
    s.form.current.nonPredicateHolds σ P α k := by
  refine ⟨h.1,?_⟩
  intro l hl
  cases l with
  | terminal => exact h.2 .terminal ⟨hl,trivial⟩
  | marker m => exact h.2 (.marker m) ⟨hl,trivial⟩
  | predicate p => trivial

/-- A satisfied accepting trace establishes the non-predicate judgements of
its first closure when the first incoming label matches that closure. -/
theorem nonPredicate_of_atomic_trace (X : Set Var) (Xc : Set Clock)
    (initial : Section3.StateForm Clock Var) (p : Path Clock (ClosureState Clock Var))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc initial))
    (he : p.firstIncoming = p.firstState.incoming)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : (p.trace labels labels_finite).holds σ P α k) :
    p.firstState.form.nonPredicateHolds σ P α k := by
  induction p generalizing α k with
  | last e s =>
      change s.form.nonPredicateHolds σ P α k
      change e = s.incoming at he
      subst e
      refine ⟨current_nonPredicate_of_atomic s σ P α k hs,?_⟩
      have hn : s.form.nextPart = none := ha.2
      simp only [hn]
  | step e s t ih =>
      change s.form.nonPredicateHolds σ P α k
      have hedge : s.form.nextPart = some t.firstState.generator ∧
          t.firstIncoming = t.firstState.incoming := ha.1.2.2.2.2
      have htail : t.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) :=
        ⟨ha.1.2.1,ha.2⟩
      change e = s.incoming at he
      subst e
      change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
      refine ⟨current_nonPredicate_of_atomic s σ P α k hs.1,?_⟩
      rw [hedge.1]
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs ⊢
        have ht := ih htail hedge.2 _ _ hs.2
        have hclosure : ConcreteContextual.catalogue.IsClosure
            (Section3.TransitionForm.ofState t.firstState.generator) t.firstState.form :=
          Path.first_mem_of_valid _ t htail.1
        exact (hclosure.extension.nonPredicateHolds σ P _ _ ht).1
      · simpa only [dif_neg hk] using hs.2
/-- The numeric invariant conditions propagate forward along the path.
Backward induction then recovers the full trace and generator satisfaction.
Used in Lemma 4.31 (trace equivalence). -/
theorem fullTrace_and_generator_of_atomic_trace [Nontrivial Clock]
    (X : Set Var) (Xc : Set Clock) (initial : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc initial))
    (he : p.firstIncoming = p.firstState.incoming)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hr : p.firstState.generator.Ready)
    (hi : p.firstState.generator.EvaluatedNumeric σ P α k)
    (hs : (p.trace labels labels_finite).holds σ P α k) :
    p.fullTrace.holds σ P α k ∧ p.firstState.form.holds σ P α k ∧
      p.firstState.generator.holds σ P α k := by
  induction p generalizing α k with
  | last e s =>
      have hnp := nonPredicate_of_atomic_trace X Xc initial (.last e s) ha he σ P α k hs
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1
      have hready := ConcreteContextual.closure_ready hc
        ((Section3.TransitionForm.ready_ofState s.generator).2 hr)
      have hin : (Section3.TransitionForm.ofState s.generator).EvaluatedNumeric σ P α k :=
        ⟨hi,by intro N hn; cases hn⟩
      change e = s.incoming at he
      subst e
      have hat : s.form.atomicProjection.holds σ P α k := by
        refine ⟨hs,?_⟩
        have hn : s.form.nextPart = none := ha.2
        simp only [Section3.TransitionForm.atomicProjection,Section3.TransitionForm.restrictCurrent,hn]
      have hf := ConcreteContextual.minimal_closure_holds_of_atomicProjection hc
        (fun p hp => (hready.1 (.predicate p) hp).admitted) σ P α k hin hat
      exact ⟨hf.1,hf,(hc.extension.sound σ P α k hf).1⟩
  | step e s t ih =>
      have hnp := nonPredicate_of_atomic_trace X Xc initial (.step e s t) ha he σ P α k hs
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1.1
      have hedge : s.form.nextPart = some t.firstState.generator ∧
          t.firstIncoming = t.firstState.incoming := ha.1.2.2.2.2
      have htail : t.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) :=
        ⟨ha.1.2.1,ha.2⟩
      have hready := ConcreteContextual.closure_ready hc
        ((Section3.TransitionForm.ready_ofState s.generator).2 hr)
      have hin : (Section3.TransitionForm.ofState s.generator).EvaluatedNumeric σ P α k :=
        ⟨hi,by intro N hn; cases hn⟩
      have hnumeric := ConcreteContextual.minimal_closure_numeric hc σ P α k hin hnp
      change e = s.incoming at he
      subst e
      change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs
        have ht := ih htail hedge.2 _ _
          (hready.2 t.firstState.generator hedge.1)
          (hnumeric.2 t.firstState.generator hedge.1 hk) hs.2
        have hat : s.form.atomicProjection.holds σ P α k := by
          refine ⟨hs.1,?_⟩
          change match s.form.nextPart with | none => True | some N => _
          rw [hedge.1]
          simpa only [dif_pos hk,Section3.TransitionForm.atomicProjection,Section3.TransitionForm.restrictCurrent] using ht.2.2
        have hf := ConcreteContextual.minimal_closure_holds_of_atomicProjection hc
          (fun p hp => (hready.1 (.predicate p) hp).admitted) σ P α k hin hat
        refine ⟨?_,hf,(hc.extension.sound σ P α k hf).1⟩
        change s.form.current.holds σ P α k ∧ (if h : k.1 < P.size then _ else False)
        exact ⟨hf.1,by simpa only [dif_pos hk,Trace.holds,Path.fullTrace,ClosureState.incoming] using ht.1⟩
      · simp only [dif_neg hk] at hs
        exact hs.2.elim

/-- Theorem 4.32 (tableau soundness). Recognition by the tableau for a
normalized formula implies satisfaction at time zero. -/
theorem formula_of_recognizes [Nontrivial Clock]
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))).recognizes labels_finite σ P) :
    σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  obtain ⟨p,hr,ha,htrace⟩ := hs
  have hinit : p.firstState.generator = Section3.StateForm.ofLocal (.predicate (.plain φ)) :=
    hr.2.2.1
  have he : p.firstIncoming = p.firstState.incoming := hr.2.2.2
  let α : ClockValuation Clock := fun _ => 0
  have hready : p.firstState.generator.Ready := by
    rw [hinit]
    exact (Section3.StateForm.ready_ofLocal _).2 hφ
  have hin : p.firstState.generator.EvaluatedNumeric σ P α ⟨0,by omega⟩ := by
    rw [hinit]
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  have hgen := (fullTrace_and_generator_of_atomic_trace X Xc _ p ha he σ P α
    ⟨0,by omega⟩ hready hin (htrace α)).2.2
  rw [hinit] at hgen
  have hplain := hgen.2 (.predicate (.plain φ)) (by simp [Section3.StateForm.ofLocal])
  have hk := partition_size_pos σ P
  change (if h : 0 < P.size then _ else False) at hplain
  simp only [dif_pos hk] at hplain
  exact hplain ⟨0,le_rfl,σ.horizon_pos⟩ (zero_mem_first_interval σ P)
end Generated
end STLTableau.Section4
