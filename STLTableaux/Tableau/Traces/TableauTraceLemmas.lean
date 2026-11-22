import STLTableaux.Tableau.Correctness.TableauSoundness

/-! Predicate invariants along a trace (Lemma D.1), trace equivalence
(Lemma 4.31), and full trace satisfaction along suffixes (Lemma D.2). -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}
namespace Path

def NumericAlong (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Path Clock (ClosureState Clock Var) → Prop
  | .last _ s => s.form.EvaluatedNumeric σ P α k
  | .step e s t => s.form.EvaluatedNumeric σ P α k ∧ ∀ hk : k.1 < P.size,
      NumericAlong σ P (ClockResetSet.elapse (e.resets.apply α)
        (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ t
/-- A path suffix with the clock valuation and partition position reached
by applying the preceding resets and elapsing the preceding intervals. -/
inductive ScopedSuffix {D : Set ℝ} (P : IntervalPartition D) :
    Path Clock (ClosureState Clock Var) → ClockValuation Clock → STLTableau.Judgement.Position P →
    Path Clock (ClosureState Clock Var) → ClockValuation Clock → STLTableau.Judgement.Position P → Prop
  | here (p α k) : ScopedSuffix P p α k p α k
  | next (e : EdgeLabel Clock) (s : ClosureState Clock Var)
      (t : Path Clock (ClosureState Clock Var)) (α : ClockValuation Clock)
      (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
      {q : Path Clock (ClosureState Clock Var)} {β : ClockValuation Clock}
      {j : STLTableau.Judgement.Position P}
      (h : ScopedSuffix P t (ClockResetSet.elapse (e.resets.apply α)
        (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ q β j) :
      ScopedSuffix P (.step e s t) α k q β j

theorem NumericAlong.at_suffix (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    {p q : Path Clock (ClosureState Clock Var)} {α β : ClockValuation Clock}
    {k j : STLTableau.Judgement.Position P} (h : ScopedSuffix P p α k q β j) :
    p.NumericAlong σ P α k → q.firstState.form.EvaluatedNumeric σ P β j := by
  induction h with
  | here p α k => cases p <;> exact fun h => by first | exact h | exact h.1
  | next e s t α k hk h ih => exact fun hn => ih (hn.2 hk)

theorem fullTrace_at_suffix (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    {p q : Path Clock (ClosureState Clock Var)} {α β : ClockValuation Clock}
    {k j : STLTableau.Judgement.Position P} (h : ScopedSuffix P p α k q β j) :
    p.fullTrace.holds σ P α k → q.fullTrace.holds σ P β j := by
  induction h with
  | here => exact id
  | next e s t α k hk h ih =>
      intro hh
      change _ ∧ (if h : k.1 < P.size then _ else False) at hh
      exact ih (by simpa only [dif_pos hk,Trace.holds,Path.fullTrace] using hh.2)
end Path
namespace Generated
variable [DecidableEq Clock]

/-- Each closure along a satisfied trace meets the current and next numeric
invariant conditions. -/
theorem numeric_along_of_atomic_trace
    (X : Set Var) (Xc : Set Clock) (initial : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc initial))
    (he : p.firstIncoming = p.firstState.incoming)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : p.firstState.generator.EvaluatedNumeric σ P α k)
    (hs : (p.trace labels labels_finite).holds σ P α k) : p.NumericAlong σ P α k := by
  induction p generalizing α k with
  | last e s =>
      have hnp := nonPredicate_of_atomic_trace X Xc initial (.last e s) ha he σ P α k hs
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1
      exact ConcreteContextual.minimal_closure_numeric hc σ P α k
        ⟨hi,by intro N hn; cases hn⟩ hnp
  | step e s t ih =>
      have hnp := nonPredicate_of_atomic_trace X Xc initial (.step e s t) ha he σ P α k hs
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1.1
      have hedge : s.form.nextPart = some t.firstState.generator ∧
          t.firstIncoming = t.firstState.incoming := ha.1.2.2.2.2
      have htail : t.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) :=
        ⟨ha.1.2.1,ha.2⟩
      have hn := ConcreteContextual.minimal_closure_numeric hc σ P α k
        ⟨hi,by intro N hn; cases hn⟩ hnp
      refine ⟨hn,?_⟩
      intro hk
      have he' : e = s.incoming := he
      subst e
      change _ ∧ (if h : k.1 < P.size then _ else False) at hs
      simp only [dif_pos hk] at hs
      exact ih htail hedge.2 _ _ (hn.2 _ hedge.1 hk) hs.2

private theorem plain_initial_numeric (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Section3.StateForm.ofLocal (.predicate (.plain φ)) : Section3.StateForm Clock Var).EvaluatedNumeric
      σ P α k := by
  intro l hl
  have he : l = .predicate (.plain φ) := hl
  subst l
  intro hk
  trivial

/-- Lemma D.1 (trace invariant). A satisfied trace of an accepting run
gives conditions (1) and (3) of the predicate invariants along the run. -/
theorem trace_invariant
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : (p.trace labels labels_finite).holds σ P α k) : p.NumericAlong σ P α k := by
  have hi : p.firstState.generator.EvaluatedNumeric σ P α k := by
    rw [hr.2.2.1]
    exact plain_initial_numeric φ σ P α k
  exact numeric_along_of_atomic_trace X Xc _ p ha hr.2.2.2 σ P α k hi hs

/-- Lemma 4.31 (trace equivalence). The trace and full trace of an
accepting run for a normalized formula have the same satisfaction relation. -/
theorem trace_equivalence [Nontrivial Clock]
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (p.trace labels labels_finite).holds σ P α k ↔ p.fullTrace.holds σ P α k := by
  constructor
  · intro hs
    have hready : p.firstState.generator.Ready := by
      rw [hr.2.2.1]
      exact (Section3.StateForm.ready_ofLocal _).2 hφ
    have hi : p.firstState.generator.EvaluatedNumeric σ P α k := by
      rw [hr.2.2.1]
      exact plain_initial_numeric φ σ P α k
    exact (fullTrace_and_generator_of_atomic_trace X Xc _ p ha hr.2.2.2 σ P α k hready hi hs).1
  · exact atomic_trace_of_fullTrace p σ P α k
/-- Closure subsumption recovers generator satisfaction from full trace
satisfaction at the corresponding position and clock valuation. -/
theorem form_generator_of_fullTrace
    (X : Set Var) (Xc : Set Clock) (initial : Section3.StateForm Clock Var)
    (p : Path Clock (ClosureState Clock Var))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc initial))
    (he : p.firstIncoming = p.firstState.incoming)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : p.fullTrace.holds σ P α k) :
    p.firstState.form.holds σ P α k ∧ p.firstState.generator.holds σ P α k := by
  induction p generalizing α k with
  | last e s =>
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1
      have he' : e = s.incoming := he
      subst e
      have hf : s.form.holds σ P α k := by
        refine ⟨hs,?_⟩
        have hn : s.form.nextPart = none := ha.2
        simp only [hn]
      exact ⟨hf,(hc.extension.sound σ P α k hf).1⟩
  | step e s t ih =>
      have hc : ConcreteContextual.catalogue.IsClosure
          (Section3.TransitionForm.ofState s.generator) s.form := ha.1.1
      have hedge : s.form.nextPart = some t.firstState.generator ∧
          t.firstIncoming = t.firstState.incoming := ha.1.2.2.2.2
      have htail : t.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) :=
        ⟨ha.1.2.1,ha.2⟩
      have he' : e = s.incoming := he
      subst e
      change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs
        have ht := ih htail hedge.2 _ _ hs.2
        have hf : s.form.holds σ P α k := by
          refine ⟨hs.1,?_⟩
          rw [hedge.1]
          simpa only [dif_pos hk,ClosureState.incoming] using ht.2
        exact ⟨hf,(hc.extension.sound σ P α k hf).1⟩
      · simp only [dif_neg hk] at hs
        exact hs.2.elim

private theorem accepting_incoming_at_suffix {D : Set ℝ}
    (X : Set Var) (Xc : Set Clock) (initial : Section3.StateForm Clock Var)
    (P : IntervalPartition D)
    {p q : Path Clock (ClosureState Clock Var)} {α β : ClockValuation Clock}
    {k j : STLTableau.Judgement.Position P} (h : Path.ScopedSuffix P p α k q β j) :
    p.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) →
    p.firstIncoming = p.firstState.incoming →
    q.accepting (closureTableau ConcreteContextual.catalogue X Xc initial) ∧
      q.firstIncoming = q.firstState.incoming := by
  induction h with
  | here => exact fun ha he => ⟨ha,he⟩
  | next e s t α k hk h ih =>
      intro ha _
      exact ih ⟨ha.1.2.1,ha.2⟩ ha.1.2.2.2.2.2

/-- Lemma D.2 (trace implies full trace). At each suffix of a satisfied
accepting run, its full trace and generator hold at the clock valuation
reached by the preceding resets and interval durations. -/
theorem trace_ftrace_implication [Nontrivial Clock]
    (X : Set Var) (Xc : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (closureTableau ConcreteContextual.catalogue X Xc
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : (p.trace labels labels_finite).holds σ P α k)
    {q : Path Clock (ClosureState Clock Var)} {β : ClockValuation Clock}
    {j : STLTableau.Judgement.Position P} (hq : Path.ScopedSuffix P p α k q β j) :
    q.fullTrace.holds σ P β j ∧ q.firstState.generator.holds σ P β j := by
  have hfull := (trace_equivalence X Xc φ hφ p hr ha σ P α k).1 hs
  have hqfull := Path.fullTrace_at_suffix σ P hq hfull
  obtain ⟨hqA,hqE⟩ := accepting_incoming_at_suffix X Xc _ P hq ha hr.2.2.2
  exact ⟨hqfull,(form_generator_of_fullTrace X Xc _ q hqA hqE σ P β j hqfull).2⟩
end Generated
end STLTableau.Section4
