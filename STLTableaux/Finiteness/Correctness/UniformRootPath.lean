import STLTableaux.Finiteness.Correctness.UniformSelectedPath
import STLTableaux.Finiteness.Bounds.SelectedRetainedCount

/-! Constructs bounded accepting paths on a fixed signal, fully stable
partition, and clock valuation. The bounds follow from the chosen expansions
and the numbers of tracked truth intervals for the root's timed subformulas. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Bounds the accepting path using the counts for the root’s timed subformulas. -/
theorem uniform_root_accepting_path
    (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : root.MixedReady)
    (hPlain : Judgement.holds σ P α k (.predicate (.plain root)))
    (hStable : σ.StablePartition root P) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) root) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) root) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | UniformStateBounds (rootStepBudget root) F ∧
        Finiteness.FormFormulasBelow root F ∧ OriginCertifiedState σ P F} p := by
  apply uniform_path_of_local_counts X Q root (rootStepBudget root) σ P _ α k hReady hPlain hStable
  intro β j N O hN J W owned Hraw Er F T hInput hD hFacts
  have hLocal := owned.local_mem_of_safe hInput
  have hQ : ∀ e ∈ T.rawLedger, e.source.formula ∈ Finiteness.rootPlainFormulas root := by
    intro e he
    apply Finiteness.subformula_mem_rootPlainFormulas
    apply hD.current_formula_below root hN e.source
    exact (T.normalized_retained_nonatomic_iff hFacts.1 e.source e.actual.source_nonatomic).2 ⟨e,he,rfl⟩
  have hQcurrent : ∀ p : Predicate Clock Var, Local.predicate p ∈ F.current.locals →
      p.formula ∈ Finiteness.rootPlainFormulas root := by
    intro p hp
    exact Finiteness.subformula_mem_rootPlainFormulas (hD.current_formula_below root hN p hp)
  have hL := T.rawLedger_length_bound O hLocal (Finiteness.rootPlainFormulas root) hQ
  have hC := T.current_locals_card_bound O hLocal hFacts.1 (Finiteness.rootPlainFormulas root) hQcurrent
  have hB := O.bounded_domain_card_root root hN
  dsimp [rootStepBudget]
  omega

/-- Point truth is transported over the initial stable piece, preserving the
same signal, partition and initial valuation. -/
theorem uniform_root_path_of_formula
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P)
    (hTruth : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | UniformStateBounds (rootStepBudget φ) F ∧
        Finiteness.FormFormulasBelow φ F ∧ OriginCertifiedState σ P F} p := by
  apply uniform_root_accepting_path X Q φ σ P α ⟨0,by omega⟩ hReady _ hStable
  change if hk : 0 < P.size then _ else False
  simp only [dif_pos (Generated.partition_size_pos σ P)]
  intro t ht
  exact ((hStable ⟨0,Generated.partition_size_pos σ P⟩).stable
    ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hTruth

/-- Replacement of an arbitrary satisfied revised run by a uniformly bounded
one, with full retained labels and whole current/next clock support bounded. -/
theorem uniform_root_path_of_satisfied_run
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives))
    (hs : (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace q).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | UniformStateBounds (rootStepBudget φ) F ∧
        Finiteness.FormFormulasBelow φ F ∧ OriginCertifiedState σ P F} q :=
  uniform_root_path_of_formula X Q φ hReady σ P α hStable
    (formula_of_satisfied_derives_run X Q φ σ P α p hr ha hs)

/-- Constructs a bounded path from a satisfied accepting full trace of the
original closure tableau. -/
theorem uniform_root_path_of_original_run
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (hs : p.fullTrace.holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X Q (plainInitialState (Clock := Clock) φ) Derives) ∧
      (JudgementTableau.fullTrace q).holds σ P α ⟨0,by omega⟩ ∧
      Subgraph.AllStates {F | UniformStateBounds (rootStepBudget φ) F ∧
        Finiteness.FormFormulasBelow φ F ∧ OriginCertifiedState σ P F} q := by
  obtain ⟨q,hq,haq,hsq⟩ := (step1_satisfied_accepting_iff X Q φ hReady σ P hStable α).1 ⟨p,hr,ha,hs⟩
  exact uniform_root_path_of_satisfied_run X Q φ hReady σ P α hStable q hq haq hsq
end STLTableau.Section4.Finiteness
