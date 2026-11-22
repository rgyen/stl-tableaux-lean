import STLTableaux.Finiteness.Correctness.OriginalPathInclusion

/-! On a given fully stable partition, the original and auxiliary derivation
tableaux admit satisfied full traces for the same signals and initial clock
valuations. The reverse direction uses Lemma 4.33. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

omit [DecidableEq Clock] [Infinite Clock] in
 theorem judgement_atomic_trace_of_fullTrace
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : (JudgementTableau.fullTrace p).holds σ P α k) :
    (p.trace JudgementTableau.labels JudgementTableau.labels_finite).holds σ P α k := by
  induction p generalizing α k with
  | last e F => exact ⟨hs.1,fun l hl => hs.2 l hl.1⟩
  | step e F t ih =>
    refine ⟨⟨hs.1.1,fun l hl => hs.1.2 l hl.1⟩,?_⟩
    change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
    by_cases hk : k.1 < P.size
    · simp only [dif_pos hk] at hs ⊢
      exact ih _ _ hs.2
    · simpa only [dif_neg hk] using hs.2

 theorem formula_of_satisfied_derives_run
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ))) Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q
      (Section3.StateForm.ofLocal (.predicate (.plain φ))) Derives))
    (hs : (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) :
    σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  have hi : (Section3.StateForm.ofLocal (.predicate (.plain φ))).EvaluatedNumeric
      σ P α ⟨0,by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  have hroot := (derives_fullTrace_and_root X Q _ p hr ha σ P α ⟨0,by omega⟩ hi
    (judgement_atomic_trace_of_fullTrace p σ P α _ hs)).2.2
  have hplain := hroot.2 (.predicate (.plain φ)) (by simp [Section3.StateForm.ofLocal])
  have hk := Generated.partition_size_pos σ P
  change (if h : 0 < P.size then _ else False) at hplain
  simp only [dif_pos hk] at hplain
  exact hplain ⟨0,le_rfl,σ.horizon_pos⟩ (Generated.zero_mem_first_interval σ P)

/-- Lemma 4.33 applied to the initial generator. The accepting run has a
satisfied full trace at the chosen initial clock valuation. -/
theorem original_satisfied_run_of_formula
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hst : σ.StablePartition φ P) (hs : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (Generated.closureTableau ConcreteContextual.catalogue X Q
        (Section3.StateForm.ofLocal (.predicate (.plain φ)))) ∧
      p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q
        (Section3.StateForm.ofLocal (.predicate (.plain φ)))) ∧
      p.fullTrace.holds σ P α ⟨0,by omega⟩ := by
  apply Generated.initial_run_exists X Q _ σ P α ⟨0,by omega⟩
  · intro ψ hψ
    obtain ⟨p,hp,hpψ⟩ := hψ
    have he : p = .plain φ := by simpa only [Section3.StateForm.ofLocal,
      Set.mem_singleton_iff,Local.predicate.injEq] using hp
    subst p
    simpa only [Section3.Predicate.formula] using (hpψ ▸ hst)
  · intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  · refine ⟨by simp [Section3.StateForm.ofLocal],?_⟩
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    change if h : 0 < P.size then _ else False
    simp only [dif_pos (Generated.partition_size_pos σ P)]
    intro t ht
    exact ((hst ⟨0,Generated.partition_size_pos σ P⟩).stable
      ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hs

/-- For the same signal, partition, and initial clock valuation, the original
tableau has a satisfied accepting full trace if and only if the derivation
tableau does. -/
theorem step1_satisfied_accepting_iff
    (X : Set Var) (Q : Set Clock) (φ : Formula Var) (hφ : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (hst : σ.StablePartition φ P)
    (α : ClockValuation Clock) :
    (∃ p : Path Clock (ClosureState Clock Var),
      p.run (Generated.closureTableau ConcreteContextual.catalogue X Q
        (Section3.StateForm.ofLocal (.predicate (.plain φ)))) ∧
      p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q
        (Section3.StateForm.ofLocal (.predicate (.plain φ)))) ∧
      p.fullTrace.holds σ P α ⟨0,by omega⟩) ↔
    (∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X Q (Section3.StateForm.ofLocal (.predicate (.plain φ))) Derives) ∧
      p.accepting (JudgementTableau.tableau X Q (Section3.StateForm.ofLocal (.predicate (.plain φ))) Derives) ∧
      (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) := by
  constructor
  · rintro ⟨p,hr,ha,hs⟩
    have hready : (Section3.StateForm.ofLocal (Clock := Clock) (.predicate (.plain φ))).Ready :=
      (Section3.StateForm.ready_ofLocal _).2 hφ
    have hm := original_accepting_run_forward X Q _ hready p hr ha
    refine ⟨JudgementTableau.forgetGenerator p,hm.1,hm.2,?_⟩
    rw [JudgementTableau.full_trace_forward]
    exact hs
  · rintro ⟨p,hr,ha,hs⟩
    exact original_satisfied_run_of_formula X Q φ σ P α hst
      (formula_of_satisfied_derives_run X Q φ σ P α p hr ha hs)

end STLTableau.Section4.Finiteness
