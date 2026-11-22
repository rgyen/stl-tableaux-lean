import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath
import STLTableaux.Finiteness.Correctness.JudgementTraceFreeSupport

/-! Constructs accepting paths over a fixed finite set of clock names.
This construction bounds clock support without requiring membership in the
slot-specific sets of judgements. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- A fixed palette of 4H clocks suffices for the actual resolved construction,
with full retained local labels bounded by H+3. -/
theorem allocated_root_accepting_path
    (X : Set Var) (Q : Finset Clock) (root : Formula Var)
    (hQ : 4*rootStepBudget root ≤ Q.card)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : root.MixedReady)
    (hPlain : Judgement.holds σ P α k (.predicate (.plain root)))
    (hStable : σ.StablePartition root P) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) root) FreeDerives) ∧
      p.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) root) FreeDerives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
        F.current.locals_finite.toFinset.card ≤ rootStepBudget root+3} p := by
  classical
  let B := rootStepBudget root
  let Inv := fun (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) => Nonempty (InputOrigins σ P β j N) ∧
      Finiteness.StateFormulasBelow root N ∧
      (Section3.TransitionForm.ofState N).allClocks_finite.toFinset.card ≤ 3*B ∧
      ∃ J,SafeNormalization J (.ofState N)
  let O := plainInitialOrigins (Clock := Clock) root σ P α k hReady hPlain hStable
  have hEmpty : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks=∅ :=
    (SafeNormalization.predicate (Predicate.plain root)).allClocks_eq_syntax
  have hRootInv : Inv α k (plainInitialState (Clock := Clock) root) := by
    refine ⟨⟨O⟩,Finiteness.plain_formulas_below root,?_,⟨.predicate (.plain root),.predicate _⟩⟩
    have hf : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks_finite.toFinset=∅ := by
      ext c; simp [hEmpty]
    rw [hf,Finset.card_empty]
    omega
  have rootRename : (plainInitialState (Clock := Clock) root).rename (Equiv.refl Clock)=plainInitialState root := by
    simp [plainInitialState,rename_state_local,Local.rename,Predicate.rename]
  rw [←rootRename]
  apply allocated_path_of_resolved_steps X Q (B+3) σ P Inv _ α α k
    (plainInitialState root) hRootInv (Equiv.refl Clock) _ _
  · intro β j N hInv
    obtain ⟨O⟩ := hInv.1
    by_cases hne : N.locals.Nonempty
    · obtain ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,hD,hFacts,hGuard,hSuccessor⟩ := O.nonempty_origin_step hne
      have hLocal := owned.local_mem_of_safe hInput
      have hQledger : ∀e∈T.rawLedger,e.source.formula∈Finiteness.rootPlainFormulas root := by
        intro e he
        exact Finiteness.subformula_mem_rootPlainFormulas (hD.current_formula_below root hInv.2.1 e.source
          ((T.normalized_retained_nonatomic_iff hFacts.1 e.source e.actual.source_nonatomic).2 ⟨e,he,rfl⟩))
      have hQcurrent : ∀p,Local.predicate p∈F.current.locals→p.formula∈Finiteness.rootPlainFormulas root := by
        intro p hp
        exact Finiteness.subformula_mem_rootPlainFormulas (hD.current_formula_below root hInv.2.1 p hp)
      have hb := O.bounded_domain_card_root root hInv.2.1
      have hl := T.rawLedger_length_bound O hLocal (Finiteness.rootPlainFormulas root) hQledger
      have hlabels := T.current_locals_card_bound O hLocal hFacts.1 (Finiteness.rootPlainFormulas root) hQcurrent
      have hLedger : T.rawLedger.length≤B := by dsimp [B,rootStepBudget]; omega
      have hLabels : F.current.locals_finite.toFinset.card≤B+3 := by dsimp [B,rootStepBudget]; omega
      let C : ResolvedCertificate N F := ⟨J,H,Er,T.realize,hInput,hFacts.1,hFacts.2.1⟩
      refine ⟨F,T.allocationSupport,C,hFacts.2.2.1,hLabels,?_,T.output_support_allocation hInput hFacts.1,
        (T.allocationSupport_card B hInv.2.2.1 hLedger).trans hQ,?_⟩
      · exact Finset.subset_union_left
      · intro M hn hj
        have hBelow := hD.formulas_below root hInv.2.1
        have hClock := T.normalized_next_clock_card hnil hFacts.1 hn
        refine ⟨hSuccessor hj M hn,hBelow.2 M hn,?_,hFacts.1.next_input hn⟩
        omega
    · have he : N.locals=∅ := Set.not_nonempty_iff_eq_empty.mp hne
      obtain ⟨J,hJ⟩ := hInv.2.2.2
      have hz := hJ.weight_zero_of_locals_empty he
      let C : ResolvedCertificate N (.ofState N) :=
        ⟨J,J,J,PendingCompletionBase.resolve_zero J hz,hJ,hJ,
          PendingCompletionBase.erased_safe J hz hJ⟩
      refine ⟨.ofState N,(Section3.TransitionForm.ofState N).allClocks_finite.toFinset,C,
        ⟨O.holds,trivial⟩,?_,Finset.Subset.refl _,?_,?_,?_⟩
      · have hf : N.locals_finite.toFinset=∅ := by ext l; simp [he]
        change N.locals_finite.toFinset.card≤B+3
        rw [hf,Finset.card_empty]
        omega
      · intro c hc
        exact (Set.Finite.mem_toFinset _).2 hc
      · have hi := hInv.2.2.1
        dsimp [B] at hi ⊢
        omega
      · intro M hn
        cases hn
  · intro c hc
    rw [hEmpty] at hc
    exact hc.elim
  · intro c hc
    rfl


omit [Infinite Clock] in
/-- Forget only the extra free-safety proof on graph edges. -/
theorem freeDerives_valid_derives
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hp : p.valid (JudgementTableau.tableau X Q root FreeDerives)) :
    p.valid (JudgementTableau.tableau X Q root Derives) := by
  induction p with
  | last e F => obtain ⟨N,h⟩ := hp; exact ⟨N,h.1⟩
  | step e F tail ih =>
    obtain ⟨N,hN⟩ := hp.1
    obtain ⟨⟨M,hM⟩,⟨K,hK⟩,I,hnext,hI,hIn⟩ := hp.2.2
    exact ⟨⟨N,hN.1⟩,ih hp.2.1,⟨⟨M,hM.1⟩,⟨K,hK.1⟩,I,hnext,hI.1,hIn⟩⟩

omit [Infinite Clock] in
theorem freeDerives_run_derives
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hp : p.run (JudgementTableau.tableau X Q root FreeDerives)) :
    p.run (JudgementTableau.tableau X Q root Derives) :=
  ⟨freeDerives_valid_derives X Q root p hp.1,hp.2.1.1,hp.2.2⟩

omit [Infinite Clock] in
theorem freeDerives_accepting_derives
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hp : p.accepting (JudgementTableau.tableau X Q root FreeDerives)) :
    p.accepting (JudgementTableau.tableau X Q root Derives) :=
  ⟨freeDerives_valid_derives X Q root p hp.1,hp.2⟩

/-- A SINGLE allocated accepting path satisfies the full trace for EVERY
initial valuation. Root closedness is derived from the actual plain input. -/
theorem allocated_root_path_of_formula
    (X : Set Var) (Q : Finset Clock) (φ : Formula Var)
    (hQ : 4*rootStepBudget φ ≤ Q.card) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P)
    (hTruth : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      p.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      p.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      p.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      (∀β : ClockValuation Clock,(JudgementTableau.fullTrace p).holds σ P β ⟨0,by omega⟩) ∧
      Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
        F.current.locals_finite.toFinset.card ≤ rootStepBudget φ+3} p := by
  have hPlain : Judgement.holds σ P α ⟨0,by omega⟩ (.predicate (.plain φ)) := by
    change if hk : 0<P.size then _ else False
    simp only [dif_pos (Generated.partition_size_pos σ P)]
    intro t ht
    exact ((hStable ⟨0,Generated.partition_size_pos σ P⟩).stable
      ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hTruth
  obtain ⟨p,hr,ha,hs,hGood⟩ := allocated_root_accepting_path X Q φ hQ σ P α ⟨0,by omega⟩ hReady hPlain hStable
  have hc : (plainInitialState (Clock := Clock) φ).freeClocks=∅ := by
    have he : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) φ)).allClocks=∅ :=
      (SafeNormalization.predicate (Predicate.plain φ)).allClocks_eq_syntax
    apply Set.eq_empty_of_subset_empty
    intro c hcf
    have hh : c∈stateClockSupport (plainInitialState (Clock := Clock) φ) := by
      rcases hcf with hg | ⟨hl,_⟩
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr hl)
    rw [←ofState_support,he] at hh
    exact hh
  refine ⟨p,hr,ha,freeDerives_run_derives X Q _ p hr,freeDerives_accepting_derives X Q _ p ha,?_,hGood⟩
  exact JudgementTableau.fullTrace_holds_all_valuations X Q _ FreeDerives
    (fun _ _ h=>h.2) p hr hc σ P α ⟨0,by omega⟩ hs

/-- Replacement of an arbitrary satisfied revised accepting run by one
allocated path, uniformly valid for all initial valuations. -/
theorem allocated_root_path_of_satisfied_run
    (X : Set Var) (Q₀ : Set Clock) (Q : Finset Clock) (φ : Formula Var)
    (hQ : 4*rootStepBudget φ ≤ Q.card) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q₀ (plainInitialState (Clock := Clock) φ) Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q₀ (plainInitialState (Clock := Clock) φ) Derives))
    (hs : (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      q.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      q.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      (∀β : ClockValuation Clock,(JudgementTableau.fullTrace q).holds σ P β ⟨0,by omega⟩) ∧
      Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
        F.current.locals_finite.toFinset.card ≤ rootStepBudget φ+3} q :=
  allocated_root_path_of_formula X Q φ hQ hReady σ P α hStable
    (formula_of_satisfied_derives_run X Q₀ φ σ P α p hr ha hs)

/-- The same allocated construction from the original closure tableau on the
same signal and fully stable partition. -/
theorem allocated_root_path_of_original_run
    (X : Set Var) (Q₀ : Set Clock) (Q : Finset Clock) (φ : Formula Var)
    (hQ : 4*rootStepBudget φ ≤ Q.card) (hReady : φ.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition φ P) (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q₀
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (ha : p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q₀
      (Section3.StateForm.ofLocal (.predicate (.plain φ)))))
    (hs : p.fullTrace.holds σ P α ⟨0,by omega⟩) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      q.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) FreeDerives) ∧
      q.run (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      q.accepting (JudgementTableau.tableau X (Q : Set Clock) (plainInitialState (Clock := Clock) φ) Derives) ∧
      (∀β : ClockValuation Clock,(JudgementTableau.fullTrace q).holds σ P β ⟨0,by omega⟩) ∧
      Subgraph.AllStates {F | F.allClocks ⊆ (Q : Set Clock) ∧
        F.current.locals_finite.toFinset.card ≤ rootStepBudget φ+3} q := by
  obtain ⟨q,hq,haq,hsq⟩ := (step1_satisfied_accepting_iff X Q₀ φ hReady σ P hStable α).1 ⟨p,hr,ha,hs⟩
  exact allocated_root_path_of_satisfied_run X Q₀ Q φ hQ hReady σ P α hStable q hq haq hsq
end STLTableau.Section4.Finiteness
