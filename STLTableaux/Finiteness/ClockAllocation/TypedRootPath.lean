import STLTableaux.Finiteness.ClockAllocation.TypedSelectedPath
import STLTableaux.Finiteness.ClockAllocation.SelectedTypedExtension
import STLTableaux.Finiteness.ClockAllocation.InitialSlotFrame
import STLTableaux.Finiteness.Correctness.FiniteRootTableau
import STLTableaux.Finiteness.ClockAllocation.AllocatedRootPath

/-! Actual root-specific sparse accepting paths. Local typing and successor
frames come from the constructed SAME selected tree; no representative or
inventory-existence premise is added to the final root theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Actual finite-partition construction with literal sparse inventory
membership at EVERY full judgement state. -/
theorem typed_root_accepting_path
    (X : Set Var) (root : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : root.MixedReady)
    (hPlain : Judgement.holds σ P α k (.predicate (.plain root)))
    (hStable : σ.StablePartition root P) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (JudgementTableau.tableau X
        ((FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root)) : Set Clock) (plainInitialState root) FreeDerives) ∧
      p.accepting (JudgementTableau.tableau X
        ((FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root)) : Set Clock) (plainInitialState root) FreeDerives) ∧
      (JudgementTableau.fullTrace p).holds σ P α k ∧
      Subgraph.AllStates {F | FiniteInventory.TransitionWithin
        (FiniteInventory.locals (Finiteness.rootPlainFormulas root) (rootSlotTriples (Clock := Clock) root))
        (FiniteInventory.guards (rootSlotTriples root)) (FiniteInventory.resets (rootSlotTriples root)) F} p := by
  classical
  let τ := rootSlotTriples (Clock := Clock) root
  let Inv := fun (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) => Nonempty (InputOrigins σ P β j N) ∧
      Finiteness.StateFormulasBelow root N ∧ ∃J,SafeNormalization J (.ofState N)
  let Frame := fun (_ : ClockValuation Clock) (_ : STLTableau.Judgement.Position P)
    (N : Section3.StateForm Clock Var) (e : Equiv.Perm Clock) => Nonempty (SlotFrame τ N e)
  let Good := fun F : Section3.TransitionForm Clock Var=>FiniteInventory.TransitionWithin
    (FiniteInventory.locals (Finiteness.rootPlainFormulas root) τ)
    (FiniteInventory.guards τ) (FiniteInventory.resets τ) F
  let O := plainInitialOrigins (Clock := Clock) root σ P α k hReady hPlain hStable
  have hInv : Inv α k (plainInitialState root) :=
    ⟨⟨O⟩,Finiteness.plain_formulas_below root,⟨.predicate (.plain root),.predicate _⟩⟩
  have hFrame : Frame α k (plainInitialState root) (Equiv.refl Clock) :=
    ⟨plain_initial_slot_frame τ root (Equiv.refl Clock)⟩
  have rootRename : (plainInitialState (Clock := Clock) root).rename (Equiv.refl Clock)=plainInitialState root := by
    simp [plainInitialState,rename_state_local,Local.rename,Predicate.rename]
  rw [←rootRename]
  apply typed_path_of_local_extensions X ((FiniteInventory.clocks τ) : Set Clock) σ P Inv Frame Good _
    α α k (plainInitialState root) hInv O.holds (Equiv.refl Clock) hFrame (fun _ _=>rfl)
  intro β j N hI incoming hFr
  obtain ⟨O⟩ := hI.1
  obtain ⟨frame⟩ := hFr
  by_cases hne : N.locals.Nonempty
  · obtain ⟨J,W,owned,H,Er,F,T,hnil,hInput,hNext,hD,hFacts,hGuard,hSuccessor⟩ := O.nonempty_origin_step hne
    have hLocal := owned.local_mem_of_safe hInput
    obtain ⟨C,e,hAgree,hF,hTyped,hNextFrame⟩ := T.exists_root_typed_extension O root hI.2.1 hInput hLocal hnil hFacts frame
    refine ⟨F,C,e,hAgree,hF,hTyped,?_⟩
    intro M hn hj
    refine ⟨⟨hSuccessor hj M hn,(hD.formulas_below root hI.2.1).2 M hn,hFacts.1.next_input hn⟩,
      hNextFrame M hn⟩
  · have he : N.locals=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨J,hJ⟩ := hI.2.2
    have hz := hJ.weight_zero_of_locals_empty he
    let C : ResolvedCertificate N (.ofState N) :=
      ⟨J,J,J,PendingCompletionBase.resolve_zero J hz,hJ,hJ,PendingCompletionBase.erased_safe J hz hJ⟩
    have hWithin := frame.stateTyped.rename_within (Finiteness.rootPlainFormulas root) incoming frame.realizes
      (by intro φ hp;exact Finiteness.subformula_mem_rootPlainFormulas (hI.2.1 (.predicate (.plain φ)) hp))
    refine ⟨.ofState N,C,incoming,(fun _ _=>rfl),⟨O.holds,trivial⟩,⟨hWithin,?_⟩,?_⟩
    · intro M hm
      cases hm
    · intro M hm
      cases hm


/-- A SINGLE actual initial accepting path in the concrete finite tableau
satisfies its FULL trace for every initial valuation on the SAME signal and
fully stable partition. No path/inventory premise is assumed. -/
theorem finiteRootTableau_accepting_path_of_formula
    (X : Set Var) (root : Formula Var) (hReady : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition root P)
    (hTruth : σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩) :
    ∃p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (finiteRootTableau (Clock := Clock) X root) ∧
      p.accepting (finiteRootTableau (Clock := Clock) X root) ∧
      ∀β : ClockValuation Clock,(JudgementTableau.fullTrace p).holds σ P β ⟨0,by omega⟩ := by
  have hPlain : Judgement.holds σ P α ⟨0,by omega⟩ (.predicate (.plain root)) := by
    change if hk : 0<P.size then _ else False
    simp only [dif_pos (Generated.partition_size_pos σ P)]
    intro t ht
    exact ((hStable ⟨0,Generated.partition_size_pos σ P⟩).stable
      ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp hTruth
  obtain ⟨p,hr,ha,hs,hWithin⟩ := typed_root_accepting_path X root σ P α ⟨0,by omega⟩ hReady hPlain hStable
  have hc : (plainInitialState (Clock := Clock) root).freeClocks=∅ := by
    have he : (Section3.TransitionForm.ofState (plainInitialState (Clock := Clock) root)).allClocks=∅ :=
      (SafeNormalization.predicate (Predicate.plain root)).allClocks_eq_syntax
    apply Set.eq_empty_of_subset_empty
    intro c hcf
    have hh : c∈stateClockSupport (plainInitialState (Clock := Clock) root) := by
      rcases hcf with hg | ⟨hl,_⟩
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr hl)
    rw [←ofState_support,he] at hh
    exact hh
  have hAll := JudgementTableau.fullTrace_holds_all_valuations X _ _ FreeDerives
    (fun _ _ h=>h.2) p hr hc σ P α ⟨0,by omega⟩ hs
  have hrD := freeDerives_run_derives X _ _ p hr
  have haD := freeDerives_accepting_derives X _ _ p ha
  refine ⟨p,?_,?_,hAll⟩
  · exact (Subgraph.run_iff _ _ p).2 ⟨hrD,hWithin⟩
  · exact (Subgraph.accepting_iff _ _ p).2 ⟨haD,hWithin⟩

/-- Starting from an arbitrary satisfied revised accepting run, construct the
actual finite-tableau path on the same signal/partition, valid for all valuations. -/
theorem finiteRootTableau_accepting_path_of_revised_run
    (X : Set Var) (Q₀ : Set Clock) (root : Formula Var) (hReady : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition root P) (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q₀ (plainInitialState (Clock := Clock) root) Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q₀ (plainInitialState (Clock := Clock) root) Derives))
    (hs : (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩) :
    ∃q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (finiteRootTableau (Clock := Clock) X root) ∧
      q.accepting (finiteRootTableau (Clock := Clock) X root) ∧
      ∀β : ClockValuation Clock,(JudgementTableau.fullTrace q).holds σ P β ⟨0,by omega⟩ :=
  finiteRootTableau_accepting_path_of_formula X root hReady σ P α hStable
    (formula_of_satisfied_derives_run X Q₀ root σ P α p hr ha hs)

/-- The actual finite-tableau construction from an arbitrary satisfied original
closure-tableau run. No equality of full-trace languages is asserted. -/
theorem finiteRootTableau_accepting_path_of_original_run
    (X : Set Var) (Q₀ : Set Clock) (root : Formula Var) (hReady : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hStable : σ.StablePartition root P) (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q₀
      (Section3.StateForm.ofLocal (.predicate (.plain root)))))
    (ha : p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q₀
      (Section3.StateForm.ofLocal (.predicate (.plain root)))))
    (hs : p.fullTrace.holds σ P α ⟨0,by omega⟩) :
    ∃q : Path Clock (Section3.TransitionForm Clock Var),
      q.run (finiteRootTableau (Clock := Clock) X root) ∧
      q.accepting (finiteRootTableau (Clock := Clock) X root) ∧
      ∀β : ClockValuation Clock,(JudgementTableau.fullTrace q).holds σ P β ⟨0,by omega⟩ := by
  obtain ⟨q,hq,haq,hsq⟩ := (step1_satisfied_accepting_iff X Q₀ root hReady σ P hStable α).1 ⟨p,hr,ha,hs⟩
  exact finiteRootTableau_accepting_path_of_revised_run X Q₀ root hReady σ P α hStable q hq haq hsq

/-- Completeness of the concrete finite tableau, with the fully stable
partition API and mixed-readiness assumptions explicit. -/
theorem finiteRootTableau_complete
    (X : Set Var) (root : Formula Var) (hReady : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hStable : σ.StablePartition root P)
    (hTruth : σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P := by
  obtain ⟨p,hr,ha,hs⟩ := finiteRootTableau_accepting_path_of_formula (Clock := Clock) X root hReady σ P (fun _=>0) hStable hTruth
  refine ⟨p,hr,ha,?_⟩
  intro α
  exact judgement_atomic_trace_of_fullTrace p σ P α _ (hs α)

/-- Fixed fully stable partition correctness of the explicit finite tableau. -/
theorem finiteRootTableau_recognizes_iff
    (X : Set Var) (root : Formula Var) (hReady : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hStable : σ.StablePartition root P) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P ↔
      σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  ⟨finiteRootTableau_sound X root σ P,
    finiteRootTableau_complete X root hReady σ P hStable⟩
end STLTableau.Section4.Finiteness
