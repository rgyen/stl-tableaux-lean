import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics
import STLTableaux.Semantics.Partitions.BoundaryMarkerAssignment
import STLTableaux.Automata.Recognition.ExecutionSuffixPartition

/-! Construct a full-domain partition for positive-flow labels with compatible
marker requirements, appending an unlabelled suffix for early termination.
This is not an execution-to-trace theorem: discrete entering labels, guards,
resets and zero-time intermediate modes are not collapsed or erased. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_exists_flow_label_partition_with_duration
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val)) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = e.count,
      (∀ i : Fin e.count, ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
          l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin e.count,
        STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; exact i.isLt⟩ = e.duration i) := by
  let required : Fin e.count → Set Marker := fun i =>
    {b | Local.marker b ∈ (inputTableau X root).label (e.start i).val.1.val}
  obtain ⟨m, h0, hlast, hm⟩ :=
    (IntervalPartition.exists_boundaryMarkers_iff e.nonempty required).mpr ⟨hfirst, hconsistent⟩
  let P : IntervalPartition ρ.domain :=
    { e.markedFlowPartition m h0 hlast with
      covers := by
        change (⋃ i, ((e.markedFlowPartition m h0 hlast).interval i).carrier) =
          Set.Ico 0 ρ.horizon
        rw [(e.markedFlowPartition m h0 hlast).covers, hexhaust, hp.1] }
  refine ⟨P, rfl, ?_, ?_⟩
  · intro i α
    exact (inputTableau_flow_labels_iff_markers X root h e hp m h0 hlast i P
      ⟨i.val, by change i.val < e.count + 1; omega⟩
      (by change i.val < e.count; exact i.isLt) rfl α).mpr (hm i)
  · intro i
    apply Subtype.ext
    exact e.markedFlowPartition_duration m h0 hlast i

theorem inputTableau_exists_flow_label_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val)) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = e.count,
      ∀ i : Fin e.count, ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
          l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩ := by
  obtain ⟨P, hsize, hl, _⟩ := inputTableau_exists_flow_label_partition_with_duration
    X root h e hp hexhaust hfirst hconsistent
  exact ⟨P, hsize, hl⟩

/-- A terminal final mode supplies exhaustion; it is not an additional run
assumption. Marker compatibility is still explicit, and this result makes no
claim about early acceptance in a nonterminal goal or intermediate jumps. -/
theorem inputTableau_terminal_exists_flow_label_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (ht : e.finalState.val.1 ∈ (inputTableau X root).terminalModes)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val)) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = e.count,
      ∀ i : Fin e.count, ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
          l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩ := by
  exact inputTableau_exists_flow_label_partition X root h e hp
    (finiteRootTableau_terminal_acceptance_exhausts X root.val h e ht)
    hfirst hconsistent

/-- Cover the entire signal even when the execution stops early. At most one
unlabelled suffix is appended; all executed pieces retain their markers and
duration. No satisfaction or invariant is asserted on that suffix. -/
theorem inputTableau_exists_completed_flow_label_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val)) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : e.count ≤ P.size,
      P.size ≤ e.count + 1 ∧
      ∀ i : Fin e.count, ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
          l.holds ρ P α ⟨i.val, by omega⟩ := by
  by_cases hexhaust : e.boundary ⟨e.count, by omega⟩ = σ.horizon
  · obtain ⟨P, hsize, hlabels⟩ :=
      inputTableau_exists_flow_label_partition X root h e hp hexhaust hfirst hconsistent
    exact ⟨P, by omega, by omega, hlabels⟩
  · have he : e.boundary ⟨e.count, by omega⟩ < σ.horizon :=
      lt_of_le_of_ne e.last_le_horizon hexhaust
    let required : Fin e.count → Set Marker := fun i =>
      {b | Local.marker b ∈ (inputTableau X root).label (e.start i).val.1.val}
    obtain ⟨m, h0, hlast, hm⟩ :=
      (IntervalPartition.exists_boundaryMarkers_iff e.nonempty required).mpr ⟨hfirst, hconsistent⟩
    let P : IntervalPartition ρ.domain :=
      { e.completedMarkedFlowPartition he m h0 with
        covers := by
          rw [(e.completedMarkedFlowPartition he m h0).covers]
          change Set.Ico 0 σ.horizon = Set.Ico 0 ρ.horizon
          rw [hp.1] }
    have hsize : P.size = e.count + 1 := rfl
    refine ⟨P, by omega, by omega, ?_⟩
    intro i α
    exact (inputTableau_flow_labels_iff_markers X root h e hp m h0 hlast i P
      ⟨i.val, by omega⟩ (by change i.val < P.size; omega)
      (e.completedMarkedFlowPartition_old_piece he m h0 hlast i) α).mpr (hm i)

end STLTableau.Section4.Finiteness
