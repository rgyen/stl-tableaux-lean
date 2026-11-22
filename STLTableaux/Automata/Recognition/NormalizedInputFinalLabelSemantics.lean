import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics
import STLTableaux.Automata.Recognition.ExecutionSuffixPartition
import STLTableaux.Automata.Recognition.TableauClockValuations
import STLTableaux.Semantics.Partitions.BoundaryMarkerAssignment

/-! Observed early endpoints discharge all final atoms for checked inputs.
A singleton has closed markers, so an open-marker demand is still an explicit
obstruction. No arbitrary intermediate jump is erased or assigned a next step. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_final_singleton_labels_iff
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (P : IntervalPartition ρ.domain) (k : STLTableau.Judgement.Position P)
    (hk : k.val < P.size)
    (he : P.interval ⟨k.val, hk⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩)
    (α : ClockValuation Clock) :
    (∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
      l.holds ρ P α k) ↔
      Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  have hs := inputTableau_modeSteps_normalizedReady X root
    (Tableau.execution_modeSteps _ h _ _ e)
    (inputTableau_initial_normalizedReady X root hl)
  have hn : Local.terminal ∉ (inputTableau X root).label e.finalState.val.1.val := by
    intro ht
    have hend := finiteRootTableau_terminal_acceptance_exhausts X root.val h e ht
    exact (ne_of_lt hearly) hend
  have ha : ∀ a, Local.predicate (.plain (.atom a)) ∈
      (inputTableau X root).label e.finalState.val.1.val →
      ∀ u : ρ.Time, u.val ∈ (P.interval ⟨k.val, hk⟩).carrier → a.Holds (ρ.value u) := by
    intro a hatom u hu
    have hu' : u.val = e.boundary ⟨e.count, by omega⟩ := by
      simpa [he, MarkedInterval.carrier_eq] using hu
    let t : σ.Time := ⟨u.val, u.property.1, hp.1.symm ▸ u.property.2⟩
    exact Tableau.execution_projected_final_atom (inputTableau X root) h _ _ e hp
      Relation.ReflTransGen.refl t u rfl hu' a hatom
  rw [normalizedReady_labels_hold_iff (inputTableau X root) _
    (fun l hl => hs.1 l hl.1) ρ P α k hk]
  constructor
  · rintro ⟨_, hm, _⟩ ho
    have hm' := hm ○ ho
    rw [he] at hm'
    cases hm'
  · intro ho
    refine ⟨hn, ?_, ha⟩
    intro m hm
    cases m with
    | «open» => exact (ho hm).elim
    | closed => exact congrArg MarkedInterval.leftBoundary he

/-- A genuine last jump supplies the guard witness for a satisfied last
trace frame. This is only the final frame, not satisfaction of the preceding
path or permission to erase intermediate zero-time states. -/
theorem inputTableau_final_singleton_frame
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (P : IntervalPartition ρ.domain) (k : STLTableau.Judgement.Position P)
    (hk : k.val < P.size)
    (he : P.interval ⟨k.val, hk⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩)
    (ho : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val)
    {s : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).State}
    (hj : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      s e.finalState)
    (α : ClockValuation Clock) (hv : (inputTableau X root).ClockCompatible s.val.2 α) :
    ∃ l : EdgeLabel Clock,
      (s.val.1.val, l, e.finalState.val.1.val) ∈ (inputTableau X root).edges ∧
      ((Path.last l e.finalState.val.1.val).trace
        JudgementTableau.labels JudgementTableau.labels_finite).holds ρ P α k := by
  obtain ⟨l, hedge, hg, _⟩ := Tableau.discreteStep_clockCompatible
    (inputTableau X root) h _ _ hj hv
  refine ⟨l, hedge, hg, ?_⟩
  exact (inputTableau_final_singleton_labels_iff X root h e hp hearly P k hk he
    (l.resets.apply α)).mpr ho

/-- There is a full-domain geometric partition exposing the early final
state. This construction refines earlier pieces and does not assert that the
original run's trace survives that refinement. -/
theorem inputTableau_exists_final_singleton_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (ho : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val) :
    ∃ P : IntervalPartition ρ.domain, ∃ k : Fin P.size,
      P.interval k = ⟨e.boundary ⟨e.count, by omega⟩,
        e.boundary ⟨e.count, by omega⟩, ●, ●⟩ ∧
      ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
          l.holds ρ P α ⟨k.val, by omega⟩ := by
  let P : IntervalPartition ρ.domain :=
    { e.completedPointOpenFlowPartition hearly with
      covers := by
        rw [(e.completedPointOpenFlowPartition hearly).covers]
        change Set.Ico 0 σ.horizon = Set.Ico 0 ρ.horizon
        rw [hp.1] }
  let k : Fin P.size := ⟨2 * e.count, by change 2 * e.count < 2 * (e.count + 1); omega⟩
  have he := e.completedPointOpenFlowPartition_stop hearly
  refine ⟨P, k, he, ?_⟩
  intro α
  exact (inputTableau_final_singleton_labels_iff X root h e hp hearly P
    ⟨k.val, by omega⟩ k.isLt he α).mpr ho

/-- Flow labels and the observed final label hold on one partition, with the
old flow indices unchanged. Only the stopping singleton and open suffix are
added. Intermediate jump modes and the full trace remain separate obligations. -/
theorem inputTableau_exists_flow_and_final_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val))
    (hfinal : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val) :
    ∃ P : IntervalPartition ρ.domain, ∃ hsize : P.size = e.count + 2,
      (∀ i : Fin e.count, ∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label (e.start i).val.1.val,
          l.holds ρ P α ⟨i.val, by rw [hsize]; omega⟩) ∧
      (∀ α : ClockValuation Clock,
        ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
          l.holds ρ P α ⟨e.count, by rw [hsize]; omega⟩) ∧
      (∀ i : Fin e.count,
        STLTableau.Judgement.duration P ⟨i.val, by rw [hsize]; omega⟩ = e.duration i) := by
  let required : Fin e.count → Set Marker := fun i =>
    {b | Local.marker b ∈ (inputTableau X root).label (e.start i).val.1.val}
  obtain ⟨m, h0, hlast, hm⟩ :=
    (IntervalPartition.exists_boundaryMarkers_iff e.nonempty required).mpr ⟨hfirst, hconsistent⟩
  let P : IntervalPartition ρ.domain :=
    { e.completedMarkedPointFlowPartition hearly m h0 hlast with
      covers := by
        rw [(e.completedMarkedPointFlowPartition hearly m h0 hlast).covers]
        change Set.Ico 0 σ.horizon = Set.Ico 0 ρ.horizon
        rw [hp.1] }
  have hsize : P.size = e.count + 2 := rfl
  refine ⟨P, hsize, ?_, ?_, ?_⟩
  · intro i α
    exact (inputTableau_flow_labels_iff_markers X root h e hp m h0 hlast i P
      ⟨i.val, by omega⟩ (by change i.val < P.size; omega)
      (e.completedMarkedPointFlowPartition_old_piece hearly m h0 hlast i) α).mpr (hm i)
  · intro α
    exact (inputTableau_final_singleton_labels_iff X root h e hp hearly P
      ⟨e.count, by omega⟩ (by change e.count < P.size; omega)
      (e.completedMarkedPointFlowPartition_stop hearly m h0 hlast) α).mpr hfinal
  · intro i
    apply Subtype.ext
    exact e.completedMarkedPointFlowPartition_duration hearly m h0 hlast i

end STLTableau.Section4.Finiteness
