import STLTableaux.Automata.Recognition.ExecutionFlowPartition

/-! Observation lemmas for endpoint-aware executions.
The initial state owns zero. Positive-time boundaries are observed at their
destination flow; initial jumps may lead into a left-open first flow. -/
namespace STLTableau.HybridAutomaton.Execution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)

theorem start_time_mem_domain (i : Fin e.count) :
    e.boundary ⟨i.val, by omega⟩ ∈ σ.domain := by
  constructor
  · rw [← e.first_zero]
    exact e.increasing.monotone (by change 0 ≤ i.val; omega)
  · exact (e.increasing (by change i.val < e.count; exact i.isLt)).trans_le e.last_le_horizon

def startTime (i : Fin e.count) : σ.Time :=
  ⟨e.boundary ⟨i.val, by omega⟩, e.start_time_mem_domain i⟩

/-- At a positive entry time, observe the destination of the jump block.
Zero instead belongs to the initial state. -/
theorem signal_at_start (i : Fin e.count) (positive : 0 < (e.startTime i).val) :
    σ.value (e.startTime i) = (e.start i).val.2 := by
  have ht : e.boundary ⟨i.val, by omega⟩ < e.boundary ⟨i.val + 1, by omega⟩ :=
    e.increasing (by change i.val < i.val + 1; omega)
  have hv := e.signal_eq i (e.startTime i) ⟨le_rfl, ht⟩ positive
  simpa only [startTime, sub_self, (e.continuousStep i).2.1] using hv

theorem signal_at_initial :
    σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = e.initialState.val.2 :=
  e.initial_signal_eq

/-- The left flow does not own its right endpoint in the signal. -/
theorem boundary_not_in_previous_piece (i : Fin e.count) :
    e.boundary ⟨i.val + 1, by omega⟩ ∉ (e.flowPartition.interval i).carrier := by
  rw [e.mem_flowPartition]
  exact fun h => (lt_irrefl _) h.2

/-- Geometric allocation to positive-flow time cells. At zero this does not
assert that the first curve supplies the observed valuation. -/
theorem existsUnique_observed_piece (t : σ.Time)
    (ht : t.val < e.boundary ⟨e.count, by omega⟩) :
    ∃! i : Fin e.count, t.val ∈ (e.flowPartition.interval i).carrier := by
  have hm : t.val ∈ Set.Ico (0 : ℝ) (e.boundary ⟨e.count, by omega⟩) :=
    ⟨t.property.1, ht⟩
  rw [← e.flowPartition.covers] at hm
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hm
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (e.flowPartition.pairwiseDisjoint hji) hj hi

noncomputable def observedIndex (t : σ.Time)
    (ht : t.val < e.boundary ⟨e.count, by omega⟩) : Fin e.count :=
  (e.existsUnique_observed_piece t ht).choose

theorem observedIndex_spec (t : σ.Time)
    (ht : t.val < e.boundary ⟨e.count, by omega⟩) :
    e.boundary ⟨(e.observedIndex t ht).val, by omega⟩ ≤ t.val ∧
      t.val < e.boundary ⟨(e.observedIndex t ht).val + 1, by omega⟩ :=
  (e.mem_flowPartition _ _).mp (e.existsUnique_observed_piece t ht).choose_spec.1

/-- Reconstruct the observed signal using only the chosen positive flow.
Jump guards, resets and intermediate invariants remain execution obligations. -/
theorem signal_eq_observed_curve (t : σ.Time)
    (ht : t.val < e.boundary ⟨e.count, by omega⟩) (positive : 0 < t.val) :
    σ.value t = e.curve (e.observedIndex t ht)
      ⟨t.val - e.boundary ⟨(e.observedIndex t ht).val, by omega⟩, by
        have hs := e.observedIndex_spec t ht
        constructor
        · linarith [hs.1]
        · linarith [hs.2, e.duration_eq (e.observedIndex t ht)]⟩ :=
  e.signal_eq _ t (e.observedIndex_spec t ht) positive

end STLTableau.HybridAutomaton.Execution
