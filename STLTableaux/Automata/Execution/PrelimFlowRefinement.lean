import STLTableaux.Automata.Execution.ExecutionTimeRefinement
import STLTableaux.Semantics.Partitions.PartitionRefinement
import STLTableaux.Semantics.Stability.Stability
import STLTableaux.Automata.Recognition.ExecutionPathTiming

/-! Select actual SYSTEM flow owners for every cell of a common refinement,
including singletons, and restrict their closed curves to positive cells.
The associated entry/exit states and connectors are proved separately. -/
namespace STLTableau.HybridAutomaton.PrelimExecution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var} (e : H.PrelimExecution σ)

/-- The actual system flow cells cover the signal only for a full witness. -/
def fullFlowPartition (full : e.ReachesHorizon) : IntervalPartition σ.domain :=
  { IntervalPartition.ofBoundaries e.boundary e.increasing with
    covers := by
      rw [(IntervalPartition.ofBoundaries e.boundary e.increasing).covers,
        e.first_zero, full]
      rfl }

noncomputable def cellOwner (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) : Fin e.count := Classical.choose (fine i)

theorem cell_subset (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) : (R.interval i).carrier ⊆
      ((e.fullFlowPartition full).interval (e.cellOwner full R fine i)).carrier :=
  Classical.choose_spec (fine i)

theorem cell_mem_bounds (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) {t : ℝ} (member : t ∈ (R.interval i).carrier) :
    e.boundary (e.cellOwner full R fine i).castSucc ≤ t ∧
      t < e.boundary (e.cellOwner full R fine i).succ := by
  have h := e.cell_subset full R fine i member
  simp only [fullFlowPartition, IntervalPartition.ofBoundaries,
    MarkedInterval.carrier_eq, Set.mem_Ico] at h
  exact ⟨h.1, h.2⟩

theorem cell_entry_lt (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) :
    (R.interval i).left < e.boundary (e.cellOwner full R fine i).succ := by
  obtain ⟨t, ht⟩ := R.nonempty i
  exact (MarkedInterval.left_le_of_mem ht).trans_lt (e.cell_mem_bounds full R fine i ht).2

theorem cell_bounds (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) :
    e.boundary (e.cellOwner full R fine i).castSucc ≤ (R.interval i).left ∧
      (R.interval i).left ≤ (R.interval i).right ∧
      (R.interval i).right ≤ e.boundary (e.cellOwner full R fine i).succ := by
  let k := e.cellOwner full R fine i
  obtain ⟨x, hx⟩ := R.nonempty i
  have xl := MarkedInterval.left_le_of_mem hx
  have xr := MarkedInterval.le_right_of_mem hx
  have xb := e.cell_mem_bounds full R fine i hx
  have inside : ∀ t, (R.interval i).left < t → t < (R.interval i).right →
      e.boundary k.castSucc ≤ t ∧ t < e.boundary k.succ := by
    intro t lower upper
    exact e.cell_mem_bounds full R fine i ⟨Or.inl lower, Or.inl upper⟩
  have lower : e.boundary k.castSucc ≤ (R.interval i).left := by
    by_contra bad
    have pos : (R.interval i).left < (R.interval i).right :=
      (lt_of_not_ge bad).trans_le (xb.1.trans xr)
    obtain ⟨t, ht, upper⟩ := exists_between (lt_min (lt_of_not_ge bad) pos)
    have h := (inside t ht (lt_min_iff.mp upper).2).1
    exact (not_lt_of_ge h) (lt_min_iff.mp upper).1
  have upper : (R.interval i).right ≤ e.boundary k.succ := by
    by_contra bad
    have pos : (R.interval i).left < (R.interval i).right :=
      (xl.trans_lt xb.2).trans (lt_of_not_ge bad)
    obtain ⟨t, ht, upper⟩ := exists_between (max_lt pos (lt_of_not_ge bad))
    have h := (inside t (max_lt_iff.mp ht).1 upper).2
    exact (not_lt_of_ge (max_lt_iff.mp ht).2.le) h
  exact ⟨lower, xl.trans xr, upper⟩

/-- Restrict the selected owner, retaining the same owner for connectors. -/
noncomputable def refinedObservedFlow (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) (positive : 0 < (STLTableau.Judgement.duration R i : ℝ)) :
    ObservedFlow H σ :=
  (e.observedFlow (e.cellOwner full R fine i)).sliceAt _ _
    ⟨(e.cell_bounds full R fine i).1, by
      change 0 < (R.interval i).right - (R.interval i).left at positive
      linarith, (e.cell_bounds full R fine i).2.2⟩

theorem refinedObservedFlow_endpoints (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) (positive : 0 < (STLTableau.Judgement.duration R i : ℝ)) :
    (e.refinedObservedFlow full R fine i positive).beginTime = (R.interval i).left ∧
    (e.refinedObservedFlow full R fine i positive).endTime = (R.interval i).right :=
  ⟨(e.observedFlow (e.cellOwner full R fine i)).sliceAt_begin _ _ _,
    (e.observedFlow (e.cellOwner full R fine i)).sliceAt_end _ _ _⟩

theorem exists_observedFlow_of_finer (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) (positive : 0 < (STLTableau.Judgement.duration R i : ℝ)) :
    ∃ f : ObservedFlow H σ,
      f.beginTime = (R.interval i).left ∧ f.endTime = (R.interval i).right :=
  ⟨e.refinedObservedFlow full R fine i positive,
    e.refinedObservedFlow_endpoints full R fine i positive⟩

/-- Refine before obtaining a tableau run, retaining full formula stability. -/
theorem exists_common_stable_flow_refinement (full : e.ReachesHorizon)
    (P : IntervalPartition σ.domain) (φ : Formula Var)
    (stable : σ.StablePartition φ P) :
    ∃ R : IntervalPartition σ.domain, R.FinerThan P ∧
      R.FinerThan (e.fullFlowPartition full) ∧ σ.StablePartition φ R := by
  obtain ⟨R, first, second, _⟩ := P.exists_common_refinement (e.fullFlowPartition full)
  exact ⟨R, first, second, stable.of_finer first⟩

run_elab do
  for n in #[``fullFlowPartition, ``exists_observedFlow_of_finer,
      ``cellOwner, ``cell_subset, ``cell_mem_bounds, ``cell_bounds, ``cell_entry_lt,
      ``refinedObservedFlow, ``refinedObservedFlow_endpoints,
      ``exists_common_stable_flow_refinement] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n}: unexpected axiom {ax}"

end STLTableau.HybridAutomaton.PrelimExecution
