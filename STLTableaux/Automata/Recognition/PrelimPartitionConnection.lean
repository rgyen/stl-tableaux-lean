import STLTableaux.Automata.Execution.PrelimFlowRefinement
import STLTableaux.Automata.Execution.FlowSignalContinuity
import STLTableaux.Automata.Recognition.ForwardVisits
import STLTableaux.Automata.Execution.BoundedZeroTimeExtension

/-! Actual SYSTEM states at every marked partition cell, including
singletons. Each boundary connector is derived from the same execution:
an artificial cut is idle and an original boundary retains its jump block. -/
namespace STLTableau.HybridAutomaton.PrelimExecution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var} (e : H.PrelimExecution σ)

def stateAtTime (k : Fin e.count) (t : ℝ)
    (bounds : e.boundary k.castSucc ≤ t ∧ t ≤ e.boundary k.succ) : H.State :=
  (e.continuousStep k).stateAt ⟨t - e.boundary k.castSucc, by
    have duration : (e.duration k : ℝ) = e.boundary k.succ - e.boundary k.castSucc :=
      e.duration_eq k
    constructor <;> linarith⟩

theorem stateAtTime_congr {k l : Fin e.count} {s t : ℝ}
    (first : e.boundary k.castSucc ≤ s ∧ s ≤ e.boundary k.succ)
    (second : e.boundary l.castSucc ≤ t ∧ t ≤ e.boundary l.succ)
    (index : k = l) (time : s = t) :
    e.stateAtTime k s first = e.stateAtTime l t second := by
  cases index
  cases time
  rfl

theorem stateAtTime_start (k : Fin e.count) (t : ℝ) (bounds)
    (time : t = e.boundary k.castSucc) : e.stateAtTime k t bounds = e.start k := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change e.curve k _ = (e.start k).val.2
  refine (congrArg (e.curve k) ?_).trans (e.continuousStep k).2.1
  apply Subtype.ext
  change t - e.boundary k.castSucc = 0
  rw [time, sub_self]

theorem stateAtTime_finish (k : Fin e.count) (t : ℝ) (bounds)
    (time : t = e.boundary k.succ) : e.stateAtTime k t bounds = e.finish k := by
  apply Subtype.ext
  refine Prod.ext (e.continuousStep k).1 ?_
  change e.curve k _ = (e.finish k).val.2
  refine (congrArg (e.curve k) ?_).trans (e.continuousStep k).2.2.1
  apply Subtype.ext
  change t - e.boundary k.castSucc = (e.duration k : ℝ)
  rw [time]
  exact (e.duration_eq k).symm

variable (full : e.ReachesHorizon) (R : IntervalPartition σ.domain)
variable (fine : R.FinerThan (e.fullFlowPartition full))

/-- The cell's left endpoint belongs to the following actual system flow,
also when the cell itself is a singleton. -/
noncomputable def cellEntryState (i : Fin R.size) : H.State :=
  e.stateAtTime (e.cellOwner full R fine i) (R.interval i).left
    ⟨(e.cell_bounds full R fine i).1,
      (e.cell_entry_lt full R fine i).le⟩

/-- A positive cell retains its actual pre-jump closed flow endpoint.
A singleton's exit is its entry; no fictitious zero-duration flow is added. -/
noncomputable def cellExitState (i : Fin R.size) : H.State :=
  e.stateAtTime (e.cellOwner full R fine i) (R.interval i).right
    ⟨(e.cell_bounds full R fine i).1.trans (e.cell_bounds full R fine i).2.1,
      (e.cell_bounds full R fine i).2.2⟩

theorem refinedObservedFlow_states (i : Fin R.size)
    (positive : 0 < (STLTableau.Judgement.duration R i : ℝ)) :
    (e.refinedObservedFlow full R fine i positive).start = e.cellEntryState full R fine i ∧
    (e.refinedObservedFlow full R fine i positive).finish = e.cellExitState full R fine i :=
  ⟨rfl, rfl⟩

theorem singleton_cell_state (i : Fin R.size)
    (zero : (STLTableau.Judgement.duration R i : ℝ) = 0) :
    e.cellExitState full R fine i = e.cellEntryState full R fine i := by
  have time : (R.interval i).right = (R.interval i).left := by
    change (R.interval i).right - (R.interval i).left = 0 at zero
    linarith
  unfold cellExitState cellEntryState
  exact e.stateAtTime_congr _ _ rfl time

/-- Original system observations give the cell entry's value, including zero. -/
theorem cell_entry_signal (i : Fin R.size) :
    σ.value (Section4.Tableau.pieceEntry σ R i) = (e.cellEntryState full R fine i).val.2 := by
  exact e.signal_eq
    (e.cellOwner full R fine i) (Section4.Tableau.pieceEntry σ R i)
    ⟨(e.cell_bounds full R fine i).1, e.cell_entry_lt full R fine i⟩

/-- The actual refined flow observes the original physical signal from its
left endpoint, including time zero. -/
theorem refinedObservedFlow_observe
    (i : Fin R.size) (positive : 0 < (STLTableau.Judgement.duration R i : ℝ))
    (t : σ.Time) (u : Set.Icc (0 : ℝ) (e.refinedObservedFlow full R fine i positive).duration)
    (time : (R.interval i).left + u.val = t.val)
    (before : u.val < (e.refinedObservedFlow full R fine i positive).duration) :
    (e.refinedObservedFlow full R fine i positive).curve u = σ.value t := by
  let k := e.cellOwner full R fine i
  have duration : ((e.refinedObservedFlow full R fine i positive).duration : ℝ) =
      (R.interval i).right - (R.interval i).left := by
    have d := (e.refinedObservedFlow full R fine i positive).duration_eq
    rw [(e.refinedObservedFlow_endpoints full R fine i positive).1,
      (e.refinedObservedFlow_endpoints full R fine i positive).2] at d
    exact d
  have inside : e.boundary k.castSucc ≤ t.val ∧ t.val < e.boundary k.succ := by
    have bounds := e.cell_bounds full R fine i
    constructor <;> linarith [u.property.1]
  have obs := e.signal_eq k t inside
  refine Eq.trans ?_ obs.symm
  apply congrArg (e.curve k)
  apply Subtype.ext
  change (R.interval i).left - e.boundary k.castSucc + u.val = t.val - e.boundary k.castSucc
  linarith

theorem first_cell_entry (size : 0 < R.size) :
    e.cellEntryState full R fine ⟨0, size⟩ = e.start ⟨0, e.nonempty⟩ := by
  let i : Fin R.size := ⟨0, size⟩
  have time : (R.interval i).left = 0 := R.first_left_eq_domain_left size σ.horizon_pos
  have lower := (e.cell_bounds full R fine i).1
  have first : e.boundary 0 = 0 := e.first_zero
  have nonneg := e.increasing.monotone (Fin.zero_le (e.cellOwner full R fine i).castSucc)
  have boundary : e.boundary (e.cellOwner full R fine i).castSucc = 0 := by
    rw [time] at lower
    rw [first] at nonneg
    linarith
  have owner : e.cellOwner full R fine i = ⟨0, e.nonempty⟩ := by
    have same := e.increasing.injective (boundary.trans first.symm)
    have values := congrArg (fun k : Fin (e.count + 1) => k.val) same
    exact Fin.ext values
  exact (e.stateAtTime_start _ _ _ (time.trans boundary.symm)).trans (congrArg e.start owner)

/-- Adjacent marked cells never skip an original positive system flow. -/
theorem cell_owner_next (i j : Fin R.size) (adj : i.val + 1 = j.val) :
    e.cellOwner full R fine j = e.cellOwner full R fine i ∨
      (e.cellOwner full R fine j).val = (e.cellOwner full R fine i).val + 1 := by
  let a := e.cellOwner full R fine i
  let b := e.cellOwner full R fine j
  have join := R.adjacent_right_eq_left i (adj ▸ j.isLt)
  have index : (⟨i.val + 1, adj ▸ j.isLt⟩ : Fin R.size) = j := Fin.ext adj
  rw [index] at join
  have il := (e.cell_bounds full R fine i).1
  have ir := (e.cell_bounds full R fine i).2
  have jl := (e.cell_bounds full R fine j).1
  have jr := e.cell_entry_lt full R fine j
  have order : a.val ≤ b.val := by
    by_contra bad
    have h : b.succ ≤ a.castSucc := by change b.val + 1 ≤ a.val; omega
    have bound := e.increasing.monotone h
    change e.boundary b.succ ≤ e.boundary a.castSucc at bound
    linarith
  have upper : b.val ≤ a.val + 1 := by
    have bound : e.boundary b.castSucc ≤ e.boundary a.succ := by linarith
    have h := e.increasing.le_iff_le.mp bound
    exact h
  by_cases same : b.val = a.val
  · exact Or.inl (Fin.ext same)
  · exact Or.inr (by omega)

/-- Each boundary is either an artificial idle or exactly one original
interflow boundary. The original jump block is retained verbatim. -/
theorem cell_connector_cases (i j : Fin R.size) (adj : i.val + 1 = j.val) :
    e.cellExitState full R fine i = e.cellEntryState full R fine j ∨
      ∃ (k : Fin e.count) (live : k.val + 1 < e.count),
        e.cellExitState full R fine i = e.finish k ∧
        e.cellEntryState full R fine j = e.start ⟨k.val + 1, live⟩ := by
  have join := R.adjacent_right_eq_left i (adj ▸ j.isLt)
  have index : (⟨i.val + 1, adj ▸ j.isLt⟩ : Fin R.size) = j := Fin.ext adj
  rw [index] at join
  rcases e.cell_owner_next full R fine i j adj with same | next
  · have states : e.cellExitState full R fine i = e.cellEntryState full R fine j := by
      unfold cellExitState cellEntryState
      exact e.stateAtTime_congr _ _ same.symm join
    exact Or.inl states
  · let a := e.cellOwner full R fine i
    let b := e.cellOwner full R fine j
    have boundary : e.boundary a.succ = e.boundary b.castSucc :=
      congrArg e.boundary (Fin.ext next.symm)
    have atBoundary : (R.interval i).right = e.boundary a.succ := by
      have lower := (e.cell_bounds full R fine j).1
      have upper := (e.cell_bounds full R fine i).2.2
      rw [← boundary] at lower
      linarith
    have leave : e.cellExitState full R fine i = e.finish a :=
      e.stateAtTime_finish _ _ _ atBoundary
    have enter : e.cellEntryState full R fine j = e.start b :=
      e.stateAtTime_start _ _ _ (join.symm.trans (atBoundary.trans boundary))
    have live : a.val + 1 < e.count := by have := b.isLt; change b.val = a.val + 1 at next; omega
    have bIndex : b = ⟨a.val + 1, live⟩ := Fin.ext next
    exact Or.inr ⟨a, live, leave, bIndex ▸ enter⟩

/-- At a marked-cell boundary, either SYSTEM idles or the exact original
interflow jump block connects the two states. No tableau fact is assumed. -/
theorem cell_connector (i j : Fin R.size) (adj : i.val + 1 = j.val) :
    Relation.ReflTransGen H.DiscreteStep
      (e.cellExitState full R fine i) (e.cellEntryState full R fine j) := by
  rcases e.cell_connector_cases full R fine i j adj with idle | ⟨k, live, leave, enter⟩
  · exact idle ▸ Relation.ReflTransGen.refl
  · rw [leave, enter]
    exact (e.discreteSteps k live).to_reflTransGen

/-- A singleton consumes no SYSTEM action. Its two adjacent entry times
have the same right-owned system state. -/
theorem singleton_next_idle (i j : Fin R.size) (adj : i.val + 1 = j.val)
    (zero : (STLTableau.Judgement.duration R i : ℝ) = 0) :
    e.cellExitState full R fine i = e.cellEntryState full R fine j := by
  have join := R.adjacent_right_eq_left i (adj ▸ j.isLt)
  have index : (⟨i.val + 1, adj ▸ j.isLt⟩ : Fin R.size) = j := Fin.ext adj
  rw [index] at join
  rcases e.cell_owner_next full R fine i j adj with same | next
  · unfold cellExitState cellEntryState
    exact e.stateAtTime_congr _ _ same.symm join
  · have boundary : e.boundary (e.cellOwner full R fine i).succ =
        e.boundary (e.cellOwner full R fine j).castSucc :=
      congrArg e.boundary (Fin.ext next.symm)
    have lower := (e.cell_bounds full R fine j).1
    have before := e.cell_entry_lt full R fine i
    rw [← boundary] at lower
    change (R.interval i).right - (R.interval i).left = 0 at zero
    linarith

run_elab do
  for n in #[``cellEntryState, ``cellExitState, ``refinedObservedFlow_states,
      ``singleton_cell_state, ``cell_entry_signal, ``refinedObservedFlow_observe,
      ``first_cell_entry,
      ``cell_owner_next, ``cell_connector_cases, ``cell_connector, ``singleton_next_idle] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n}: unexpected axiom {ax}"

end STLTableau.HybridAutomaton.PrelimExecution
