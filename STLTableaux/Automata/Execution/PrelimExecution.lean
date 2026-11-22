import STLTableaux.Automata.Execution.HybridAutomata
import STLTableaux.Semantics.Partitions.BoundaryPartition

/-! Execution prefixes end with a positive flow and observe the signal on the
half-open interval up to the cut. Full system trajectories observe the signal
through its horizon. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*}

/-- A prefix ends with its last positive flow. Goal visits may occur before
the horizon; full trajectory membership separately requires reaching it. -/
structure PrelimExecution (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) where
  count : ℕ
  nonempty : 0 < count
  initialState : H.State
  initial_mem : initialState.val ∈ H.initial
  start : Fin count → H.State
  finish : Fin count → H.State
  boundary : Fin (count + 1) → ℝ
  first_zero : boundary ⟨0, by omega⟩ = 0
  increasing : StrictMono boundary
  last_le_horizon : boundary ⟨count, by omega⟩ ≤ σ.horizon
  duration : Fin count → NNReal
  duration_eq : ∀ i, (duration i : ℝ) =
    boundary ⟨i.val + 1, by omega⟩ - boundary ⟨i.val, by omega⟩
  curve : ∀ i, Set.Icc (0 : ℝ) (duration i) → Var → ℝ
  continuousStep : ∀ i, H.ContinuousStep (start i) (finish i) (duration i) (curve i)
  initialSteps : Relation.ReflTransGen H.DiscreteStep initialState (start ⟨0, nonempty⟩)
  discreteSteps : ∀ (i : Fin count) (hi : i.val + 1 < count),
    Relation.TransGen H.DiscreteStep (finish i) (start ⟨i.val + 1, hi⟩)
  /-- Each flow supplies the signal on its left-closed, right-open time
  interval. In particular, time zero is read after the initial jump block. -/
  signal_eq : ∀ (i : Fin count) (t : σ.Time)
    (ht : boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val < boundary ⟨i.val + 1, by omega⟩),
    σ.value t = curve i ⟨t.val - boundary ⟨i.val, by omega⟩,
      by
        constructor
        · linarith [ht.1]
        · linarith [ht.2, duration_eq i]⟩

namespace PrelimExecution
variable {H : HybridAutomaton Mode Label Var} {σ : FiniteSignal Var}

def lastIndex (e : H.PrelimExecution σ) : Fin e.count :=
  ⟨e.count - 1, by have := e.nonempty; omega⟩

/-- No separately chosen post-jump state exists at the end of the witness. -/
def finalState (e : H.PrelimExecution σ) : H.State := e.finish e.lastIndex

/-- A whole-signal witness reaches the horizon, not merely a shorter prefix. -/
def ReachesHorizon (e : H.PrelimExecution σ) : Prop :=
  e.boundary ⟨e.count, by omega⟩ = σ.horizon

theorem signal_at_zero_curve (e : H.PrelimExecution σ) :
    σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = e.curve ⟨0, e.nonempty⟩ ⟨0, by simp⟩ := by
  let i : Fin e.count := ⟨0, e.nonempty⟩
  have zero : e.boundary i.castSucc = 0 := e.first_zero
  have upper : 0 < e.boundary i.succ :=
    zero ▸ e.increasing (show i.castSucc < i.succ by simp)
  refine (e.signal_eq i ⟨0, le_rfl, σ.horizon_pos⟩ ⟨zero.le, upper⟩).trans ?_
  apply congrArg (e.curve i)
  exact Subtype.ext (by change 0 - e.boundary i.castSucc = 0; rw [zero, sub_self])

theorem signal_at_zero (e : H.PrelimExecution σ) :
    σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = (e.start ⟨0, e.nonempty⟩).val.2 :=
  e.signal_at_zero_curve.trans (e.continuousStep ⟨0, e.nonempty⟩).2.1

/-- The system invariant constrains every actually observed signal value. -/
theorem invariant_at (e : H.PrelimExecution σ) (t : σ.Time)
    (observed : t.val < e.boundary ⟨e.count, by omega⟩) :
    ∃ q, (q, σ.value t) ∈ H.invariant := by
  have between : t.val ∈ Set.Ico (e.boundary 0) (e.boundary ⟨e.count, by omega⟩) :=
    ⟨by
      change e.boundary ⟨0, by omega⟩ ≤ t.val
      rw [e.first_zero]
      exact t.property.1, observed⟩
  obtain ⟨i, lower, upper⟩ := IntervalPartition.exists_boundary_piece e.boundary between
  refine ⟨(e.start i).val.1, ?_⟩
  rw [e.signal_eq i t ⟨lower, upper⟩]
  exact ((e.continuousStep i).2.2.2 _).2

theorem duration_pos (e : H.PrelimExecution σ) (i : Fin e.count) :
    0 < (e.duration i : ℝ) := by
  rw [e.duration_eq]
  exact sub_pos.mpr (e.increasing (show i.castSucc < i.succ by simp))

/-- Every flow starts strictly before the horizon, even if its endpoint is τ. -/
theorem entry_lt_horizon (e : H.PrelimExecution σ) (i : Fin e.count) :
    e.boundary i.castSucc < σ.horizon := by
  exact (e.increasing (show i.castSucc < Fin.last e.count by simp)).trans_le e.last_le_horizon

theorem no_entry_at_horizon (e : H.PrelimExecution σ) (i : Fin e.count) :
    e.boundary i.castSucc ≠ σ.horizon := (e.entry_lt_horizon i).ne

/-- Interflow jump blocks precede the following positive flow. -/
theorem interflow_time_lt_horizon (e : H.PrelimExecution σ) (i : Fin e.count)
    (hi : i.val + 1 < e.count) :
    e.boundary i.succ < σ.horizon := by
  exact e.entry_lt_horizon ⟨i.val + 1, hi⟩

theorem final_mode_eq_last_start (e : H.PrelimExecution σ) :
    e.finalState.val.1 = (e.start e.lastIndex).val.1 :=
  (e.continuousStep e.lastIndex).1.symm

/-- The final mode was already present when the last positive flow started. -/
theorem final_mode_entered_before_horizon (e : H.PrelimExecution σ) :
    e.boundary e.lastIndex.castSucc < σ.horizon ∧
      (e.start e.lastIndex).val.1 = e.finalState.val.1 :=
  ⟨e.entry_lt_horizon _, e.final_mode_eq_last_start.symm⟩

/-- Includes modes skipped within initial and interflow jump blocks.
There is no jump block after the last flow. Splitting a block at a state
is an existential choice of a witnessing transition sequence. -/
def VisitsMode (e : H.PrelimExecution σ) (q : Mode) : Prop :=
  (∃ i, (e.start i).val.1 = q) ∨
  (∃ s : H.State, s.val.1 = q ∧
    Relation.ReflTransGen H.DiscreteStep e.initialState s ∧
    Relation.ReflTransGen H.DiscreteStep s (e.start ⟨0, e.nonempty⟩)) ∨
  ∃ (i : Fin e.count) (hi : i.val + 1 < e.count) (s : H.State),
    s.val.1 = q ∧
    Relation.ReflTransGen H.DiscreteStep (e.finish i) s ∧
    Relation.ReflTransGen H.DiscreteStep s (e.start ⟨i.val + 1, hi⟩)

theorem visits_final_mode (e : H.PrelimExecution σ) :
    e.VisitsMode e.finalState.val.1 :=
  Or.inl ⟨e.lastIndex, e.final_mode_eq_last_start.symm⟩
end PrelimExecution

/-- The execution observes the signal up to the end of its last continuous
transition. This transition can end before the signal horizon. -/
def IsPrelimPrefix (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) : Prop :=
  Nonempty (H.PrelimExecution σ)

/-- A system trajectory for the model-checking reduction realizes the signal
through its entire time horizon. -/
def IsPrelimTrajectory (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) : Prop :=
  ∃ e : H.PrelimExecution σ, e.ReachesHorizon

theorem IsPrelimTrajectory.isPrefix {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (trajectory : H.IsPrelimTrajectory σ) : H.IsPrelimPrefix σ := by
  obtain ⟨e, _⟩ := trajectory
  exact ⟨e⟩

/-- No unobserved suffix remains in a system trajectory. -/
theorem IsPrelimTrajectory.invariant_at {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (trajectory : H.IsPrelimTrajectory σ) (t : σ.Time) :
    ∃ q, (q, σ.value t) ∈ H.invariant := by
  obtain ⟨e, full⟩ := trajectory
  apply e.invariant_at t
  rw [full]
  exact t.property.2

/-- Reaching a goal requires no additional jump out of the goal. -/
def PrelimReaches (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var)
    (goal : Set Mode) : Prop :=
  ∃ e : H.PrelimExecution σ, ∃ q ∈ goal, e.VisitsMode q

theorem PrelimExecution.reaches_of_final_mode
    {H : HybridAutomaton Mode Label Var} {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) {goal : Set Mode} (hg : e.finalState.val.1 ∈ goal) :
    H.PrelimReaches σ goal :=
  ⟨e, e.finalState.val.1, hg, e.visits_final_mode⟩

theorem PrelimExecution.reaches_of_flow_mode
    {H : HybridAutomaton Mode Label Var} {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (i : Fin e.count) {goal : Set Mode}
    (hg : (e.start i).val.1 ∈ goal) : H.PrelimReaches σ goal :=
  ⟨e, (e.start i).val.1, hg, Or.inl ⟨i, rfl⟩⟩

/-- Form a preliminary execution from the continuous segments when the
observation at zero agrees with the first flow. -/
def Execution.toPrelimExecution {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ)
    (zero : σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = (e.start ⟨0, e.nonempty⟩).val.2) :
    H.PrelimExecution σ where
  count := e.count
  nonempty := e.nonempty
  initialState := e.initialState
  initial_mem := e.initial_mem
  start := e.start
  finish := e.finish
  boundary := e.boundary
  first_zero := e.first_zero
  increasing := e.increasing
  last_le_horizon := e.last_le_horizon
  duration := e.duration
  duration_eq := e.duration_eq
  curve := e.curve
  continuousStep := e.continuousStep
  initialSteps := e.initialSteps
  discreteSteps := e.discreteSteps
  signal_eq := by
    intro i t ht
    rcases eq_or_lt_of_le t.property.1 with atZero | positive
    · have lower := e.increasing.monotone (Fin.zero_le i.castSucc)
      have atStart : e.boundary i.castSucc = 0 :=
        le_antisymm (ht.1.trans_eq atZero.symm) (e.first_zero.ge.trans lower)
      have idx : i = ⟨0, e.nonempty⟩ := by
        apply Fin.ext
        have same := e.increasing.injective (atStart.trans e.first_zero.symm)
        exact congrArg (fun k : Fin (e.count + 1) => k.val) same
      have tZero : t = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext atZero.symm
      have uZero : t.val - e.boundary i.castSucc = 0 := by rw [← atZero, atStart, sub_self]
      calc
        σ.value t = (e.start i).val.2 := by rw [tZero, idx]; exact zero
        _ = _ := (e.continuousStep i).2.1.symm.trans
          (congrArg (e.curve i) (Subtype.ext uZero.symm))
    · exact e.signal_eq i t ht positive

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``PrelimExecution.signal_at_zero_curve, ``PrelimExecution.signal_at_zero,
      ``PrelimExecution.invariant_at, ``IsPrelimTrajectory.isPrefix,
      ``IsPrelimTrajectory.invariant_at, ``PrelimExecution.duration_pos,
      ``PrelimExecution.entry_lt_horizon,
      ``PrelimExecution.no_entry_at_horizon, ``PrelimExecution.interflow_time_lt_horizon,
      ``PrelimExecution.final_mode_entered_before_horizon,
      ``PrelimExecution.reaches_of_final_mode, ``PrelimExecution.reaches_of_flow_mode] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.HybridAutomaton
