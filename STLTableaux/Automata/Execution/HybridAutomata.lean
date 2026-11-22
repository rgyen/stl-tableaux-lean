import STLTableaux.Automata.Execution.HybridTrajectory

/-! Hybrid automata and executions with an optional final sequence of jumps.
At an early stopping time, `Execution` observes the state after those jumps.
`PrelimExecution` describes executions ending with a continuous transition. -/
namespace STLTableau

structure HybridAutomaton (Mode Label Var : Type*) where
  modes_finite : Finite Mode
  variables_finite : Finite Var
  edge : Set (Mode × Label × Mode)
  initial : Set (Mode × (Var → ℝ))
  invariant : Set (Mode × (Var → ℝ))
  flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop
  /-- Standard trajectory closure (T2 and finite T3); T1 follows from flow.
  This is automaton well-formedness, not an STL-specific premise. -/
  trajectory_closed : HybridFlow.Closed flow invariant
  jump : {e // e ∈ edge} → (Mode × (Var → ℝ)) → (Mode × (Var → ℝ)) → Prop

namespace HybridAutomaton
variable {Mode Label Var : Type*}

/-- Only invariant-satisfying pairs are semantic states. -/
def State (H : HybridAutomaton Mode Label Var) := {s // s ∈ H.invariant}

/-- A segment is defined on the closed duration interval.
Its flow may be discontinuous. -/
def ContinuousStep (H : HybridAutomaton Mode Label Var)
    (s s' : H.State) (r : NNReal) (γ : Set.Icc (0 : ℝ) r → Var → ℝ) : Prop :=
  s.val.1 = s'.val.1 ∧ γ ⟨0, by simp⟩ = s.val.2 ∧
    γ ⟨r, by simp⟩ = s'.val.2 ∧
    ∀ t, H.flow s.val ⟨t.val, t.property.1⟩ (γ t) ∧
      (s.val.1, γ t) ∈ H.invariant

theorem ContinuousStep.evolves {H : HybridAutomaton Mode Label Var}
    {a b : H.State} {r : NNReal} {γ : HybridFlow.Curve Var r}
    (step : H.ContinuousStep a b r γ) : HybridFlow.Evolves H.flow H.invariant a.val.1 γ := by
  intro t
  rw [step.2.1]
  exact step.2.2.2 t

def ContinuousStep.stateAt {H : HybridAutomaton Mode Label Var}
    {a b : H.State} {r : NNReal} {γ : HybridFlow.Curve Var r}
    (step : H.ContinuousStep a b r γ) (t : Set.Icc (0 : ℝ) r) : H.State :=
  ⟨(a.val.1, γ t), (step.2.2.2 t).2⟩

theorem ContinuousStep.prefixStep {H : HybridAutomaton Mode Label Var}
    {a b : H.State} {r : NNReal} {γ : HybridFlow.Curve Var r}
    (step : H.ContinuousStep a b r γ) (s : NNReal) (hs : s ≤ r) :
    H.ContinuousStep a (step.stateAt ⟨s, by simp [hs]⟩) s
      (HybridFlow.prefixCurve γ s hs) := by
  refine ⟨rfl, step.2.1, rfl, ?_⟩
  intro t
  exact step.2.2.2 ⟨t.val, t.property.1, t.property.2.trans hs⟩

theorem ContinuousStep.suffixStep {H : HybridAutomaton Mode Label Var}
    {a b : H.State} {r : NNReal} {γ : HybridFlow.Curve Var r}
    (step : H.ContinuousStep a b r γ) (s : NNReal) (hs : s ≤ r) :
    H.ContinuousStep (step.stateAt ⟨s, by simp [hs]⟩) b (r - s)
      (HybridFlow.suffixCurve γ s hs) := by
  have start : HybridFlow.suffixCurve γ s hs ⟨0, by simp⟩ = γ ⟨s, by simp [hs]⟩ := by
    apply congrArg γ
    exact Subtype.ext (by simp)
  have finish : HybridFlow.suffixCurve γ s hs
      ⟨((r - s : NNReal) : ℝ), (r - s).coe_nonneg, le_rfl⟩ =
      γ ⟨r, r.coe_nonneg, le_rfl⟩ := by
    apply congrArg γ
    apply Subtype.ext
    change (s : ℝ) + ((r - s : NNReal) : ℝ) = r
    rw [NNReal.coe_sub hs]
    ring
  refine ⟨step.1, start, finish.trans step.2.2.1, ?_⟩
  intro t
  have result := H.trajectory_closed.suffix step.evolves s hs t
  rw [start] at result
  exact result

def DiscreteStep (H : HybridAutomaton Mode Label Var) (s s' : H.State) : Prop :=
  ∃ e : {e // e ∈ H.edge}, e.val.1 = s.val.1 ∧ e.val.2.2 = s'.val.1 ∧
    H.jump e s.val s'.val

/-- Endpoint-aware execution used in the visit and trace lemmas.
A finite sequence of positive-duration continuous segments, with arbitrary
initial discrete steps and at least one discrete step between segments.
An optional final sequence of discrete steps takes no additional time.
At time zero the signal reads the state before the initial discrete steps. -/
structure Execution (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) where
  count : ℕ
  nonempty : 0 < count
  initialState : H.State
  initial_mem : initialState.val ∈ H.initial
  initial_signal_eq : σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = initialState.val.2
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
  finalState : H.State
  finalSteps : Relation.ReflTransGen H.DiscreteStep
    (finish ⟨count - 1, by omega⟩) finalState
  /-- If the stopping time is in the signal domain, observe the state after
  all final jumps. At the horizon there is no such `t`, so this is vacuous. -/
  final_signal_eq : ∀ (t : σ.Time), t.val = boundary ⟨count, by omega⟩ →
    σ.value t = finalState.val.2
  signal_eq : ∀ (i : Fin count) (t : σ.Time)
    (ht : boundary ⟨i.val, by omega⟩ ≤ t.val ∧
      t.val < boundary ⟨i.val + 1, by omega⟩) (_positive : 0 < t.val),
    σ.value t = curve i ⟨t.val - boundary ⟨i.val, by omega⟩,
      by
        constructor
        · linarith [ht.1]
        · linarith [ht.2, duration_eq i]⟩

def IsTrajectory (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var) : Prop :=
  Nonempty (H.Execution σ)

/-- Reachability at the endpoint, including the optional final discrete tail.
No positive residence time in the goal mode is required. -/
def Reaches (H : HybridAutomaton Mode Label Var) (σ : FiniteSignal Var)
    (goal : Set Mode) : Prop :=
  ∃ e : H.Execution σ, e.finalState.val.1 ∈ goal

/-- Extend only the discrete tail. Its new endpoint must agree with the same
signal when stopping early; this obligation is vacuous at the horizon. -/
def Execution.appendFinalSteps {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (s : H.State)
    (h : Relation.ReflTransGen H.DiscreteStep e.finalState s)
    (hobs : ∀ t : σ.Time, t.val = e.boundary ⟨e.count, by omega⟩ →
      σ.value t = s.val.2) : H.Execution σ :=
  { e with finalState := s, finalSteps := e.finalSteps.trans h, final_signal_eq := hobs }

theorem Execution.reaches_of_finalSteps {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) {s : H.State} {goal : Set Mode}
    (h : Relation.ReflTransGen H.DiscreteStep e.finalState s)
    (hobs : ∀ t : σ.Time, t.val = e.boundary ⟨e.count, by omega⟩ →
      σ.value t = s.val.2)
    (hg : s.val.1 ∈ goal) : H.Reaches σ goal :=
  ⟨e.appendFinalSteps s h hobs, hg⟩

/-- Horizon-ending tails need no value at `σ(τ)`: the signal domain is half-open. -/
def Execution.appendFinalStepsAtHorizon {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var} (e : H.Execution σ) (s : H.State)
    (h : Relation.ReflTransGen H.DiscreteStep e.finalState s)
    (hend : e.boundary ⟨e.count, by omega⟩ = σ.horizon) : H.Execution σ :=
  e.appendFinalSteps s h (by
    intro t ht
    have hlt := t.property.2
    rw [ht, hend] at hlt
    exact (lt_irrefl _ hlt).elim)

/-- Apply the proposed horizon boundary convention to an underlying automaton.
`terminal` denotes the modes carrying `*`, not all accepting modes.
The underlying invariant must not retain the old strict horizon conjunct.
The underlying jump must separately preserve the global clock; this wrapper
does not change resets or flow. This is not the full tableau translation. -/
def withHorizon (H : HybridAutomaton Mode Label Var)
    (terminal : Set Mode) (c : Var) (τ : ℝ) : HybridAutomaton Mode Label Var where
  modes_finite := H.modes_finite
  variables_finite := H.variables_finite
  edge := H.edge
  initial := H.initial
  invariant := {s | s ∈ H.invariant ∧ (s.1 ∉ terminal → s.2 c ≤ τ)}
  flow := H.flow
  trajectory_closed := H.trajectory_closed.strengthen
    (fun s => s.1 ∉ terminal → s.2 c ≤ τ)
  jump := fun e s s' => H.jump e s s' ∧
    (s'.1 ∈ terminal → τ ≤ s'.2 c) ∧
    (s'.1 ∉ terminal → s'.2 c < τ)

theorem withHorizon_nonterminal_entry_lt
    (H : HybridAutomaton Mode Label Var) (terminal : Set Mode) (c : Var) (τ : ℝ)
    {s s' : (H.withHorizon terminal c τ).State}
    (h : (H.withHorizon terminal c τ).DiscreteStep s s')
    (hn : s'.val.1 ∉ terminal) : s'.val.2 c < τ := by
  obtain ⟨e, _, _, hj⟩ := h
  exact hj.2.2 hn

/-- A clock-preserving jump from an ordinary mode into `*` occurs exactly
at the horizon, rather than strictly after it. -/
theorem withHorizon_terminal_entry_eq
    (H : HybridAutomaton Mode Label Var) (terminal : Set Mode) (c : Var) (τ : ℝ)
    {s s' : (H.withHorizon terminal c τ).State}
    (h : (H.withHorizon terminal c τ).DiscreteStep s s')
    (hs : s.val.1 ∉ terminal) (ht : s'.val.1 ∈ terminal)
    (hc : s'.val.2 c = s.val.2 c) : s'.val.2 c = τ := by
  obtain ⟨e, _, _, hj⟩ := h
  exact le_antisymm (hc ▸ s.property.2 hs) (hj.2.1 ht)

end HybridAutomaton
end STLTableau
