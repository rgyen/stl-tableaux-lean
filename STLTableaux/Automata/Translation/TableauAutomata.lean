import STLTableaux.Tableau.Construction.Tableau
import STLTableaux.Automata.Execution.HybridAutomata

/-! Tableau-to-automaton construction with the approved horizon convention.
Only declared variables, clocks and states become automaton coordinates.
No recognition/trajectory equivalence is asserted in this module. -/
namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*}

/-- Disjoint coordinates enforce freshness of the global clock. -/
abbrev HAVar (T : Tableau Clock Var State) :=
  Sum T.realVariables (Sum T.clocks Unit)

def globalClock (T : Tableau Clock Var State) : T.HAVar := .inr (.inr ())

/-- Guards are interpreted over real coordinates, without truncating negatives. -/
def realComparison : ClockRelation → ℝ → ℝ → Prop
  | .ge => (· ≥ ·)
  | .gt => (· > ·)
  | .eq => (· = ·)
  | .lt => (· < ·)
  | .le => (· ≤ ·)

def guardsHold (T : Tableau Clock Var State) (l : EdgeLabel Clock)
    (v : T.HAVar → ℝ) : Prop :=
  ∀ g ∈ l.guards, ∃ hc : g.clock ∈ T.clocks,
    realComparison g.relation (v (.inr (.inl ⟨g.clock, hc⟩))) g.bound

def reset (T : Tableau Clock Var State) (Λ : ClockResetSet Clock)
    (v : T.HAVar → ℝ) : T.HAVar → ℝ
  | .inl x => v (.inl x)
  | .inr (.inl c) => match Λ.value c.val with
    | some a => a
    | none => v (.inr (.inl c))
  | .inr (.inr u) => v (.inr (.inr u))

/-- Initial reset additionally sets the fresh clock to zero. -/
def initialReset (T : Tableau Clock Var State) (Λ : ClockResetSet Clock)
    (v : T.HAVar → ℝ) : T.HAVar → ℝ
  | .inr (.inr _) => 0
  | x => T.reset Λ v x

/-- Evaluate atoms only on their explicitly declared arguments. -/
def atomHolds (T : Tableau Clock Var State) (a : AtomicProposition Var)
    (v : T.HAVar → ℝ) : Prop :=
  ∃ h : ∀ i, a.arguments i ∈ T.realVariables,
    a.relation.Holds (a.function fun i => v (.inl ⟨a.arguments i, h i⟩)) 0

/-- Explicit well-formedness obligations for a finite tuple. They must be
discharged for the concrete generated tableau, not assumed by correctness. -/
structure TranslationReady (T : Tableau Clock Var State) : Prop where
  states_finite : T.states.Finite
  variables_finite : T.realVariables.Finite
  clocks_finite : T.clocks.Finite
  edge_states : ∀ e ∈ T.edges, e.1 ∈ T.states ∧ e.2.2 ∈ T.states
  initial_states : ∀ e ∈ T.initial, e.2 ∈ T.states
  final_states : T.final ⊆ T.states
  edge_guards : ∀ e ∈ T.edges, ∀ g ∈ e.2.1.guards, g.clock ∈ T.clocks
  initial_guards : ∀ e ∈ T.initial, ∀ g ∈ e.1.guards, g.clock ∈ T.clocks
  edge_resets : ∀ e ∈ T.edges, e.2.1.resets.clocks ⊆ T.clocks
  initial_resets : ∀ e ∈ T.initial, e.1.resets.clocks ⊆ T.clocks
  atom_variables : ∀ q ∈ T.states, ∀ a,
    Local.predicate (.plain (.atom a)) ∈ T.label q →
    ∀ i, a.arguments i ∈ T.realVariables

def terminalModes (T : Tableau Clock Var State) : Set T.states :=
  {q | Local.terminal ∈ T.label q.val}

def goalModes (T : Tableau Clock Var State) : Set T.states :=
  {q | q.val ∈ T.final}

/-- The clock-independent part of the construction. Signal coordinates have
no flow restriction; resets preserve them and the fresh global clock. -/
def baseAutomaton (T : Tableau Clock Var State) (h : T.TranslationReady) :
    HybridAutomaton T.states (EdgeLabel Clock) T.HAVar where
  modes_finite := h.states_finite.to_subtype
  variables_finite := by
    letI := h.variables_finite.to_subtype
    letI := h.clocks_finite.to_subtype
    infer_instance
  edge := {e | (e.1.val, e.2.1, e.2.2.val) ∈ T.edges}
  initial := {s | ∃ l, (l, s.1.val) ∈ T.initial ∧
    ∃ v, T.guardsHold l v ∧ s.2 = T.initialReset l.resets v}
  invariant := {s | ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label s.1.val →
    T.atomHolds a s.2}
  flow := fun s t v =>
    (∀ c : T.clocks, v (.inr (.inl c)) = s.2 (.inr (.inl c)) + t) ∧
    v T.globalClock = s.2 T.globalClock + t
  trajectory_closed := by
    apply HybridFlow.Closed.of_rebase_add
    · intro q v a b r s first total
      dsimp only [Prod.snd] at *
      refine ⟨?_, ?_⟩
      · intro c
        rw [total.1 c, first.1 c]
        push_cast
        ring
      · rw [total.2, first.2]
        push_cast
        ring
    · intro q v a b r s first second
      dsimp only [Prod.snd] at *
      refine ⟨?_, ?_⟩
      · intro c
        rw [second.1 c, first.1 c]
        push_cast
        ring
      · rw [second.2, first.2]
        push_cast
        ring
  jump := fun e s s' =>
    s.1 = e.val.1 ∧ s'.1 = e.val.2.2 ∧
    T.guardsHold e.val.2.1 s.2 ∧ s'.2 = T.reset e.val.2.1.resets s.2

/-- Apply the horizon conditions to the base automaton at a positive horizon. -/
def toAutomaton (T : Tableau Clock Var State) (h : T.TranslationReady)
    (τ : ℝ) (_hτ : 0 < τ) :
    HybridAutomaton T.states (EdgeLabel Clock) T.HAVar :=
  (T.baseAutomaton h).withHorizon T.terminalModes T.globalClock τ

@[simp] theorem reset_globalClock (T : Tableau Clock Var State)
    (Λ : ClockResetSet Clock) (v : T.HAVar → ℝ) :
    T.reset Λ v T.globalClock = v T.globalClock := rfl

@[simp] theorem reset_realVariable (T : Tableau Clock Var State)
    (Λ : ClockResetSet Clock) (v : T.HAVar → ℝ) (x : T.realVariables) :
    T.reset Λ v (.inl x) = v (.inl x) := rfl

theorem realComparison_coe (r : ClockRelation) (x y : NNReal) :
    realComparison r x y ↔ r.Holds x y := by
  cases r <;> simp [realComparison, ClockRelation.Holds]

/-- The real-valued guard interpretation agrees with tableau guards on
nonnegative clock valuations. -/
theorem guardsHold_iff (T : Tableau Clock Var State) (l : EdgeLabel Clock)
    (v : T.HAVar → ℝ) (α : ClockValuation Clock)
    (hsupport : ∀ g ∈ l.guards, g.clock ∈ T.clocks)
    (hv : ∀ c : T.clocks, v (.inr (.inl c)) = (α c.val : ℝ)) :
    T.guardsHold l v ↔ ∀ g ∈ l.guards, g.holds α := by
  constructor
  · intro h g hg
    obtain ⟨hc, hr⟩ := h g hg
    rw [hv] at hr
    exact (realComparison_coe _ _ _).mp hr
  · intro h g hg
    refine ⟨hsupport g hg, ?_⟩
    rw [hv]
    exact (realComparison_coe _ _ _).mpr (h g hg)

theorem reset_clock_agrees (T : Tableau Clock Var State)
    (Λ : ClockResetSet Clock) (v : T.HAVar → ℝ) (α : ClockValuation Clock)
    (hv : ∀ c : T.clocks, v (.inr (.inl c)) = (α c.val : ℝ))
    (c : T.clocks) :
    T.reset Λ v (.inr (.inl c)) = (Λ.apply α c.val : ℝ) := by
  cases hc : Λ.value c.val with
  | none => simpa only [reset, ClockResetSet.apply, hc] using hv c
  | some a => simp only [reset, ClockResetSet.apply, hc]

theorem atomHolds_iff (T : Tableau Clock Var State) (a : AtomicProposition Var)
    (v : T.HAVar → ℝ) (w : Var → ℝ)
    (hsupport : ∀ i, a.arguments i ∈ T.realVariables)
    (hv : ∀ x : T.realVariables, v (.inl x) = w x.val) :
    T.atomHolds a v ↔ a.Holds w := by
  constructor
  · rintro ⟨h, ha⟩
    simpa only [hv, AtomicProposition.Holds] using ha
  · intro ha
    refine ⟨hsupport, ?_⟩
    simpa only [hv, AtomicProposition.Holds] using ha

theorem initial_globalClock_zero (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s} (hs : s ∈ (T.toAutomaton h τ hτ).initial) : s.2 T.globalClock = 0 := by
  obtain ⟨l, _, v, _, hv⟩ := hs
  rw [hv]
  rfl

theorem jump_globalClock_preserved (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s') :
    s'.val.2 T.globalClock = s.val.2 T.globalClock := by
  obtain ⟨e, _, _, he⟩ := hj
  have hr := he.1.2.2.2
  rw [hr]
  rfl

theorem jump_realVariable_preserved (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s') (x : T.realVariables) :
    s'.val.2 (.inl x) = s.val.2 (.inl x) := by
  obtain ⟨e, _, _, he⟩ := hj
  rw [he.1.2.2.2]
  rfl

theorem nonterminal_entry_lt_horizon (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s')
    (ht : s'.val.1 ∉ T.terminalModes) : s'.val.2 T.globalClock < τ :=
  (T.baseAutomaton h).withHorizon_nonterminal_entry_lt _ _ _ hj ht

theorem flow_globalClock (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s t v} (hf : (T.toAutomaton h τ hτ).flow s t v) :
    v T.globalClock = s.2 T.globalClock + t := hf.2

theorem terminal_entry_eq_horizon (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hs : s.val.1 ∉ T.terminalModes) (ht : s'.val.1 ∈ T.terminalModes) :
    s'.val.2 T.globalClock = τ :=
  (T.baseAutomaton h).withHorizon_terminal_entry_eq _ _ _ hj hs ht
    (T.jump_globalClock_preserved h τ hτ hj)

/-- Any finite zero-time tail preserves the fresh clock, not just one jump. -/
theorem discreteSteps_globalClock_preserved (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s') :
    s'.val.2 T.globalClock = s.val.2 T.globalClock := by
  induction hj with
  | refl => rfl
  | tail _ hstep ih => exact (T.jump_globalClock_preserved h τ hτ hstep).trans ih

theorem continuousStep_globalClock (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → T.HAVar → ℝ}
    (hc : (T.toAutomaton h τ hτ).ContinuousStep s s' r γ) :
    s'.val.2 T.globalClock = s.val.2 T.globalClock + r := by
  have hf := (hc.2.2.2 ⟨r, by simp⟩).1.2
  rw [hc.2.2.1] at hf
  exact hf

theorem execution_final_clock_eq_last_finish (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ) :
    e.finalState.val.2 T.globalClock =
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩).val.2 T.globalClock :=
  T.discreteSteps_globalClock_preserved h τ hτ e.finalSteps

end STLTableau.Section4.Tableau
