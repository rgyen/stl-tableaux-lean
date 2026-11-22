import STLTableaux.Automata.Translation.PrelimStateGoal

/-! Proposition 5.6: bounded zero-time jump extension. A shortcut is exactly
a nonempty original discrete chain of at most n steps, through valid states.
Original edges remain available. Execution unfolding changes no flow or
observed signal and introduces no final discrete tail. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} (H : HybridAutomaton Mode Label Var)

/-- A chain of one to `n` zero-time jumps from `a` to `b`. -/
def BoundedZeroTime (n : ℕ) (a b : H.State) : Prop :=
  ∃ (k : ℕ) (v : Fin (k + 1) → H.State),
    0 < k ∧ k ≤ n ∧ v 0 = a ∧ v (Fin.last k) = b ∧
      ∀ i : Fin k, H.DiscreteStep (v i.castSucc) (v i.succ)

private theorem finite_chain_rtg {α : Type*} {R : α → α → Prop} (k : ℕ)
    (v : Fin (k + 1) → α) (steps : ∀ i : Fin k, R (v i.castSucc) (v i.succ)) :
    Relation.ReflTransGen R (v 0) (v (Fin.last k)) := by
  induction k with
  | zero => exact .refl
  | succ k ih =>
    have tail := ih (fun i => v i.succ) (fun i => steps i.succ)
    exact tail.head (steps 0)

theorem BoundedZeroTime.transGen {n : ℕ} {a b : H.State}
    (path : H.BoundedZeroTime n a b) : Relation.TransGen H.DiscreteStep a b := by
  obtain ⟨k, v, positive, _, first, last, steps⟩ := path
  cases k with
  | zero => omega
  | succ k =>
    have tail := finite_chain_rtg k (fun i => v i.succ) (fun i => steps i.succ)
    exact first ▸ last ▸ Relation.TransGen.head' (steps 0) tail

theorem boundedZeroTime_zero {a b : H.State} : ¬ H.BoundedZeroTime 0 a b := by
  rintro ⟨k, _, hk, hn, _⟩
  omega

theorem boundedZeroTime_single {n : ℕ} (hn : 1 ≤ n) {a b : H.State}
    (step : H.DiscreteStep a b) : H.BoundedZeroTime n a b := by
  refine ⟨1, ![a, b], by decide, hn, rfl, rfl, ?_⟩
  intro i
  fin_cases i
  exact step

/-- The right summand names a shortcut by its endpoint modes. Multiple
original chains with these endpoints are alternatives of the same jump
relation; no overapproximation of guards, resets, or intermediate invariants
is made. The left summand retains every original edge and its label. -/
def boundedZeroTimeExtension (n : ℕ) :
    HybridAutomaton Mode (Sum Label (Mode × Mode)) Var where
  modes_finite := H.modes_finite
  variables_finite := H.variables_finite
  edge := {e | match e.2.1 with
    | .inl l => (e.1, l, e.2.2) ∈ H.edge
    | .inr modes => e.1 = modes.1 ∧ e.2.2 = modes.2 ∧
        ∃ a b : H.State, a.val.1 = modes.1 ∧ b.val.1 = modes.2 ∧
          H.BoundedZeroTime n a b}
  initial := H.initial
  invariant := H.invariant
  flow := H.flow
  trajectory_closed := H.trajectory_closed
  jump := fun e s s' => match e.val.2.1 with
    | .inl l => ∃ old : {f // f ∈ H.edge},
        old.val = (e.val.1, l, e.val.2.2) ∧ H.jump old s s'
    | .inr _ => ∃ a b : H.State,
        a.val = s ∧ b.val = s' ∧ H.BoundedZeroTime n a b

theorem extension_step_iff (n : ℕ) {a b : H.State} :
    (H.boundedZeroTimeExtension n).DiscreteStep a b ↔
      H.DiscreteStep a b ∨ H.BoundedZeroTime n a b := by
  constructor
  · rintro ⟨e, hs, ht, hj⟩
    cases hl : e.val.2.1 with
    | inl l =>
      change (match e.val.2.1 with
        | .inl l => ∃ old : {f // f ∈ H.edge},
            old.val = (e.val.1, l, e.val.2.2) ∧ H.jump old a.val b.val
        | .inr _ => ∃ s t : H.State,
            s.val = a.val ∧ t.val = b.val ∧ H.BoundedZeroTime n s t) at hj
      rw [hl] at hj
      obtain ⟨old, he, jump⟩ := hj
      exact Or.inl ⟨old, he ▸ hs, he ▸ ht, jump⟩
    | inr modes =>
      change (match e.val.2.1 with
        | .inl l => ∃ old : {f // f ∈ H.edge},
            old.val = (e.val.1, l, e.val.2.2) ∧ H.jump old a.val b.val
        | .inr _ => ∃ s t : H.State,
            s.val = a.val ∧ t.val = b.val ∧ H.BoundedZeroTime n s t) at hj
      rw [hl] at hj
      obtain ⟨s, t, ha, hb, path⟩ := hj
      exact Or.inr ((Subtype.ext ha : s = a) ▸ (Subtype.ext hb : t = b) ▸ path)
  · rintro (⟨old, hs, ht, jump⟩ | path)
    · let e : Mode × Sum Label (Mode × Mode) × Mode :=
        (old.val.1, Sum.inl old.val.2.1, old.val.2.2)
      have he : e ∈ (H.boundedZeroTimeExtension n).edge := old.property
      exact ⟨⟨e, he⟩, hs, ht, old, rfl, jump⟩
    · let modes := (a.val.1, b.val.1)
      let e : Mode × Sum Label (Mode × Mode) × Mode :=
        (a.val.1, Sum.inr modes, b.val.1)
      have he : e ∈ (H.boundedZeroTimeExtension n).edge :=
        ⟨rfl, rfl, a, b, rfl, rfl, path⟩
      exact ⟨⟨e, he⟩, rfl, rfl, a, b, rfl, rfl, path⟩

theorem extension_rtg_iff (n : ℕ) {a b : H.State} :
    Relation.ReflTransGen (H.boundedZeroTimeExtension n).DiscreteStep a b ↔
      Relation.ReflTransGen H.DiscreteStep a b := by
  constructor
  · intro steps
    induction steps with
    | refl => exact .refl
    | tail _ step ih =>
      rcases (H.extension_step_iff n).mp step with old | path
      · exact ih.tail old
      · exact ih.trans (path.transGen H).to_reflTransGen
  · intro steps
    induction steps with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail ((H.extension_step_iff n).mpr (Or.inl step))

theorem extension_tg_iff (n : ℕ) {a b : H.State} :
    Relation.TransGen (H.boundedZeroTimeExtension n).DiscreteStep a b ↔
      Relation.TransGen H.DiscreteStep a b := by
  constructor
  · intro steps
    induction steps with
    | single step =>
      rcases (H.extension_step_iff n).mp step with old | path
      · exact .single old
      · exact path.transGen H
    | tail _ step ih =>
      rcases (H.extension_step_iff n).mp step with old | path
      · exact ih.tail old
      · exact ih.trans (path.transGen H)
  · intro steps
    induction steps with
    | single step => exact .single ((H.extension_step_iff n).mpr (Or.inl step))
    | tail _ step ih => exact ih.tail ((H.extension_step_iff n).mpr (Or.inl step))

/-- Unfold added zero-time edges while retaining every positive flow,
entry/exit valuation, time boundary, and observation of the same signal. -/
def PrelimExecution.unfoldZeroTimeExtension (n : ℕ) {σ : FiniteSignal Var}
    (e : (H.boundedZeroTimeExtension n).PrelimExecution σ) : H.PrelimExecution σ where
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
  initialSteps := (H.extension_rtg_iff n).mp e.initialSteps
  discreteSteps := fun i hi => (H.extension_tg_iff n).mp (e.discreteSteps i hi)
  signal_eq := e.signal_eq

/-- Original executions remain available without compressing any step. -/
def PrelimExecution.inZeroTimeExtension (n : ℕ) {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) : (H.boundedZeroTimeExtension n).PrelimExecution σ where
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
  initialSteps := (H.extension_rtg_iff n).mpr e.initialSteps
  discreteSteps := fun i hi => (H.extension_tg_iff n).mpr (e.discreteSteps i hi)
  signal_eq := e.signal_eq

/-- Prefix-language preservation, including early goal witnesses. -/
theorem boundedZeroTimeExtension_prefix_iff (n : ℕ) (σ : FiniteSignal Var) :
    (H.boundedZeroTimeExtension n).IsPrelimPrefix σ ↔ H.IsPrelimPrefix σ :=
  ⟨fun ⟨e⟩ => ⟨e.unfoldZeroTimeExtension H n⟩,
    fun ⟨e⟩ => ⟨e.inZeroTimeExtension H n⟩⟩

/-- Proposition 5.6 for full-horizon system trajectories. The execution
transfers preserve the final boundary as well as the observed signal. -/
theorem boundedZeroTimeExtension_trajectory_iff (n : ℕ) (σ : FiniteSignal Var) :
    (H.boundedZeroTimeExtension n).IsPrelimTrajectory σ ↔ H.IsPrelimTrajectory σ := by
  constructor
  · rintro ⟨e, full⟩
    exact ⟨e.unfoldZeroTimeExtension H n, full⟩
  · rintro ⟨e, full⟩
    exact ⟨e.inZeroTimeExtension H n, full⟩

theorem PrelimExecution.extension_visitsState_iff (n : ℕ) {σ : FiniteSignal Var}
    (e : (H.boundedZeroTimeExtension n).PrelimExecution σ) (s : H.State) :
    (e.unfoldZeroTimeExtension H n).VisitsState s ↔ e.VisitsState s := by
  change ((∃ i u, s.val = ((e.start i).val.1, e.curve i u)) ∨
    (Relation.ReflTransGen H.DiscreteStep e.initialState s ∧
      Relation.ReflTransGen H.DiscreteStep s (e.start ⟨0, e.nonempty⟩)) ∨
    ∃ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.ReflTransGen H.DiscreteStep (e.finish i) s ∧
      Relation.ReflTransGen H.DiscreteStep s (e.start ⟨i.val + 1, hi⟩)) ↔ _
  simp only [← H.extension_rtg_iff n]
  rfl

theorem boundedZeroTimeExtension_reachesState_iff (n : ℕ) (σ : FiniteSignal Var)
    (goal : Set H.State) :
    (H.boundedZeroTimeExtension n).PrelimReachesState σ goal ↔
      H.PrelimReachesState σ goal := by
  constructor
  · rintro ⟨e, s, hg, visit⟩
    exact ⟨e.unfoldZeroTimeExtension H n, s, hg,
      (e.extension_visitsState_iff H n s).mpr visit⟩
  · rintro ⟨e, s, hg, visit⟩
    refine ⟨e.inZeroTimeExtension H n, s, hg, ?_⟩
    exact ((e.inZeroTimeExtension H n).extension_visitsState_iff H n s).mp visit

/-- Represent initial jump blocks in the initial condition. This operation
is used on the system, not on the translated property automaton. -/
def withInitialJumpClosure : HybridAutomaton Mode Label Var :=
  { H with
    initial := {s | ∃ a b : H.State, a.val ∈ H.initial ∧ b.val = s ∧
      Relation.ReflTransGen H.DiscreteStep a b} }

/-- With initial jumps represented in `init`, start at the first flow
without changing any observed value or either end of any flow. -/
def PrelimExecution.startWithFlow {σ : FiniteSignal Var} (e : H.PrelimExecution σ) :
    H.withInitialJumpClosure.PrelimExecution σ :=
  { e with
    initialState := e.start ⟨0, e.nonempty⟩
    initial_mem := ⟨e.initialState, e.start ⟨0, e.nonempty⟩, e.initial_mem, rfl, e.initialSteps⟩
    initialSteps := .refl }

/-- Unfold the initial condition into a genuine initial jump block. -/
private theorem PrelimExecution.unfoldInitialJumpClosure {σ : FiniteSignal Var}
    (e : H.withInitialJumpClosure.PrelimExecution σ) :
    ∃ out : H.PrelimExecution σ, out.ReachesHorizon ↔ e.ReachesHorizon := by
  obtain ⟨a, b, initial, same, jumps⟩ := e.initial_mem
  have hb : b = e.initialState := Subtype.ext same
  exact ⟨{ e with
    initialState := a
    initial_mem := initial
    initialSteps := (hb ▸ jumps).trans e.initialSteps }, Iff.rfl⟩

theorem initialJumpClosure_prefix_iff (σ : FiniteSignal Var) :
    H.withInitialJumpClosure.IsPrelimPrefix σ ↔ H.IsPrelimPrefix σ :=
  ⟨fun ⟨e⟩ => let ⟨out, _⟩ := e.unfoldInitialJumpClosure H; ⟨out⟩,
    fun ⟨e⟩ => ⟨e.startWithFlow H⟩⟩

theorem initialJumpClosure_trajectory_iff (σ : FiniteSignal Var) :
    H.withInitialJumpClosure.IsPrelimTrajectory σ ↔ H.IsPrelimTrajectory σ :=
  ⟨fun ⟨e, full⟩ => let ⟨out, same⟩ := e.unfoldInitialJumpClosure H; ⟨out, same.mpr full⟩,
    fun ⟨e, full⟩ => ⟨e.startWithFlow H, full⟩⟩

/-- A bounded system witness starts with its first flow and each subsequent
block is realized by one shortcut. The full projected signal is unchanged. -/
theorem PrelimExecution.exists_bounded_startWithFlow {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (n : ℕ)
    (bound : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish i) (e.start ⟨i.val + 1, hi⟩)) :
    let K := H.withInitialJumpClosure.boundedZeroTimeExtension n
    ∃ w : K.PrelimExecution σ,
      (w.ReachesHorizon ↔ e.ReachesHorizon) ∧
      w.initialState = w.start ⟨0, w.nonempty⟩ ∧
      ∀ (i : Fin w.count) (hi : i.val + 1 < w.count),
        K.DiscreteStep (w.finish i) (w.start ⟨i.val + 1, hi⟩) := by
  refine ⟨(e.startWithFlow H).inZeroTimeExtension H.withInitialJumpClosure n,
    Iff.rfl, rfl, ?_⟩
  intro i hi
  exact (H.withInitialJumpClosure.extension_step_iff n).mpr (Or.inr (bound i hi))

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``BoundedZeroTime.transGen, ``boundedZeroTime_zero, ``boundedZeroTime_single,
      ``extension_step_iff, ``extension_rtg_iff, ``extension_tg_iff,
      ``PrelimExecution.unfoldZeroTimeExtension, ``PrelimExecution.inZeroTimeExtension,
      ``boundedZeroTimeExtension_prefix_iff, ``boundedZeroTimeExtension_trajectory_iff,
      ``boundedZeroTimeExtension_reachesState_iff, ``PrelimExecution.startWithFlow,
      ``initialJumpClosure_prefix_iff, ``initialJumpClosure_trajectory_iff,
      ``PrelimExecution.exists_bounded_startWithFlow] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end STLTableau.HybridAutomaton
