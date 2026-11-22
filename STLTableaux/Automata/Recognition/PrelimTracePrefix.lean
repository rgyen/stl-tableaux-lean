import STLTableaux.Automata.Translation.PrelimStateGoal
import STLTableaux.Automata.Recognition.TypedOrdinaryTrace

/-! Relate preliminary executions to the visit and partition lemmas. The
construction aligns the initial physical coordinates and fills the
unobserved stopping time. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "H" => T.prelimAutomaton h τ
local notation "Old" => T.typedAutomaton h τ

theorem prelim_step_to_typed {a b : (H).State}
    (step : (H).DiscreteStep a b) (early : b.val.2 (.inl T.globalClock) < τ) :
    (Old).DiscreteStep a b := by
  obtain ⟨e, hs, hd, h₁, h₂, hg, hr, hc, hz, ht, hm, ha⟩ := step
  exact ⟨e, hs, hd, h₁, h₂, hg, hr, hc, hz,
    iff_of_false (fun hb => early.not_ge (ht hb)) early.not_ge, hm, ha⟩

private theorem prelimRTG {a b : (H).State}
    (steps : Relation.ReflTransGen (H).DiscreteStep a b)
    (early : b.val.2 (.inl T.globalClock) < τ) :
    Relation.ReflTransGen (Old).DiscreteStep a b := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih =>
    exact (ih ((T.prelim_jump_global h τ step) ▸ early)).tail
      (T.prelim_step_to_typed h τ step early)

private theorem prelimTG {a b : (H).State}
    (steps : Relation.TransGen (H).DiscreteStep a b)
    (early : b.val.2 (.inl T.globalClock) < τ) :
    Relation.TransGen (Old).DiscreteStep a b := by
  obtain ⟨c, pre, step⟩ := Relation.TransGen.tail'_iff.mp steps
  exact Relation.TransGen.tail'
    (T.prelimRTG h τ pre ((T.prelim_jump_global h τ step) ▸ early))
    (T.prelim_step_to_typed h τ step early)

private def traceInitialValue (v w : T.TypedVar → ℝ) : T.TypedVar → ℝ
  | .inl (.inl x) => w (.inl (.inl x))
  | .inl (.inr c) => v (.inl (.inr c))
  | .inr b => v (.inr b)

/-- `prelimAutomaton` checks the atoms of an initial singleton on the
following flow's physical value. Reuse that guard to represent the singleton
in the trace's initial state, with the same mode, clocks, and marker. -/
private theorem traceInitialConditions {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (hh : σ.horizon = τ) :
    let w := T.traceInitialValue e.initialState.val.2 (e.start ⟨0, e.nonempty⟩).val.2
    ∃ inv : (e.initialState.val.1, w) ∈ (Old).invariant,
      (e.initialState.val.1, w) ∈ (Old).initial ∧
        Relation.ReflTransGen (Old).DiscreteStep ⟨(e.initialState.val.1, w), inv⟩
          (e.start ⟨0, e.nonempty⟩) := by
  let a := e.initialState
  let b := e.start ⟨0, e.nonempty⟩
  let w := T.traceInitialValue a.val.2 b.val.2
  change ∃ inv : (a.val.1, w) ∈ (Old).invariant,
    (a.val.1, w) ∈ (Old).initial ∧ Relation.ReflTransGen (Old).DiscreteStep ⟨_, inv⟩ b
  have steps : Relation.ReflTransGen (Old).DiscreteStep a b :=
    T.prelimRTG h τ e.initialSteps (by
      change (e.start _).val.2 (.inl T.globalClock) < τ
      rw [T.prelim_entry_time h τ e]
      exact (e.entry_lt_horizon _).trans_eq hh)
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp steps with same | moves
  · have eq : w = a.val.2 := by
      change T.traceInitialValue a.val.2 b.val.2 = a.val.2
      rw [← same]
      funext x
      rcases x with (x | c) | m <;> rfl
    have inv : (a.val.1, w) ∈ (Old).invariant := by rw [eq]; exact a.property
    refine ⟨inv, by rw [eq]; exact e.initial_mem, ?_⟩
    have ab : (⟨(a.val.1, w), inv⟩ : (Old).State) = b := by
      apply Subtype.ext
      change (a.val.1, w) = b.val
      rw [eq]
      exact congrArg Subtype.val same.symm
    exact ab ▸ Relation.ReflTransGen.refl
  have aInitial : a.val ∈ (Old).initial := e.initial_mem
  obtain ⟨l, init, v, guards, value, dwell, bit⟩ := aInitial
  rcases T.typed_boundary_block h τ moves with jump | ⟨c, first, _, second⟩
  · obtain ⟨ed, es, et, js, jt, g, reset, gt, dt, time, marker, atoms⟩ := jump
    have atoms₀ : T.atomsAt a.val.1 w := by
      simpa only [atomsAt, atomHolds, old, traceInitialValue, w] using atoms (marker dwell).2
    have inv : (a.val.1, w) ∈ (Old).invariant := by
      rcases a.property with ⟨hb, hg, _, hm⟩
      exact ⟨hb, hg, atoms₀, hm⟩
    let v' : T.HAVar → ℝ
      | .inl x => b.val.2 (.inl (.inl x))
      | .inr c => v (.inr c)
    have value' : T.old w = T.initialReset l.resets v' := by
      funext x
      rcases x with x | (c | u)
      · rfl
      · exact congrFun value (.inr (.inl c))
      · exact congrFun value (.inr (.inr u))
    exact ⟨inv, ⟨l, init, v', guards, value', dwell, bit⟩,
      .single ⟨ed, es, et, js, jt, g, reset, gt, dt, time, marker, atoms⟩⟩
  · exact (T.no_adjacent_zero h τ first dwell second).elim

private noncomputable def traceInitialState {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (hh : σ.horizon = τ) : (Old).State :=
  ⟨(e.initialState.val.1,
    T.traceInitialValue e.initialState.val.2 (e.start ⟨0, e.nonempty⟩).val.2),
    (T.traceInitialConditions h τ e hh).choose⟩

noncomputable def prefixSignal {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ) :
    FiniteSignal T.TypedVar := by
  classical
  exact ⟨σ.horizon, σ.horizon_pos, fun t =>
    if t.val = 0 then T.traceInitialValue e.initialState.val.2 (e.start ⟨0, e.nonempty⟩).val.2
    else if t.val = e.boundary ⟨e.count, by omega⟩ then e.finalState.val.2 else σ.value t⟩

noncomputable def prelimTypedPrefix {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (hh : σ.horizon = τ) :
    (Old).Execution (T.prefixSignal h τ e) where
  count := e.count
  nonempty := e.nonempty
  initialState := T.traceInitialState h τ e hh
  initial_mem := (T.traceInitialConditions h τ e hh).choose_spec.1
  initial_signal_eq := by simp [prefixSignal, traceInitialState]
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
  initialSteps := (T.traceInitialConditions h τ e hh).choose_spec.2
  discreteSteps := fun i hi => T.prelimTG h τ (e.discreteSteps i hi) (by
    rw [T.prelim_entry_time h τ e]
    exact (e.entry_lt_horizon _).trans_eq hh)
  finalState := e.finalState
  finalSteps := .refl
  final_signal_eq := by
    intro t ht
    have stoppos : 0 < e.boundary ⟨e.count, by omega⟩ := by
      rw [← e.first_zero]
      exact e.increasing (Fin.mk_lt_mk.mpr e.nonempty)
    have pos : 0 < t.val := ht.symm ▸ stoppos
    simp only [prefixSignal, if_neg pos.ne', if_pos ht]
  signal_eq := by
    intro i t ht positive
    have hlast := e.increasing.monotone (Fin.le_last i.succ)
    have hn : t.val ≠ e.boundary ⟨e.count, by omega⟩ := (ht.2.trans_le hlast).ne
    simp only [prefixSignal, if_neg positive.ne', if_neg hn]
    exact e.signal_eq i t ht

private theorem prefixSignal_physical_before_stop {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (t : σ.Time) (x : T.realVariables)
    (notStop : t.val ≠ e.boundary ⟨e.count, by omega⟩) :
    (T.prefixSignal h τ e).value t (.inl (.inl x)) = σ.value t (.inl (.inl x)) := by
  by_cases zero : t.val = 0
  · simp only [prefixSignal, if_pos zero, traceInitialValue]
    exact (congrFun e.signal_at_zero.symm _).trans
      (congrArg (fun u : σ.Time => σ.value u (.inl (.inl x))) (Subtype.ext zero.symm))
  · simp only [prefixSignal, if_neg zero, if_neg notStop]

theorem prefixSignal_projectsThrough {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {cut : ℝ} (hc : cut ≤ e.boundary ⟨e.count, by omega⟩) :
    T.TypedProjectsThrough (T.prefixSignal h τ e) ρ cut := by
  refine ⟨hc.trans (e.last_le_horizon.trans_eq proj.1), ?_⟩
  intro t u he hu x
  have hn : t.val ≠ e.boundary ⟨e.count, by omega⟩ :=
    ((he ▸ hu).trans_le hc).ne
  exact (T.prefixSignal_physical_before_stop h τ e t x hn).trans (proj.2 t u he x)

theorem prefixSignal_projects_at_horizon {σ : FiniteSignal T.TypedVar}
    (e : (H).PrelimExecution σ) (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    (he : e.boundary ⟨e.count, by omega⟩ = σ.horizon) :
    T.TypedProjectsTo (T.prefixSignal h τ e) ρ := by
  refine ⟨proj.1, ?_⟩
  intro t u ht x
  have hn : t.val ≠ e.boundary ⟨e.count, by omega⟩ := fun h => t.property.2.ne (h.trans he)
  exact (T.prefixSignal_physical_before_stop h τ e t x hn).trans (proj.2 t u ht x)

/-- A purely logical terminal certificate, passed to the existing path
assembler. It is never appended to the actual prelim execution. -/
theorem end_edge_of_prelimGoal (a : (H).State)
    (certificate : ∃ (l : EdgeLabel Clock) (q : T.states),
      (a.val.1.val, l, q.val) ∈ T.edges ∧
      T.guardsHold l (T.old a.val.2) ∧ T.EndGoal q)
    (ht : a.val.2 (.inl T.globalClock) = τ) (hd : 0 < a.val.2 T.dwell) :
    ∃ b : (T.endPositionAutomaton h τ).State,
      T.EndGoal b.val.1 ∧ (T.endPositionAutomaton h τ).DiscreteStep a b := by
  obtain ⟨l, q, edge, guards, endGoal⟩ := certificate
  let v : T.TypedVar → ℝ
    | .inl x => T.reset l.resets (T.old a.val.2) x
    | .inr false => 0
    | .inr true => 1
  have inv : (q, v) ∈ (T.endPositionAutomaton h τ).invariant := by
    refine ⟨Or.inr rfl, fun _ => ht.le, ?_, ?_⟩
    · intro p hp
      rcases endGoal.2 _ hp with he | he <;> cases he
    · intro m hm
      rcases endGoal.2 _ hm with he | he
      · cases he
      · cases he
        exact iff_of_true rfl rfl
  let b : (T.endPositionAutomaton h τ).State := ⟨(q, v), inv⟩
  let e := (a.val.1, l, q)
  refine ⟨b, endGoal, ⟨⟨e, edge⟩, rfl, rfl, rfl, rfl, guards,
    fun _ => rfl, rfl, rfl, Or.inr ⟨ht, hd, endGoal⟩,
    fun hz => (hd.ne' hz).elim, ?_⟩⟩
  intro hz
  exact (one_ne_zero (show (1 : ℝ) = 0 from hz)).elim

end STLTableau.Section4.Tableau
