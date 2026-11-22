import STLTableaux.Automata.Composition.SystemTableauFlowLift
import STLTableaux.Automata.Recognition.PartitionJumpBoundary

/-! Realize a tableau edge between partition intervals using the endpoint
of the system's continuous transition. The same guard and reset conditions
cover singleton intervals and positive-duration intervals. -/
namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

/-- The given edge, checked guard and partition labels produce an actual
prelim jump. The source endpoint's real values are not identified with
the next signal observation. Marker and post-atom tests are derived from
the partition, including the zero-residence singleton case. -/
theorem prelim_jump_after_cell (h : T.TranslationReady) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (i j : Fin P.size) (adj : i.val + 1 = j.val)
    (q q' : T.states) (l : EdgeLabel Clock) (edge : (q.val, l, q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (x : Var → ℝ) (w : T.realVariables → ℝ)
    (b : (T.prelimAutomaton h σ.horizon).State)
    (exit : b.val = (q, T.forwardCurveValue
      (T.entryValue (P.interval i).left α x (P.interval i).leftBoundary)
      (STLTableau.Judgement.duration P i) w))
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ P α ⟨i.val, by omega⟩)
    (guards : ∀ g ∈ l.guards,
      g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
    (labels' : ∀ loc ∈ T.label q'.val, loc.holds σ P
      (l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
      ⟨j.val, by omega⟩)
    (atoms' : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      a.Holds (σ.value (pieceEntry σ P j))) :
    let β := l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    ∃ c : (T.prelimAutomaton h σ.horizon).State,
      c.val = (q', T.entryValue (P.interval j).left β
        (σ.value (pieceEntry σ P j)) (P.interval j).leftBoundary) ∧
      (T.prelimAutomaton h σ.horizon).DiscreteStep b c := by
  intro β
  have next : i.val + 1 < P.size := adj ▸ j.isLt
  have index : (⟨i.val + 1, next⟩ : Fin P.size) = j := Fin.ext adj
  have join := P.adjacent_right_eq_left i next
  rw [index] at join
  have mode : b.val.1 = q := congrArg Prod.fst exit
  have time : b.val.2 (.inl T.globalClock) = (P.interval j).left := by
    rw [exit]
    change (P.interval i).left + ((P.interval i).right - (P.interval i).left) = _
    linarith
  have clocks (c : T.clocks) : b.val.2 (.inl (.inr (.inl c))) =
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i) c.val : ℝ) := by
    rw [exit]
    simp [forwardCurveValue, entryValue, ClockResetSet.elapse]
  have notTerminal : q' ∉ T.terminalModes := by
    intro terminal
    have impossible : j.val = P.size := labels' .terminal terminal
    omega
  have early : (P.interval j).left < σ.horizon := (pieceEntry σ P j).property.2
  obtain ⟨c, entry, step⟩ := T.forward_jump_entry h σ.horizon b q' l (mode ▸ edge)
    (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) clocks guards
    (σ.value (pieceEntry σ P j)) (P.interval j).leftBoundary
    (iff_of_false notTerminal (by rw [time]; exact early.not_ge))
    (by
      intro zero
      have duration : (STLTableau.Judgement.duration P i : ℝ) = 0 := by
        simpa only [exit, forwardCurveValue, entryValue, dwell, zero_add] using zero
      obtain ⟨closed, opened⟩ :=
        (partition_adjacent_jump_markers σ P i j adj).2 duration
      constructor
      · rw [exit]
        change T.entryValue (P.interval i).left α x (P.interval i).leftBoundary T.bit = 1
        rw [closed]
        rfl
      · exact opened)
    atoms' (T.piece_entry_markers σ P j q' _ labels')
    (by
      intro opened a ha
      rw [mode] at ha
      exact T.partition_source_atoms_at_open_successor σ P i j adj q α labels opened a ha)
  refine ⟨c, by simpa only [time] using entry, ?_⟩
  obtain ⟨e, hs, ht, h₁, h₂, hg, hr, hc, hz, horizon, marker, post⟩ := step
  exact ⟨e, hs, ht, h₁, h₂, hg, hr, hc, hz, horizon.mp, marker, post⟩

private theorem rejoinState (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) (τ : ℝ)
    (s : (T.systemTableauAutomaton H h τ).State)
    (agree : ∀ x : T.realVariables,
      (H.leftStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s).val.2 x.val =
      (H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s).val.2
        (.inl (.inl x))) :
    T.joinState H h τ
      (H.leftStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s)
      (H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s) agree = s := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext x
  rcases every_joined_variable T.systemVarName T.tableauVarName x with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact congrFun (congrArg (fun s => s.val.2) (T.joinState_system H h τ _ _ agree)) x
  · exact congrFun (congrArg (fun s => s.val.2) (T.joinState_tableau H h τ _ _ agree)) x

/-- At a cell boundary, synchronize the given tableau edge with the
actual SYSTEM action (or idle). The target real values are derived from
the following observed system flow, not supplied as an endpoint-matching
assumption. This also permits a singleton as the target partition cell. -/
theorem systemTableau_jump_after_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (i j : Fin P.size) (adj : i.val + 1 = j.val)
    (q q' : T.states) (l : EdgeLabel Clock) (edge : (q.val, l, q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (x : Var → ℝ) (w : T.realVariables → ℝ)
    (b : (T.systemTableauAutomaton H h σ.horizon).State)
    (exit : (H.rightStateOn (T.prelimAutomaton h σ.horizon)
      T.systemVarName T.tableauVarName b).val = (q, T.forwardCurveValue
        (T.entryValue (P.interval i).left α x (P.interval i).leftBoundary)
        (STLTableau.Judgement.duration P i) w))
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ P α ⟨i.val, by omega⟩)
    (guards : ∀ g ∈ l.guards,
      g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
    (labels' : ∀ loc ∈ T.label q'.val, loc.holds σ P
      (l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
      ⟨j.val, by omega⟩)
    (atoms' : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      a.Holds (σ.value (pieceEntry σ P j)))
    (g : ObservedFlow H σ) (begin : g.beginTime = (P.interval j).left)
    (system :
      H.leftStateOn (T.prelimAutomaton h σ.horizon) T.systemVarName T.tableauVarName b = g.start ∨
      H.DiscreteStep
        (H.leftStateOn (T.prelimAutomaton h σ.horizon) T.systemVarName T.tableauVarName b)
        g.start) :
    let A := T.prelimAutomaton h σ.horizon
    let β := l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    ∃ c : (T.systemTableauAutomaton H h σ.horizon).State,
      H.leftStateOn A T.systemVarName T.tableauVarName c = g.start ∧
      (H.rightStateOn A T.systemVarName T.tableauVarName c).val =
        (q', T.entryValue (P.interval j).left β
          (σ.value (pieceEntry σ P j)) (P.interval j).leftBoundary) ∧
      (T.systemTableauAutomaton H h σ.horizon).DiscreteStep b c := by
  intro A β
  let s := H.leftStateOn A T.systemVarName T.tableauVarName b
  let m := H.rightStateOn A T.systemVarName T.tableauVarName b
  have observed : σ.value (pieceEntry σ P j) = g.start.val.2 := by
    have upper : (pieceEntry σ P j).val < g.endTime := by
      change (P.interval j).left < g.endTime
      linarith [g.positive, g.duration_eq]
    have body := g.observe (pieceEntry σ P j) ⟨begin.le, upper⟩
    refine body.trans ((congrArg g.curve ?_).trans g.step.2.1)
    apply Subtype.ext
    change (P.interval j).left - g.beginTime = 0
    rw [begin]
    ring
  obtain ⟨m', entry, jump⟩ := T.prelim_jump_after_cell h σ P i j adj q q' l edge
    α x w m exit labels guards labels' atoms'
  have agree : ∀ x : T.realVariables, s.val.2 x.val = m.val.2 (.inl (.inl x)) := by
    intro x
    exact H.parallelOn_shared_value A T.systemVarName T.tableauVarName b rfl
  have agree' : ∀ x : T.realVariables, g.start.val.2 x.val = m'.val.2 (.inl (.inl x)) := by
    intro x
    rw [entry]
    change g.start.val.2 x.val = σ.value (pieceEntry σ P j) x.val
    rw [observed]
  let c := T.joinState H h σ.horizon g.start m' agree'
  refine ⟨c, T.joinState_system H h σ.horizon _ _ _, ?_, ?_⟩
  · rw [T.joinState_tableau]
    exact entry
  · have same : T.joinState H h σ.horizon s m agree = b := T.rejoinState H h σ.horizon b agree
    rcases system with idle | move
    · have idle' : s = g.start := idle
      have step := T.paste_monitor_step H h σ.horizon s agree (by rw [idle']; exact agree') jump
      rw [same] at step
      simpa only [idle'] using step
    · have step := T.paste_simultaneous H h σ.horizon agree agree' move jump
      rw [same] at step
      exact step

/-- The initial singleton is a PROPERTY-only jump: the SYSTEM stays at
its actual initial flow state and its real values are unchanged. The
following positive residence is built over that system curve. Initial
signal agreement is derived from the supplied direct-start system witness,
not added as an independent boundary premise. -/
theorem systemTableau_initial_singleton_to_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (f : ObservedFlow H σ) (first : f.start = e.start ⟨0, e.nonempty⟩)
    (flows : H.ContinuousFlows) (P : IntervalPartition σ.domain) (more : 1 < P.size)
    (zero : (STLTableau.Judgement.duration P ⟨0, by omega⟩ : ℝ) = 0)
    (left : f.beginTime = (P.interval ⟨1, more⟩).left)
    (right : f.endTime = (P.interval ⟨1, more⟩).right)
    (q q' : T.states) (l₀ l₁ : EdgeLabel Clock)
    (initial : (l₀, q.val) ∈ T.initial) (edge : (q.val, l₁, q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (guards₀ : ∀ g ∈ l₀.guards, g.holds α)
    (labels : ∀ loc ∈ T.label q.val,
      loc.holds σ P (l₀.resets.apply α) ⟨0, by omega⟩)
    (guards₁ : ∀ g ∈ l₁.guards, g.holds
      (ClockResetSet.elapse (l₀.resets.apply α) (STLTableau.Judgement.duration P ⟨0, by omega⟩)))
    (labels' : ∀ loc ∈ T.label q'.val, loc.holds σ P
      (l₁.resets.apply (ClockResetSet.elapse (l₀.resets.apply α)
        (STLTableau.Judgement.duration P ⟨0, by omega⟩))) ⟨1, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      Continuous a.function) :
    let A := T.prelimAutomaton h σ.horizon
    let B := T.systemTableauAutomaton H h σ.horizon
    let β := l₁.resets.apply (ClockResetSet.elapse (l₀.resets.apply α)
      (STLTableau.Judgement.duration P ⟨0, by omega⟩))
    let v := T.entryValue f.beginTime β (f.curve ⟨0, by simp⟩)
      (P.interval ⟨1, more⟩).leftBoundary
    ∃ a b c : B.State,
      a.val ∈ B.initial ∧
      H.leftStateOn A T.systemVarName T.tableauVarName a = f.start ∧
      H.leftStateOn A T.systemVarName T.tableauVarName b = f.start ∧
      H.leftStateOn A T.systemVarName T.tableauVarName c = f.finish ∧
      (H.rightStateOn A T.systemVarName T.tableauVarName a).val.1 = q ∧
      B.DiscreteStep a b ∧ B.ContinuousStep b c f.duration
        (fun u => T.joinValuation (f.curve u) (T.clockLiftCurve v f.curve u)) := by
  intro A B β v
  let i : Fin P.size := ⟨0, by omega⟩
  let j : Fin P.size := ⟨1, more⟩
  have size : 0 < P.size := by omega
  have atZero : (P.interval i).left = 0 := P.first_left_eq_domain_left size σ.horizon_pos
  have duration : STLTableau.Judgement.duration P i = 0 := Subtype.ext zero
  have join : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i more
  have rightZero : (P.interval j).left = 0 := by
    change (P.interval i).right - (P.interval i).left = 0 at zero
    linarith
  have time₀ : pieceEntry σ P i = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext atZero
  have time₁ : pieceEntry σ P j = ⟨0, le_rfl, σ.horizon_pos⟩ := Subtype.ext rightZero
  have starts : f.start = e.initialState := first.trans direct.symm
  have signal : σ.value ⟨0, le_rfl, σ.horizon_pos⟩ = f.start.val.2 :=
    e.signal_at_zero.trans (congrArg (fun s : H.State => s.val.2) first.symm)
  have observed : σ.value (pieceEntry σ P j) = f.curve ⟨0, by simp⟩ :=
    (congrArg σ.value time₁).trans (signal.trans f.step.2.1.symm)
  obtain ⟨a, init, entry⟩ := T.initial_piece h σ P size q l₀ initial α guards₀ labels
  have exit : a.val = (q, T.forwardCurveValue
      (T.entryValue (P.interval i).left (l₀.resets.apply α)
        (σ.value (pieceEntry σ P i)) (P.interval i).leftBoundary)
      (STLTableau.Judgement.duration P i) (fun x => σ.value (pieceEntry σ P i) x.val)) := by
    rw [entry]
    congr 1
    funext x
    cases x with
    | inl x =>
      cases x with
      | inl x => rfl
      | inr x => simp [forwardCurveValue, duration, i]
    | inr b => cases b <;> simp [forwardCurveValue, duration, i, dwell, bit]
  have atoms := T.closed_system_cell_atoms H f flows P j left right q' β labels'
    nonStrict functions
  obtain ⟨b, entryB, jump⟩ := T.prelim_jump_after_cell h σ P i j rfl q q' l₁ edge
    (l₀.resets.apply α) _ _ a exit labels guards₁ labels' (by
      intro p hp
      rw [observed]
      exact atoms ⟨0, by simp⟩ p hp)
  obtain ⟨b', c, entryB', _, step⟩ := T.monitor_flow_over_system_cell H h f flows P j
    left right q' β β labels' nonStrict functions
  have same : b' = b := by
    apply Subtype.ext
    rw [entryB', entryB, left, observed]
  subst b'
  have agree₀ : ∀ x : T.realVariables, f.start.val.2 x.val = a.val.2 (.inl (.inl x)) := by
    intro x
    rw [entry]
    change f.start.val.2 x.val = σ.value (pieceEntry σ P i) x.val
    rw [time₀, signal]
  have agree : ∀ u x, f.curve u x.val = T.clockLiftCurve v f.curve u (.inl (.inl x)) :=
    fun _ _ => rfl
  let ja := T.joinState H h σ.horizon f.start a agree₀
  let jb := T.joinState H h σ.horizon f.start b
    (T.curve_initial_agreement H h σ.horizon f.step step agree)
  let jc := T.joinState H h σ.horizon f.finish c
    (T.curve_final_agreement H h σ.horizon f.step step agree)
  refine ⟨ja, jb, jc, ?_, T.joinState_system H h σ.horizon _ _ _,
    T.joinState_system H h σ.horizon _ _ _, T.joinState_system H h σ.horizon _ _ _,
    ?_, T.paste_monitor_step H h σ.horizon f.start _ _ jump,
    T.paste_continuous H h σ.horizon f.step step agree⟩
  · exact T.joinState_initial H h σ.horizon f.start a agree₀ (starts.symm ▸ e.initial_mem) init
  · rw [T.joinState_tableau]
    exact congrArg Prod.fst entry

run_elab do
  for n in #[``prelim_jump_after_cell, ``systemTableau_jump_after_cell,
      ``systemTableau_initial_singleton_to_cell] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
