import STLTableaux.Automata.Composition.SystemTableauRunWord
import STLTableaux.Automata.Recognition.PrelimPartitionConnection

namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

/-- A singleton goal keeps the actual SYSTEM state, takes only the given
empty continuation if needed, and observes a positive actual SYSTEM suffix. -/
theorem systemTableau_singleton_goal_word (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) (zero : (STLTableau.Judgement.duration R i : ℝ) = 0)
    (q : T.states) (goal : q ∈ T.goalModes) (α : ClockValuation Clock)
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ R α ⟨i.val, by omega⟩)
    (a : (T.systemTableauAutomaton H h σ.horizon).State)
    (system : H.leftStateOn (T.prelimAutomaton h σ.horizon)
      T.systemVarName T.tableauVarName a = e.cellEntryState full R fine i)
    (monitor : (H.rightStateOn (T.prelimAutomaton h σ.horizon)
      T.systemVarName T.tableauVarName a).val =
      (q, T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
        (R.interval i).leftBoundary))
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    T.SystemGoalWord H h σ a (R.interval i).left := by
  let A := T.prelimAutomaton h σ.horizon
  let B := T.systemTableauAutomaton H h σ.horizon
  let k := e.cellOwner full R fine i
  let g := (e.observedFlow k).sliceAt (R.interval i).left (e.boundary k.succ)
    ⟨(e.cell_bounds full R fine i).1, e.cell_entry_lt full R fine i, le_rfl⟩
  have begin : g.beginTime = (R.interval i).left :=
    (e.observedFlow k).sliceAt_begin _ _ _
  have finish : g.endTime = e.boundary k.succ :=
    (e.observedFlow k).sliceAt_end _ _ _
  have start : g.start = e.cellEntryState full R fine i := rfl
  have bound : g.endTime ≤ σ.horizon := by
    rw [finish, ← full]
    exact e.increasing.monotone (Fin.le_last _)
  have signal := e.cell_entry_signal full R fine i
  have real : g.curve ⟨0, by simp⟩ = σ.value (pieceEntry σ R i) :=
    g.step.2.1.trans ((congrArg (fun s : H.State => s.val.2) start).trans signal.symm)
  have closed := (partition_singleton_markers σ R i zero).1
  let m := H.rightStateOn A T.systemVarName T.tableauVarName a
  have next : ∃ (m' : A.State) (mark : Marker),
      m'.val = (empty, T.entryValue (R.interval i).left α
        (σ.value (pieceEntry σ R i)) mark) ∧
      (m = m' ∨ A.DiscreteStep m m') := by
    by_cases same : q = empty
    · exact ⟨m, (R.interval i).leftBoundary, by simpa [same] using monitor, Or.inl rfl⟩
    · obtain ⟨l, edge, guards, resets⟩ := continuation q goal same
      have more : i.val + 1 < R.size := by
        by_contra missing
        have last : i.val + 1 = R.size := by omega
        have positive := last_piece_positive σ R i last
        linarith
      let j : Fin R.size := ⟨i.val + 1, more⟩
      have joint := R.adjacent_right_eq_left i more
      have time : (R.interval j).left = (R.interval i).left := by
        change (R.interval i).right - (R.interval i).left = 0 at zero
        change (R.interval i).right = (R.interval j).left at joint
        linarith
      have sample : pieceEntry σ R j = pieceEntry σ R i := Subtype.ext time
      have zd : STLTableau.Judgement.duration R i = 0 := Subtype.ext zero
      have exit : m.val = (q, T.forwardCurveValue
          (T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
            (R.interval i).leftBoundary)
          (STLTableau.Judgement.duration R i)
          (fun x => σ.value (pieceEntry σ R i) x.val)) := by
        rw [monitor, zd]
        congr 1
        funext x
        cases x with
        | inl x => cases x <;> simp [forwardCurveValue, entryValue]
        | inr b => cases b <;> simp [forwardCurveValue, entryValue, dwell, bit]
      obtain ⟨m', entry, jump⟩ := T.prelim_jump_after_cell h σ R i j rfl q empty l edge
        α (σ.value (pieceEntry σ R i)) (fun x => σ.value (pieceEntry σ R i) x.val)
        m exit labels (by intro g hg; rw [guards] at hg; exact hg.elim)
        (by intro loc hl; rw [heLab] at hl; exact hl.elim)
        (by intro atom ha; rw [heLab] at ha; exact ha.elim)
      refine ⟨m', (R.interval j).leftBoundary, ?_, Or.inr jump⟩
      have elapse : ClockResetSet.elapse α 0 = α := by
        funext c
        apply Subtype.ext
        simp [ClockResetSet.elapse]
      simpa [time, sample, resets, zd, elapse] using entry
  obtain ⟨m', mark, entry, lead⟩ := next
  obtain ⟨u, v, uentry, vend, flow⟩ := T.monitor_flow_of_closed_system_curve H h
    σ.horizon g empty α mark
    (by intro t atom ha; rw [heLab] at ha; exact ha.elim)
    (by intro b hb; rw [heLab] at hb; exact hb.elim) bound
  have same : u = m' := by
    apply Subtype.ext
    rw [uentry, entry, begin, real]
  rw [same] at flow
  have agree : ∀ t x, g.curve t x.val =
      T.clockLiftCurve (T.entryValue g.beginTime α (g.curve ⟨0, by simp⟩) mark)
        g.curve t (.inl (.inl x)) := fun _ _ => rfl
  let c := T.joinState H h σ.horizon g.start m'
    (T.curve_initial_agreement H h σ.horizon g.step flow agree)
  let d := T.joinState H h σ.horizon g.finish v
    (T.curve_final_agreement H h σ.horizon g.step flow agree)
  have jointflow : B.ContinuousStep c d g.duration
      (fun t => T.joinValuation (g.curve t)
        (T.clockLiftCurve
          (T.entryValue g.beginTime α (g.curve ⟨0, by simp⟩) mark) g.curve t)) :=
    T.paste_continuous H h σ.horizon g.step flow agree
  have oldAgree : ∀ x : T.realVariables,
      g.start.val.2 x.val = m.val.2 (.inl (.inl x)) := by
    intro x
    rw [monitor]
    change g.start.val.2 x.val = σ.value (pieceEntry σ R i) x.val
    exact congrFun ((congrArg (fun s : H.State => s.val.2) start).trans signal.symm) x.val
  have old : T.joinState H h σ.horizon g.start m oldAgree = a := by
    apply T.systemTableau_state_ext H h σ.horizon
    · rw [T.joinState_system]; exact start.trans system.symm
    · rw [T.joinState_tableau]
  have jumps : Relation.ReflTransGen B.DiscreteStep a c := by
    rw [← old]
    rcases lead with same | step
    · have equal : T.joinState H h σ.horizon g.start m oldAgree = c := by
        apply T.systemTableau_state_ext H h σ.horizon
        · rw [T.joinState_system, T.joinState_system]
        · rw [T.joinState_tableau, T.joinState_tableau]; exact same
      exact equal ▸ Relation.ReflTransGen.refl
    · exact .single (T.paste_monitor_step H h σ.horizon g.start oldAgree
        (T.curve_initial_agreement H h σ.horizon g.step flow agree) step)
  let p : ProjectedFlowPiece B σ T.systemCoordinate := {
    left := g.beginTime, duration := g.duration, positive := g.positive,
    start := c, finish := d,
    curve := fun t => T.joinValuation (g.curve t)
      (T.clockLiftCurve (T.entryValue g.beginTime α (g.curve ⟨0, by simp⟩) mark) g.curve t),
    step := jointflow,
    observe := by
      intro t u time before x
      change g.curve u x = σ.value t x
      have obs := g.observe t
        ⟨by linarith [u.property.1], by linarith [g.duration_eq]⟩
      refine Eq.trans ?_ (congrFun obs x).symm
      apply congrArg (fun u => g.curve u x)
      apply Subtype.ext
      linarith }
  refine ⟨c, d, g.endTime, jumps, ?_, bound, ?_⟩
  · have time : g.beginTime + (g.duration : ℝ) = g.endTime := by linarith [g.duration_eq]
    rw [← begin, ← time]
    exact ⟨.last p⟩
  · change H.rightStateOn A T.systemVarName T.tableauVarName d ∈ T.prelimGoal h σ.horizon
    rw [T.joinState_tableau]
    apply Or.inl
    have mode : v.val.1 = empty := congrArg Prod.fst vend
    exact mode ▸ heGoal

run_elab do
  for ax in ← Lean.collectAxioms ``systemTableau_singleton_goal_word do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"

end STLTableau.Section4.Tableau
