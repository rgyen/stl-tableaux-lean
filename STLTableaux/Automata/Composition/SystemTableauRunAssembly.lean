import STLTableaux.Automata.Composition.SystemTableauSingletonWord
import STLTableaux.Automata.Recognition.PrelimBoundedPartition

/-! Follow the given accepting tableau path over the refined actual SYSTEM
execution. Clock/reset values are threaded by the trace recursion, not chosen
independently per edge. This module makes no induction on the STL formula. -/
namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)
variable (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
variable {σ : FiniteSignal Var} (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
variable (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
variable (actions : ∀ (i j : Fin R.size), i.val + 1 = j.val →
  e.cellExitState full R fine i = e.cellEntryState full R fine j ∨
    H.DiscreteStep (e.cellExitState full R fine i) (e.cellEntryState full R fine j))
variable (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
variable (input : ∀ (q : T.states) a,
  Local.predicate (.plain (.atom a)) ∈ T.label q.val →
    a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
local notation "A" => T.prelimAutomaton h σ.horizon
local notation "B" => T.systemTableauAutomaton H h σ.horizon
local notation "left" => H.leftStateOn A T.systemVarName T.tableauVarName
local notation "right" => H.rightStateOn A T.systemVarName T.tableauVarName

include actions φ hw input in
private theorem next_entry (i j : Fin R.size) (adj : i.val + 1 = j.val)
    (q q' : T.states) (l : EdgeLabel Clock) (edge : (q.val, l, q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (w : T.realVariables → ℝ) (b : (B).State)
    (system : left b = e.cellExitState full R fine i)
    (exit : (right b).val = (q, T.forwardCurveValue
      (T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
        (R.interval i).leftBoundary) (STLTableau.Judgement.duration R i) w))
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ R α ⟨i.val, by omega⟩)
    (guards : ∀ g ∈ l.guards,
      g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration R i)))
    (labels' : ∀ loc ∈ T.label q'.val, loc.holds σ R
      (l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration R i)))
      ⟨j.val, by omega⟩) :
    let β := l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration R i))
    ∃ c : (B).State, (B).DiscreteStep b c ∧ left c = e.cellEntryState full R fine j ∧
      (right c).val = (q', T.entryValue (R.interval j).left β
        (σ.value (pieceEntry σ R j)) (R.interval j).leftBoundary) := by
  intro β
  obtain ⟨c, entry, jump⟩ := T.prelim_jump_after_cell h σ R i j adj q q' l edge
    α _ w (right b) exit labels guards labels'
    (T.piece_entry_atoms σ φ hw R j q' β labels' (input q'))
  have agree : ∀ x : T.realVariables, (left b).val.2 x.val =
      (right b).val.2 (.inl (.inl x)) := by
    intro x
    exact H.parallelOn_shared_value A T.systemVarName T.tableauVarName b rfl
  have agree' : ∀ x : T.realVariables, (e.cellEntryState full R fine j).val.2 x.val =
      c.val.2 (.inl (.inl x)) := by
    intro x
    rw [entry]
    change (e.cellEntryState full R fine j).val.2 x.val = σ.value (pieceEntry σ R j) x.val
    rw [e.cell_entry_signal full R fine j]
  let out := T.joinState H h σ.horizon (e.cellEntryState full R fine j) c agree'
  have rejoin : T.joinState H h σ.horizon (left b) (right b) agree = b := by
    apply T.systemTableau_state_ext H h σ.horizon
    · exact T.joinState_system H h σ.horizon _ _ _
    · exact T.joinState_tableau H h σ.horizon _ _ _
  refine ⟨out, ?_, T.joinState_system H h σ.horizon _ _ _, ?_⟩
  · rcases actions i j adj with idle | move
    · have same : left b = e.cellEntryState full R fine j := system.trans idle
      have step := T.paste_monitor_step H h σ.horizon (left b) agree
        (by rw [same]; exact agree') jump
      rw [rejoin] at step
      simpa only [same] using step
    · have step := T.paste_simultaneous H h σ.horizon agree agree' (system.symm ▸ move) jump
      rw [rejoin] at step
      exact step
  · rw [T.joinState_tableau]
    exact entry

private theorem systemPath_first (p : Path Clock State) (valid : p.valid T) :
    p.firstState ∈ T.states := by
  cases p <;> first | exact valid | exact valid.1

private theorem horizon_goal (i : Fin R.size) (last : i.val + 1 = R.size)
    (q target : T.states) (l : EdgeLabel Clock) (edge : (q.val, l, target.val) ∈ T.edges)
    (α : ClockValuation Clock) (w : T.realVariables → ℝ) (b : (B).State)
    (exit : (right b).val = (q, T.forwardCurveValue
      (T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
        (R.interval i).leftBoundary) (STLTableau.Judgement.duration R i) w))
    (goal : target ∈ T.goalModes)
    (guards : ∀ g ∈ l.guards,
      g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration R i)))
    (labels : ∀ loc ∈ T.label target.val, loc.holds σ R
      (l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration R i)))
      ⟨R.size, by omega⟩) : b ∈ T.systemTableauGoal H h σ.horizon := by
  have clocks (c : T.clocks) : T.old (right b).val.2 (.inr (.inl c)) =
      (ClockResetSet.elapse α (STLTableau.Judgement.duration R i) c.val : ℝ) := by
    rw [exit]
    simp [old, forwardCurveValue, entryValue, ClockResetSet.elapse]
  have allowed : T.EndGoal target := (T.endGoal_iff target σ R _).2 ⟨goal, labels⟩
  change right b ∈ T.prelimGoal h σ.horizon
  refine Or.inr ⟨?_, l, target, ?_, ?_, allowed⟩
  · rw [exit]
    change σ.horizon ≤ (R.interval i).left + ((R.interval i).right - (R.interval i).left)
    have endTime := R.last_right_eq_domain_right i last
    linarith
  · rw [congrArg Prod.fst exit]
    exact edge
  · exact (T.guardsHold_iff l _ _ (h.edge_guards _ edge) clocks).2 guards

include actions φ hw input in
/-- Induction on the GIVEN accepting path. The same incoming valuation
is reset and advanced by the current partition duration before the next
frame; singleton visits contribute a jump but never a zero-duration flow. -/
theorem trace_to_system_word (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (finite : ∀ q, (T.label q).Finite)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty)
    (p : Path Clock State) (accepting : p.accepting T) (i : Fin R.size)
    (α : ClockValuation Clock)
    (sat : (p.trace T.label finite).holds σ R α ⟨i.val, by omega⟩)
    (a : (B).State) (system : left a = e.cellEntryState full R fine i)
    (entry : (right a).val = (⟨p.firstState, T.systemPath_first p accepting.1⟩,
      T.entryValue (R.interval i).left (p.firstIncoming.resets.apply α)
        (σ.value (pieceEntry σ R i)) (R.interval i).leftBoundary)) :
    T.SystemGoalWord H h σ a (R.interval i).left := by
  induction p generalizing i α a with
  | last l q =>
    let q' : T.states := ⟨q, accepting.1⟩
    by_cases zero : (STLTableau.Judgement.duration R i : ℝ) = 0
    · exact T.systemTableau_singleton_goal_word H h e full R fine i zero q'
        accepting.2 (l.resets.apply α) sat.2 a system entry empty heGoal heLab continuation
    · have positive : 0 < (STLTableau.Judgement.duration R i : ℝ) :=
        lt_of_le_of_ne (STLTableau.Judgement.duration R i).coe_nonneg (Ne.symm zero)
      obtain ⟨piece, first, begin, duration, _, finish⟩ := T.projected_system_cell H h e full
        R fine i positive flows q' (l.resets.apply α) sat.2
        (fun atom ha => (input q' atom ha).1)
        (fun atom ha => functions atom (input q' atom ha).2) a system entry
      have bound : piece.left + (piece.duration : ℝ) ≤ σ.horizon := by
        rw [begin, duration]
        change (R.interval i).left + ((R.interval i).right - (R.interval i).left) ≤ _
        linarith [R.right_le_domain_right i]
      have goal : piece.finish ∈ T.systemTableauGoal H h σ.horizon := by
        change right piece.finish ∈ T.prelimGoal h σ.horizon
        apply Or.inl
        rw [congrArg Prod.fst finish]
        exact accepting.2
      simpa only [first, begin] using SystemGoalWord.of_piece piece bound goal
  | step l q tail ih =>
    let q' : T.states := ⟨q, accepting.1.1⟩
    let β := ClockResetSet.elapse (l.resets.apply α) (STLTableau.Judgement.duration R i)
    have tailSat : (tail.trace T.label finite).holds σ R β ⟨i.val + 1, by omega⟩ := by
      simpa only [Trace.holds, dif_pos i.isLt] using sat.2
    have valid := accepting.1.2.1
    let target : T.states := ⟨tail.firstState, T.systemPath_first tail valid⟩
    have head : (∀ g ∈ tail.firstIncoming.guards, g.holds β) ∧
        ∀ loc ∈ T.label target.val, loc.holds σ R (tail.firstIncoming.resets.apply β)
          ⟨i.val + 1, by omega⟩ := by
      cases tail <;> first | exact tailSat | exact tailSat.1
    by_cases more : i.val + 1 < R.size
    · let j : Fin R.size := ⟨i.val + 1, more⟩
      have join : (R.interval i).right = (R.interval j).left := R.adjacent_right_eq_left i more
      by_cases zero : (STLTableau.Judgement.duration R i : ℝ) = 0
      · have zd : STLTableau.Judgement.duration R i = 0 := Subtype.ext zero
        have exit : (right a).val = (q', T.forwardCurveValue
            (T.entryValue (R.interval i).left (l.resets.apply α)
              (σ.value (pieceEntry σ R i)) (R.interval i).leftBoundary)
            (STLTableau.Judgement.duration R i)
            (fun x => σ.value (pieceEntry σ R i) x.val)) := by
          rw [entry, zd]
          congr 1
          funext x
          cases x with
          | inl x => cases x <;> simp [forwardCurveValue, entryValue, Path.firstIncoming]
          | inr b => cases b <;> simp [forwardCurveValue, entryValue, dwell, bit]
        obtain ⟨c, jump, csystem, centry⟩ := T.next_entry H h e full R fine actions φ hw
          input i j rfl q' target tail.firstIncoming accepting.1.2.2 (l.resets.apply α) _ a
          (system.trans (e.singleton_cell_state full R fine i zero).symm) exit sat.1.2
          head.1 head.2
        have plan := ih ⟨valid, accepting.2⟩ j β tailSat c csystem centry
        have sameTime : (R.interval i).left = (R.interval j).left := by
          change (R.interval i).right - (R.interval i).left = 0 at zero
          linarith
        simpa only [sameTime] using SystemGoalWord.prepend_jump jump plan
      · have positive : 0 < (STLTableau.Judgement.duration R i : ℝ) :=
          lt_of_le_of_ne (STLTableau.Judgement.duration R i).coe_nonneg (Ne.symm zero)
        obtain ⟨piece, first, begin, duration, psystem, finish⟩ :=
          T.projected_system_cell H h e full R fine i positive flows q'
            (l.resets.apply α) sat.1.2 (fun atom ha => (input q' atom ha).1)
            (fun atom ha => functions atom (input q' atom ha).2) a system entry
        obtain ⟨c, jump, csystem, centry⟩ := T.next_entry H h e full R fine actions φ hw
          input i j rfl q' target tail.firstIncoming accepting.1.2.2 (l.resets.apply α) _
          piece.finish psystem finish sat.1.2 head.1 head.2
        have plan := ih ⟨valid, accepting.2⟩ j β tailSat c csystem centry
        have time : piece.left + (piece.duration : ℝ) = (R.interval j).left := by
          rw [begin, duration]
          change (R.interval i).left + ((R.interval i).right - (R.interval i).left) = _
          linarith
        have tailPlan : T.SystemGoalWord H h σ c (piece.left + piece.duration) := by
          simpa only [time] using plan
        simpa only [first, begin] using SystemGoalWord.prepend piece jump tailPlan
    · have last : i.val + 1 = R.size := by omega
      have positive : 0 < (STLTableau.Judgement.duration R i : ℝ) :=
        last_piece_positive σ R i last
      obtain ⟨piece, first, begin, duration, _, finish⟩ :=
        T.projected_system_cell H h e full R fine i positive flows q'
          (l.resets.apply α) sat.1.2 (fun atom ha => (input q' atom ha).1)
          (fun atom ha => functions atom (input q' atom ha).2) a system entry
      have targetGoal : target ∈ T.goalModes := by
        cases tail with
        | last => exact accepting.2
        | step l' q'' rest =>
          have bad := tailSat.2
          simp only [dif_neg more] at bad
      have labels : ∀ loc ∈ T.label target.val, loc.holds σ R
          (tail.firstIncoming.resets.apply β) ⟨R.size, by omega⟩ := by
        intro loc hl
        simpa only [last] using head.2 loc hl
      have goal := T.horizon_goal H h R i last q' target tail.firstIncoming accepting.1.2.2
        (l.resets.apply α) _ piece.finish finish targetGoal head.1 labels
      have bound : piece.left + (piece.duration : ℝ) ≤ σ.horizon := by
        rw [begin, duration]
        change (R.interval i).left + ((R.interval i).right - (R.interval i).left) ≤ _
        linarith [R.right_le_domain_right i]
      simpa only [first, begin] using SystemGoalWord.of_piece piece bound goal

run_elab do
  for ax in ← Lean.collectAxioms ``trace_to_system_word do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"

end STLTableau.Section4.Tableau
