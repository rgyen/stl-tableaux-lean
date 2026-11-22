import STLTableaux.Automata.Translation.EmptyContinuationSupport
import STLTableaux.Automata.Translation.PrelimStateGoal

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State) (h : T.TranslationReady)

/-- Follow the accepting path to construct a flow-ending execution. At the
horizon the last edge supplies a certificate for the state goal. -/
theorem prelim_stateGoal_forward (σ : FiniteSignal Var) (φ : Formula Var)
    (hw : SignalAtomRightContinuous σ φ) (P : IntervalPartition σ.domain)
    (finite : ∀ q, (T.label q).Finite) (hrec : T.recognizes finite σ P)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    ∃ aug, T.TypedProjectsTo aug σ ∧
      (T.prelimAutomaton h σ.horizon).PrelimReachesState aug
        (T.prelimGoal h σ.horizon) := by
  obtain ⟨p, run, acc, allα⟩ := hrec
  let α : ClockValuation Clock := fun _ => 0
  have size := P.size_pos_of_domain_nonempty
    (show σ.domain.Nonempty from ⟨0, le_rfl, σ.horizon_pos⟩)
  let i : Fin P.size := ⟨0, size⟩
  let q : T.states := ⟨p.firstState, by cases p <;> first | exact run.1 | exact run.1.1⟩
  have hs := allα α
  have hh : (∀ g ∈ p.firstIncoming.guards, g.holds α) ∧
      ∀ l ∈ T.label q.val, l.holds σ P (p.firstIncoming.resets.apply α)
        ⟨0, by omega⟩ := by
    cases p <;> first | exact hs | exact hs.1
  obtain ⟨init, hinit, entry⟩ := T.initial_piece h σ P size q p.firstIncoming run.2
    α hh.1 hh.2
  have plan : T.GoalWord h σ init (P.interval i).left := by
    apply T.trace_to_plan h σ φ hw P finite input _ p acc i α hs init entry
    intro j f β s hv labels goal hz
    obtain ⟨piece, hle, hre, _, jumps, _, hend⟩ := T.forward_singleton_goal h σ P j f β s hv hz
      goal labels empty heGoal heLab continuation
    refine ⟨piece.start, piece.finish, σ.horizon, jumps, ?_, Or.inl ⟨hend, le_rfl⟩⟩
    have word := FlowWord.last piece
    rw [hre, hle] at word
    exact word
  obtain ⟨a, b, z, lead, word, last⟩ := plan
  have hz : (P.interval i).left = 0 := P.first_left_eq_domain_left size σ.horizon_pos
  rw [hz] at word
  have stop : z ≤ σ.horizon := by rcases last with h | h <;> first | exact h.2 | exact h.1.le
  obtain ⟨aug, proj, e, hend, endTime⟩ := word.prelim_execution init hinit lead stop
  let current := T.endPosition_to_prelim h σ.horizon e
  have goal : current.finalState ∈ T.prelimGoal h σ.horizon := by
    rcases last with ⟨hg, _⟩ | ⟨he, c, step, _⟩
    · exact Or.inl (hend.symm ▸ hg)
    · have ht : b.val.2 (.inl T.globalClock) = σ.horizon := by
        have hb := T.prelim_final_time h σ.horizon current
        have hc : current.finalState = b := hend
        rw [hc] at hb
        exact hb.trans (endTime.trans he)
      exact hend.symm ▸ T.prelimGoal_of_end_edge h σ.horizon step ht
  exact ⟨aug, proj, current, current.finalState, goal, current.visits_finalState⟩

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root

/-- Specialize the forward construction to the tableau with empty continuation. -/
theorem empty_prelim_stateGoal_forward (h : (U).TranslationReady)
    (σ : FiniteSignal Var) (hw : SignalAtomRightContinuous σ root.val)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (P : IntervalPartition σ.domain)
    (recognized : (U).recognizes JudgementTableau.labels_finite σ P) :
    ∃ aug, (U).TypedProjectsTo aug σ ∧
      ((U).prelimAutomaton h σ.horizon).PrelimReachesState aug
        ((U).prelimGoal h σ.horizon) := by
  obtain ⟨empty, _, goal, labels, continuation⟩ :=
    empty_continuation_data (Clock := Clock) X root
  apply (U).prelim_stateGoal_forward h σ root.val hw P JudgementTableau.labels_finite
    recognized _ empty goal labels continuation
  intro q a ha
  have hs := emptyContinuation_atom_subformula X root q a ha
  exact ⟨nonStrict a hs, hs⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``Tableau.prelim_stateGoal_forward, ``empty_prelim_stateGoal_forward] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
