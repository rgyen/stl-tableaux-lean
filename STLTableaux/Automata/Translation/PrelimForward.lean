import STLTableaux.Automata.Translation.EndPositionCorrectness
import STLTableaux.Automata.Translation.PrelimEntryTimes

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State) (h : T.TranslationReady)
variable (σ : FiniteSignal Var)
local notation "H" => (T.endPositionAutomaton h σ.horizon)

/-- A nonempty observed flow word ending in an ordinary goal, with no final tail. -/
def OrdinaryGoalWord (s : (H).State) (t : ℝ) : Prop :=
  ∃ (a b : (H).State) (z : ℝ), Relation.ReflTransGen (H).DiscreteStep s a ∧
    T.FlowWord H σ a t b z ∧ b.val.1 ∈ T.goalModes ∧ z ≤ σ.horizon

private theorem pieceOfMove (P : IntervalPartition σ.domain) (i : Fin P.size)
    {s b : (H).State} (move : T.PieceEvolution h σ P i s b)
    (hd : 0 < STLTableau.Judgement.duration P i) :
    ∃ piece : T.FlowPiece H σ, piece.start = s ∧ piece.finish = b ∧
      piece.left = (P.interval i).left ∧
      piece.left + (piece.duration : ℝ) = (P.interval i).right := by
  rcases move with ⟨hz, _⟩ | ⟨_, γ, step, obs, _⟩
  · exact (hd.ne' hz).elim
  · let piece : T.FlowPiece H σ := {
      left := (P.interval i).left
      duration := STLTableau.Judgement.duration P i
      positive := hd
      start := s
      finish := b
      curve := γ
      flow := step
      obs := by
        intro t u he hu x
        rw [obs u hu x]
        exact congrArg (fun v : σ.Time => σ.value v x.val) (Subtype.ext he) }
    refine ⟨piece, rfl, rfl, rfl, ?_⟩
    change (P.interval i).left + ((P.interval i).right - (P.interval i).left) = _
    ring

private theorem prependOrdinary (P : IntervalPartition σ.domain) (i : Fin P.size)
    {s b c : (H).State} (move : T.PieceEvolution h σ P i s b)
    (jump : (H).DiscreteStep b c) (tail : T.OrdinaryGoalWord h σ c (P.interval i).right) :
    T.OrdinaryGoalWord h σ s (P.interval i).left := by
  obtain ⟨a, y, z, lead, word, goal, stop⟩ := tail
  by_cases hz : STLTableau.Judgement.duration P i = 0
  · have hbs : b = s := by
      rcases move with m | m
      · exact m.2
      · exact (m.1.ne' hz).elim
    have ht : (P.interval i).left = (P.interval i).right := by
      have hh := congrArg (fun v : NNReal => (v : ℝ)) hz
      change (P.interval i).right - (P.interval i).left = 0 at hh
      linarith
    exact ⟨a, y, z, lead.head (hbs ▸ jump), ht ▸ word, goal, stop⟩
  · obtain ⟨piece, hs, hb, hl, hr⟩ :=
      T.pieceOfMove h σ P i move (pos_iff_ne_zero.mpr hz)
    have hw := FlowWord.cons piece (Relation.TransGen.head' (hb ▸ jump) lead) (hr ▸ word)
    exact ⟨s, y, z, .refl, hs ▸ hl ▸ hw, goal, stop⟩

private theorem firstState (p : Path Clock State) (hp : p.valid T) :
    p.firstState ∈ T.states := by cases p <;> first | exact hp | exact hp.1

private theorem headHolds (p : Path Clock State) (finite : ∀ q, (T.label q).Finite)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k)
    (hp : (p.trace T.label finite).holds σ P α k) :
    (∀ g ∈ p.firstIncoming.guards, g.holds α) ∧
      ∀ l ∈ T.label p.firstState, l.holds σ P (p.firstIncoming.resets.apply α) k := by
  cases p with
  | last => exact hp
  | step => exact hp.1

/-- Structural induction on the supplied run. This result covers exactly
the case in which its last state is on an actual partition interval.
It does not assert that every recognized run has that property. -/
theorem interval_run_to_ordinary_word (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (finite : ∀ q, (T.label q).Finite)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (singleton : ∀ (i : Fin P.size) (q : T.states) (α : ClockValuation Clock) (s : (H).State),
      s.val = (q, T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
        (P.interval i).leftBoundary) →
      (∀ l ∈ T.label q.val, l.holds σ P α ⟨i.val, by omega⟩) →
      q ∈ T.goalModes → STLTableau.Judgement.duration P i = 0 →
      T.OrdinaryGoalWord h σ s (P.interval i).left)
    (p : Path Clock State) (ha : p.accepting T) (i : Fin P.size)
    (fits : i.val + (p.trace T.label finite).length ≤ P.size)
    (α : ClockValuation Clock)
    (hs : (p.trace T.label finite).holds σ P α ⟨i.val, by omega⟩)
    (s : (H).State)
    (entry : s.val = (⟨p.firstState, T.firstState p ha.1⟩,
      T.entryValue (P.interval i).left (p.firstIncoming.resets.apply α)
        (σ.value (pieceEntry σ P i)) (P.interval i).leftBoundary)) :
    T.OrdinaryGoalWord h σ s (P.interval i).left := by
  induction p generalizing i α s with
  | last l q =>
    let q' : T.states := ⟨q, ha.1⟩
    by_cases hz : STLTableau.Judgement.duration P i = 0
    · exact singleton i q' _ s entry hs.2 ha.2 hz
    · obtain ⟨b, move⟩ := T.exists_piece_exit h σ φ hw P i q' (l.resets.apply α)
        s entry hs.2 (input q')
      obtain ⟨piece, hstart, hfinish, hleft, hr⟩ :=
        T.pieceOfMove h σ P i move (pos_iff_ne_zero.mpr hz)
      have hmode := (move.registers T h σ P i).1
      have goal : b.val.1 ∈ T.goalModes :=
        hmode ▸ (show s.val.1 ∈ T.goalModes from entry ▸ ha.2)
      exact ⟨s, b, (P.interval i).right, .refl,
        hstart ▸ hfinish ▸ hleft ▸ hr ▸ FlowWord.last piece, goal, P.right_le_domain_right i⟩
  | step l q tail ih =>
    let q' : T.states := ⟨q, ha.1.1⟩
    let β := ClockResetSet.elapse (l.resets.apply α) (STLTableau.Judgement.duration P i)
    have hs' : (tail.trace T.label finite).holds σ P β ⟨i.val + 1, by omega⟩ := by
      simpa only [Trace.holds, dif_pos i.isLt] using hs.2
    have hhead := T.headHolds σ tail finite P β _ hs'
    have hvalid := ha.1.2.1
    let target : T.states := ⟨tail.firstState, T.firstState tail hvalid⟩
    have positive := Trace.length_pos (tail.trace T.label finite)
    have hlen : i.val + ((tail.trace T.label finite).length + 1) ≤ P.size := fits
    have hmore : i.val + 1 < P.size := by omega
    let j : Fin P.size := ⟨i.val + 1, hmore⟩
    obtain ⟨b, s', move, jump, en⟩ := T.ordinary_piece_transition h σ φ hw P i j rfl
      q' target tail.firstIncoming ha.1.2.2 (l.resets.apply α) s entry hs.1.2
      (input q') hhead.1 hhead.2 (input target)
    have hp := ih ⟨hvalid, ha.2⟩ j (by dsimp [j]; omega) β hs' s' en
    apply T.prependOrdinary h σ P i move jump
    exact (P.adjacent_right_eq_left i hmore).symm ▸ hp

/-- Forward construction for a given recognized run ending on an interval.
No horizon jump, formula induction or fresh tableau edge is used. -/
theorem prelim_forward_of_interval_run (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (finite : ∀ q, (T.label q).Finite)
    (p : Path Clock State) (run : p.run T) (acc : p.accepting T)
    (allα : ∀ α, (p.trace T.label finite).holds σ P α ⟨0, by omega⟩)
    (fits : (p.trace T.label finite).length ≤ P.size)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    ∃ aug, T.TypedProjectsTo aug σ ∧
      (T.prelimAutomaton h σ.horizon).PrelimReaches aug T.goalModes := by
  let α : ClockValuation Clock := fun _ => 0
  have size := P.size_pos_of_domain_nonempty
    (show σ.domain.Nonempty from ⟨0, le_rfl, σ.horizon_pos⟩)
  let i : Fin P.size := ⟨0, size⟩
  let q : T.states := ⟨p.firstState, T.firstState p run.1⟩
  have hs := allα α
  have hh := T.headHolds σ p finite P α ⟨0, by omega⟩ hs
  obtain ⟨init, hinit, entry⟩ := T.initial_piece h σ P size q p.firstIncoming run.2
    α hh.1 hh.2
  have plan : T.OrdinaryGoalWord h σ init (P.interval i).left := by
    apply T.interval_run_to_ordinary_word h σ φ hw P finite input _ p acc i
      (by simpa [i] using fits) α hs init entry
    intro j f β s hv labels goal hz
    obtain ⟨piece, hle, hre, _, jumps, _, hend⟩ := T.forward_singleton_goal h σ P j f β s hv hz
      goal labels empty heGoal heLab continuation
    refine ⟨piece.start, piece.finish, σ.horizon, jumps, ?_, hend, le_rfl⟩
    have word := FlowWord.last piece
    rw [hre] at word
    rw [hle] at word
    exact word
  obtain ⟨a, b, z, lead, word, goal, stop⟩ := plan
  have hz : (P.interval i).left = 0 := P.first_left_eq_domain_left size σ.horizon_pos
  rw [hz] at word
  obtain ⟨aug, proj, reaches⟩ := word.reaches_prelim init hinit lead stop T.goalModes goal
  exact ⟨aug, proj, T.endPosition_prelimReaches h σ.horizon reaches⟩

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => (localClosureGraph (Clock := Clock) X root)

/-- Concrete graph instance of the interval-final case; the extra length
hypothesis is explicit and is not asserted for every accepting run. -/
theorem local_prelim_forward_of_interval_run (h : (U).TranslationReady)
    (σ : FiniteSignal Var) (hw : SignalAtomRightContinuous σ root.val)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (P : IntervalPartition σ.domain) (p : Path Clock (Section3.TransitionForm Clock Var))
    (run : p.run U) (acc : p.accepting U)
    (allα : ∀ α, (p.trace (U).label JudgementTableau.labels_finite).holds σ P α ⟨0, by omega⟩)
    (fits : (p.trace (U).label JudgementTableau.labels_finite).length ≤ P.size) :
    ∃ aug, (U).TypedProjectsTo aug σ ∧
      ((U).prelimAutomaton h σ.horizon).PrelimReaches aug (U).goalModes := by
  obtain ⟨empty, _, goal, labels, continuation⟩ :=
    local_empty_continuation_data (Clock := Clock) X root
  apply (U).prelim_forward_of_interval_run h σ root.val hw P
    JudgementTableau.labels_finite p run acc allα fits _ empty goal labels continuation
  intro q a ha
  have hs := localClosure_atom_subformula X root q a ha
  exact ⟨nonStrict a hs, hs⟩

/-- Discharges the initial-mode premise for the implemented normalized input graph.
This is a statement about actual mode visits, not about tableau trace positions. -/
theorem local_prelim_visits_nonterminal {τ : ℝ} (h : (U).TranslationReady)
    {aug : FiniteSignal (U).TypedVar}
    (e : ((U).prelimAutomaton h τ).PrelimExecution aug) (hh : aug.horizon = τ)
    (q : (U).states) (visit : e.VisitsMode q) : q ∉ (U).terminalModes := by
  obtain ⟨l, hi, _, _, _, _, _⟩ := e.initial_mem
  have first : e.initialState.val.1 ∉ (U).terminalModes := by
    exact finiteRootTableau_initial_nonterminal X root.val _ hi.1
  exact (U).prelim_visits_nonterminal h τ e hh first q visit

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``Tableau.interval_run_to_ordinary_word,
      ``Tableau.prelim_forward_of_interval_run, ``local_prelim_forward_of_interval_run,
      ``Tableau.prelim_visits_nonterminal, ``local_prelim_visits_nonterminal] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
