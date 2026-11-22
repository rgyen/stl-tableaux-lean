import STLTableaux.Automata.Recognition.ForwardVisits
import STLTableaux.Automata.Recognition.ProjectedFlowWord
import STLTableaux.Automata.Execution.ForwardEmptyGoal

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State) (h : T.TranslationReady)
variable (σ : FiniteSignal Var)
local notation "H" => (T.endPositionAutomaton h σ.horizon)

/-- Optional leading initial/singleton jumps, a nonempty observed word,
and either an ordinary goal flow or a final horizon bookkeeping jump. -/
def GoalWord (s : (H).State) (t : ℝ) : Prop :=
  ∃ (a b : (H).State) (z : ℝ), Relation.ReflTransGen (H).DiscreteStep s a ∧
    T.FlowWord H σ a t b z ∧
      ((b.val.1 ∈ T.goalModes ∧ z ≤ σ.horizon) ∨
       (z = σ.horizon ∧ ∃ c : (H).State, (H).DiscreteStep b c ∧ c.val.1 ∈ T.goalModes))

private theorem toPiece (P : IntervalPartition σ.domain) (i : Fin P.size)
    {s b : (H).State} (move : T.PieceEvolution h σ P i s b)
    (hd : 0 < STLTableau.Judgement.duration P i) :
    ∃ piece : T.FlowPiece H σ, piece.start = s ∧ piece.finish = b ∧
      piece.left = (P.interval i).left ∧
      piece.left + (piece.duration : ℝ) = (P.interval i).right := by
  rcases move with ⟨hz,_⟩ | ⟨_,γ,hγ,obs,_⟩
  · exact (hd.ne' hz).elim
  · let piece : T.FlowPiece H σ := {
      left := (P.interval i).left
      duration := STLTableau.Judgement.duration P i, positive := hd
      start := s, finish := b, curve := γ, flow := hγ
      obs := by
        intro t u he hu x
        rw [obs u hu x]
        exact congrArg (fun v : σ.Time => σ.value v x.val) (Subtype.ext he) }
    refine ⟨piece,rfl,rfl,rfl,?_⟩
    change (P.interval i).left + ((P.interval i).right - (P.interval i).left) = _
    ring

private theorem prepend_piece (P : IntervalPartition σ.domain) (i : Fin P.size)
    {s b c : (H).State} (move : T.PieceEvolution h σ P i s b)
    (jump : (H).DiscreteStep b c) (tail : T.GoalWord h σ c (P.interval i).right) :
    T.GoalWord h σ s (P.interval i).left := by
  obtain ⟨a,y,z,lead,word,goal⟩ := tail
  by_cases hz : STLTableau.Judgement.duration P i = 0
  · have hbs : b = s := by
      rcases move with m | m
      · exact m.2
      · exact (m.1.ne' hz).elim
    have ht : (P.interval i).left = (P.interval i).right := by
      have hh := congrArg (fun v : NNReal => (v : ℝ)) hz
      change (P.interval i).right - (P.interval i).left = 0 at hh
      linarith
    exact ⟨a,y,z,lead.head (hbs ▸ jump),ht ▸ word,goal⟩
  · obtain ⟨piece,hs,hb,hl,hr⟩ := T.toPiece h σ P i move (pos_iff_ne_zero.mpr hz)
    have hw := FlowWord.cons piece (Relation.TransGen.head' (hb ▸ jump) lead) (hr ▸ word)
    exact ⟨s,y,z,.refl,hs ▸ hl ▸ hw,goal⟩

private theorem head_holds (p : Path Clock State) (finite : ∀ q, (T.label q).Finite)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : (p.trace T.label finite).holds σ P α k) :
    (∀ g ∈ p.firstIncoming.guards, g.holds α) ∧
      ∀ l ∈ T.label p.firstState, l.holds σ P (p.firstIncoming.resets.apply α) k := by
  cases p with
  | last => exact hp
  | step => exact hp.1

private theorem horizon_piece (P : IntervalPartition σ.domain) (i : Fin P.size)
    (hi : i.val+1 = P.size) {s b : (H).State}
    (α : ClockValuation Clock) (q : T.states)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary))
    (move : T.PieceEvolution h σ P i s b) (target : T.states) (l : EdgeLabel Clock)
    (hedge : (q.val,l,target.val) ∈ T.edges) (hend : T.EndGoal target)
    (hg : ∀ g ∈ l.guards, g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))) :
    T.GoalWord h σ s (P.interval i).left := by
  have hd := last_piece_positive σ P i hi
  obtain ⟨piece,hs,hb,hl,hr⟩ := T.toPiece h σ P i move (show 0 < _ from hd)
  obtain ⟨hm,hcl,hcg,hdwell,_⟩ := move.registers T h σ P i
  rw [entry] at hm hcl hcg hdwell
  have htime : b.val.2 (.inl T.globalClock) = σ.horizon := by
    change b.val.2 (.inl T.globalClock) =
      (P.interval i).left + ((P.interval i).right - (P.interval i).left) at hcg
    linarith [P.last_right_eq_domain_right i hi]
  have hpos : 0 < b.val.2 T.dwell := by
    change b.val.2 T.dwell = 0 + _ at hdwell
    linarith
  obtain ⟨c,hc,jump⟩ := T.end_entry h σ.horizon b target l (hm ▸ hedge) hend htime hpos
    (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) hcl hg (fun _ => 0)
  exact ⟨s,b,(P.interval i).right,.refl,hs ▸ hb ▸ hl ▸ hr ▸ FlowWord.last piece,
    Or.inr ⟨P.last_right_eq_domain_right i hi,c,jump,hc ▸ hend.1⟩⟩

private theorem first_valid_state (p : Path Clock State) (hp : p.valid T) :
    p.firstState ∈ T.states := by cases p <;> first | exact hp | exact hp.1

/-- Induction over the given accepting run, not over the STL formula.
The isolated singleton-goal construction supplies only the base case. -/
theorem trace_to_plan (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (finite : ∀ q, (T.label q).Finite)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (singleton : ∀ (i : Fin P.size) (q : T.states) (α : ClockValuation Clock) (s : (H).State),
      s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
        (P.interval i).leftBoundary) →
      (∀ l ∈ T.label q.val, l.holds σ P α ⟨i.val,by omega⟩) →
      q ∈ T.goalModes → STLTableau.Judgement.duration P i = 0 →
      T.GoalWord h σ s (P.interval i).left)
    (p : Path Clock State) (ha : p.accepting T) (i : Fin P.size)
    (α : ClockValuation Clock) (hs : (p.trace T.label finite).holds σ P α ⟨i.val,by omega⟩)
    (s : (H).State)
    (entry : s.val = (⟨p.firstState,T.first_valid_state p ha.1⟩,
      T.entryValue (P.interval i).left (p.firstIncoming.resets.apply α)
        (σ.value (pieceEntry σ P i)) (P.interval i).leftBoundary)) :
    T.GoalWord h σ s (P.interval i).left := by
  induction p generalizing i α s with
  | last l q =>
    let q' : T.states := ⟨q,ha.1⟩
    by_cases hz : STLTableau.Judgement.duration P i = 0
    · exact singleton i q' _ s entry hs.2 ha.2 hz
    · obtain ⟨b,move⟩ := T.exists_piece_exit h σ φ hw P i q' (l.resets.apply α)
        s entry hs.2 (input q')
      obtain ⟨piece,hstart,hfinish,hleft,hr⟩ :=
        T.toPiece h σ P i move (pos_iff_ne_zero.mpr hz)
      have hmode := (move.registers T h σ P i).1
      have hgoal : b.val.1 ∈ T.goalModes := hmode ▸ (show s.val.1 ∈ T.goalModes from entry ▸ ha.2)
      exact ⟨s,b,(P.interval i).right,.refl,hstart ▸ hfinish ▸ hleft ▸ hr ▸ FlowWord.last piece,
        Or.inl ⟨hgoal,P.right_le_domain_right i⟩⟩
  | step l q tail ih =>
    let q' : T.states := ⟨q,ha.1.1⟩
    let β := ClockResetSet.elapse (l.resets.apply α) (STLTableau.Judgement.duration P i)
    have hs' : (tail.trace T.label finite).holds σ P β ⟨i.val+1,by omega⟩ := by
      simpa only [Trace.holds,dif_pos i.isLt] using hs.2
    have hhead := T.head_holds σ tail finite P β _ hs'
    have hvalid := ha.1.2.1
    let target : T.states := ⟨tail.firstState,T.first_valid_state tail hvalid⟩
    by_cases hmore : i.val+1 < P.size
    · let j : Fin P.size := ⟨i.val+1,hmore⟩
      obtain ⟨b,s',move,jump,en⟩ := T.ordinary_piece_transition h σ φ hw P i j rfl
        q' target tail.firstIncoming ha.1.2.2 (l.resets.apply α) s entry hs.1.2
        (input q') hhead.1 hhead.2 (input target)
      have hp := ih ⟨hvalid,ha.2⟩ j β hs' s' en
      apply T.prepend_piece h σ P i move jump
      exact (P.adjacent_right_eq_left i hmore).symm ▸ hp
    · have hend : i.val+1 = P.size := by have := i.isLt; omega
      obtain ⟨b,move⟩ := T.exists_piece_exit h σ φ hw P i q' (l.resets.apply α)
        s entry hs.1.2 (input q')
      have hg : target ∈ T.goalModes := by
        cases tail with
        | last => exact ha.2
        | step l' s'' tail' =>
          have hbad := hs'.2
          simp only [dif_neg hmore] at hbad
      have endOK : T.EndGoal target := by
        apply (T.endGoal_iff target σ P (tail.firstIncoming.resets.apply β)).2
        refine ⟨hg,?_⟩
        intro x hx
        have hh := hhead.2 x hx
        simpa only [hend] using hh
      exact T.horizon_piece h σ P i hend _ q' entry move target tail.firstIncoming
        ha.1.2.2 endOK hhead.1

theorem corrected_forward (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (finite : ∀ q, (T.label q).Finite)
    (hrec : T.recognizes finite σ P)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    ∃ aug, T.TypedProjectsTo aug σ ∧ (H).Reaches aug T.goalModes := by
  obtain ⟨p,run,acc,allα⟩ := hrec
  let α : ClockValuation Clock := fun _ => 0
  have size := P.size_pos_of_domain_nonempty
    (show σ.domain.Nonempty from ⟨0,le_rfl,σ.horizon_pos⟩)
  let i : Fin P.size := ⟨0,size⟩
  let q : T.states := ⟨p.firstState,T.first_valid_state p run.1⟩
  have hs := allα α
  have hh := T.head_holds σ p finite P α ⟨0,by omega⟩ hs
  obtain ⟨init,hinit,entry⟩ := T.initial_piece h σ P size q p.firstIncoming run.2
    α hh.1 hh.2
  have initReal : ∀ x : T.realVariables, init.val.2 (.inl (.inl x)) =
      σ.value ⟨0, le_rfl, σ.horizon_pos⟩ x.val := by
    intro x
    rw [entry]
    change σ.value (pieceEntry σ P i) x.val = σ.value ⟨0, le_rfl, σ.horizon_pos⟩ x.val
    apply congrArg (fun t : σ.Time => σ.value t x.val)
    apply Subtype.ext
    exact P.first_left_eq_domain_left size σ.horizon_pos
  have plan : T.GoalWord h σ init (P.interval i).left := by
    apply T.trace_to_plan h σ φ hw P finite input _ p acc i α hs init entry
    intro j f β s hv labels goal hz
    obtain ⟨piece,hle,hre,_,jumps,_,hend⟩ := T.forward_singleton_goal h σ P j f β s hv hz
      goal labels empty heGoal heLab continuation
    exact ⟨piece.start,piece.finish,σ.horizon,jumps,by
      have word := FlowWord.last piece
      rw [hre] at word
      rw [hle] at word
      exact word,Or.inl ⟨hend,le_rfl⟩⟩
  obtain ⟨a,b,z,lead,word,last⟩ := plan
  have hz : (P.interval i).left = 0 := P.first_left_eq_domain_left size σ.horizon_pos
  rw [hz] at word
  rcases last with ⟨hg,he⟩ | ⟨he,c,jump,hg⟩
  · exact word.reaches_positive init hinit initReal lead he T.goalModes hg
  · subst z
    exact word.reaches_end init c hinit initReal lead jump T.goalModes hg

end STLTableau.Section4.Tableau
