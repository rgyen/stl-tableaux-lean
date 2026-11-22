import STLTableaux.Automata.Recognition.ProjectedFlowWord
import STLTableaux.Automata.Recognition.ForwardVisits
import STLTableaux.Automata.Translation.LocalClosureGraph

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State) (h : T.TranslationReady)

private theorem closed_singleton (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) (hz : STLTableau.Judgement.duration P i = 0) :
    (P.interval i).leftBoundary = ● := by
  have hr : (P.interval i).right - (P.interval i).left = 0 := congrArg NNReal.toReal hz
  obtain ⟨x,hx⟩ := P.nonempty i
  have ha := hx.1.resolve_left (by linarith [MarkedInterval.le_right_of_mem hx])
  cases hm : (P.interval i).leftBoundary <;> simp_all [Marker.Includes]

/-- Positive observation in an empty-labelled mode, starting at a
specified original time/value and continuing to the horizon. The right
endpoint needs no signal evaluation. -/
private theorem empty_flow_piece (σ : FiniteSignal Var) (q : T.states)
    (a : (T.endPositionAutomaton h σ.horizon).State) (time : σ.Time)
    (hmode : a.val.1 = q) (hl : T.label q.val = ∅)
    (hcg : a.val.2 (.inl T.globalClock) = time.val)
    (hx : ∀ x : T.realVariables, a.val.2 (.inl (.inl x)) = σ.value time x.val) :
    ∃ p : T.FlowPiece (T.endPositionAutomaton h σ.horizon) σ,
      p.left = time.val ∧ p.left + p.duration = σ.horizon ∧ p.start = a ∧ p.finish.val.1 = q := by
  let H := T.endPositionAutomaton h σ.horizon
  let r : NNReal := ⟨σ.horizon - time.val,sub_nonneg.mpr time.property.2.le⟩
  have hpos : 0 < r := sub_pos.mpr time.property.2
  let obsTime (u : Set.Ico (0 : ℝ) r) : σ.Time :=
    ⟨time.val+u.val,add_nonneg time.property.1 u.property.1,by
      have hr : u.val < σ.horizon-time.val := u.property.2
      linarith⟩
  let x (u : Set.Ico (0 : ℝ) r) (v : T.realVariables) := σ.value (obsTime u) v.val
  let w (v : T.realVariables) := σ.value time v.val
  obtain ⟨b,γ,step,observes,_⟩ :=
    T.forward_positive_flow h σ.horizon a r hpos x w (by
      funext v
      rw [hx]
      exact congrArg (fun z : σ.Time => σ.value z v.val)
        (show obsTime ⟨0,le_rfl,hpos⟩ = time from Subtype.ext (add_zero _))) (by
      intro _ p hp
      rw [hmode,hl] at hp
      exact hp.elim) (by
      intro p hp
      rw [hmode,hl] at hp
      exact hp.elim) (by
      intro _
      rw [hcg]
      change time.val + (σ.horizon-time.val) ≤ _
      linarith)
  let p : T.FlowPiece H σ := {
    left := time.val, duration := r, positive := hpos, start := a, finish := b, curve := γ,
    flow := step, obs := by
      intro t u ht hu v
      rw [observes u hu v]
      exact congrArg (fun z : σ.Time => σ.value z v.val)
        (show obsTime ⟨u.val,u.property.1,hu⟩ = t from Subtype.ext ht) }
  exact ⟨p,rfl,by change time.val + (σ.horizon-time.val) = _; ring,rfl,step.1.symm.trans hmode⟩

/-- The last ordinary goal is an actual singleton. Its final-to-empty
continuation is a real edge (with empty guard/reset), if it is needed.
Record literal zero versus one leading discrete step as well as the
combined ReflTransGen for direct use in the word constructor. -/
theorem forward_singleton_goal (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) (q : T.states) (α : ClockValuation Clock)
    (s : (T.endPositionAutomaton h σ.horizon).State)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary))
    (hz : STLTableau.Judgement.duration P i = 0) (hq : q ∈ T.goalModes)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P α ⟨i.val,by omega⟩)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ T.edges ∧ l.guards = ∅ ∧
        l.resets = ClockResetSet.empty) :
    let H := T.endPositionAutomaton h σ.horizon
    ∃ p : T.FlowPiece H σ, p.left = (P.interval i).left ∧ p.left + p.duration = σ.horizon ∧
      ((q = empty ∧ p.start = s) ∨ (q ≠ empty ∧ H.DiscreteStep s p.start)) ∧
      Relation.ReflTransGen H.DiscreteStep s p.start ∧
      p.start.val.1 = empty ∧ p.finish.val.1 ∈ T.goalModes := by
  let H := T.endPositionAutomaton h σ.horizon
  let t := pieceEntry σ P i
  have time : t.val = (P.interval i).left := rfl
  have start : ∃ a : H.State, a.val.1 = empty ∧ a.val.2 (.inl T.globalClock) = t.val ∧
      (∀ x : T.realVariables, a.val.2 (.inl (.inl x)) = σ.value t x.val) ∧
      ((q = empty ∧ a = s) ∨ (q ≠ empty ∧ H.DiscreteStep s a)) := by
    by_cases eq : q = empty
    · refine ⟨s,?_,?_,?_,Or.inl ⟨eq,rfl⟩⟩
      · exact (congrArg Prod.fst entry).trans eq
      · rw [entry]; rfl
      · intro x; rw [entry]; rfl
    · obtain ⟨l,he,hguards,_⟩ := continuation q hq eq
      have ht : s.val.2 (.inl T.globalClock) = t.val := by rw [entry]; rfl
      have hclosed := closed_singleton σ P i hz
      have hnon : empty ∉ T.terminalModes := by
        change Local.terminal ∉ T.label empty.val
        rw [heLab]; exact fun e => e.elim
      obtain ⟨a,ha,hj⟩ := T.forward_jump_entry h σ.horizon s empty l (by
        rw [entry]; exact he) α (fun _ => by rw [entry]; rfl) (by
          intro g hg; rw [hguards] at hg; exact hg.elim) (σ.value t) ○
        (iff_of_false hnon (by rw [ht]; exact not_le_of_gt t.property.2))
        (fun _ => ⟨by rw [entry,hclosed]; rfl,rfl⟩)
        (by intro p hP; rw [heLab] at hP; exact hP.elim)
        (by intro m hm; rw [heLab] at hm; exact hm.elim)
        (by
          intro _ p hp
          rw [entry] at hp
          have holds := labels (.predicate (.plain (.atom p))) hp
          simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos i.isLt,
            Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] at holds
          apply holds
          rw [time]
          exact (P.interval i).left_mem (P.nonempty i) (by simp [hclosed,Marker.Includes]))
      have hacg : a.val.2 (.inl T.globalClock) = t.val := by
        rw [ha]; exact ht
      refine ⟨a,congrArg Prod.fst ha,hacg,fun _ => by rw [ha]; rfl,
        Or.inr ⟨eq,(T.step_before_iff h σ.horizon (hacg ▸ t.property.2)).2 hj⟩⟩
  obtain ⟨a,ha,hacg,hx,steps⟩ := start
  obtain ⟨p,hp,hpend,hpa,hfinish⟩ := T.empty_flow_piece h σ empty a t ha heLab hacg hx
  refine ⟨p,hp.trans time,hpend,hpa ▸ steps,?_,hpa ▸ ha,hfinish ▸ heGoal⟩
  rw [hpa]
  rcases steps with ⟨_,rfl⟩ | ⟨_,hj⟩
  · exact .refl
  · exact .single hj

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => (localClosureGraph (Clock := Clock) X root)

/-- All three hypotheses on the continuation in forward_singleton_goal
are theorems on the actual local-closure tableau. -/
theorem local_empty_continuation_data :
    ∃ empty : (U).states, empty.val = emptyMode ∧ empty ∈ (U).goalModes ∧
      (U).label empty.val = ∅ ∧
      ∀ f : (U).states, f ∈ (U).goalModes → f ≠ empty →
        ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ (U).edges ∧ l.guards = ∅ ∧
          l.resets = ClockResetSet.empty := by
  let q : (U).states := ⟨emptyMode, Or.inl rfl,empty_consistent⟩
  refine ⟨q,rfl,⟨Or.inl rfl,q.property⟩,empty_label X root,?_⟩
  intro f hf hne
  exact ⟨emptyIncoming,localClosure_final_empty_edge X root hf (fun he => hne (Subtype.ext he)),
    rfl,rfl⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in #[``Tableau.forward_singleton_goal,``local_empty_continuation_data] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
