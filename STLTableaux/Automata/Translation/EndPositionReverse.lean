import STLTableaux.Automata.Recognition.EndPositionPrefix
import STLTableaux.Automata.Translation.LocalClosureGraph

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)
local notation "New" => (T.endPositionAutomaton h τ)

theorem end_edge_clock_reset {a b : (𝓗).State} (hj : (New).DiscreteStep a b) :
    ∃ l, (a.val.1.val,l,b.val.1.val) ∈ T.edges ∧ T.guardsHold l (T.old a.val.2) ∧
      T.ClockAgree (T.old b.val.2) (T.reset l.resets (T.old a.val.2)) := by
  obtain ⟨edge,hs,ht,_,_,hg,hr,hclock,_⟩ := hj
  exact ⟨edge.val.2.1, by rw [← hs, ← ht]; exact edge.property, hg,
    hr, hclock⟩

theorem prepend_end_visit {a b c : (𝓗).State} {r : NNReal}
    (he : T.ClockElapse (T.old a.val.2) (T.old b.val.2) r)
    (hs : a.val.1 = b.val.1) (hj : (New).DiscreteStep b c)
    {ds w qs} (tail : ∀ l : EdgeLabel Clock, ∃ p : Path Clock State,
      p.firstIncoming = l ∧ p.firstState = c.val.1.val ∧ p.valid T ∧ visitModes p = qs ∧
      T.TimedPath p (T.old c.val.2) w ds)
    (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.firstIncoming = incoming ∧ p.firstState = a.val.1.val ∧
      p.valid T ∧ visitModes p = a.val.1.val :: qs ∧
      T.TimedPath p (T.old a.val.2) w (r :: ds) := by
  obtain ⟨l,hedge,hguard,hreset⟩ := T.end_edge_clock_reset h τ hj
  obtain ⟨p,hl,hq,hvalid,hm,ht⟩ := tail l
  refine ⟨.step incoming a.val.1.val p,rfl,rfl,⟨a.val.1.property,hvalid,?_⟩,
    congrArg (List.cons _) hm,?_⟩
  · simpa only [hl,hq,hs] using hedge
  · apply TimedPath.step _ _ he
    · simpa only [hl] using hguard
    · rw [hl]
      exact ht.entry_clock_congr T hreset

private def EndPrefixTail (s : (𝓗).State) (w : T.HAVar → ℝ) (ds : List NNReal)
    (qs : List State) : Prop := ∀ l : EdgeLabel Clock, ∃ p : Path Clock State,
  p.firstIncoming = l ∧ p.firstState = s.val.1.val ∧ p.valid T ∧ visitModes p = qs ∧
    T.TimedPath p (T.old s.val.2) w ds

private theorem endPrefixFlowDuration {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) : T.visitDuration h τ
      ⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩ = e.duration i := by
  change (e.boundary i.succ - e.boundary i.castSucc).toNNReal = _
  have hd : e.boundary i.succ - e.boundary i.castSucc = e.duration i := (e.duration_eq i).symm
  rw [hd]
  simp

/-- Fold all visits preceding a flow, retaining their modes and durations. -/
private theorem endPrefixTiming {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {w ds qs}
    (tail : T.EndPrefixTail h τ (e.start i) w ds qs) :
    T.EndPrefixTail h τ e.initialState w (xs.map (T.visitDuration h τ) ++ ds)
      (xs.map (fun v => v.state.val.1.val) ++ qs) := by
  induction hp generalizing ds qs with
  | initial same => simpa [same] using tail
  | initialJump step =>
    simpa [visitDuration,EndPrefixTail] using T.prepend_typed_visit h τ
      (ClockElapse.zero T _) rfl step tail
  | @direct i j xs hn pre step ih =>
    have hh := ih (T.prepend_typed_visit h τ (T.typed_flow_clock_elapse h τ e i)
      (e.continuousStep i).1 step tail)
    simpa [List.map_append,endPrefixFlowDuration] using hh
  | @viaPoint i j xs hn pre s enter leave ih =>
    have mid := T.prepend_typed_visit h τ (ClockElapse.zero T _) rfl leave tail
    have hh := ih (T.prepend_typed_visit h τ (T.typed_flow_clock_elapse h τ e i)
      (e.continuousStep i).1 enter mid)
    have hd : e.boundary i.succ - e.boundary i.castSucc = e.duration i := (e.duration_eq i).symm
    simpa [List.map_append,visitDuration, hd] using hh

private theorem endPrefixModesLast (p : Path Clock State) :
    (visitModes p).getLast? = some p.lastState := by
  induction p with
  | last => rfl
  | step _ _ p ih => simp [visitModes,List.getLast?_cons,ih,Path.lastState]

theorem endGoal_cut_timed_run {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs)
    (q : (New).State) (jump : (New).DiscreteStep (e.finish i) q)
    (endGoal : T.EndGoal q.val.1) (hb : e.boundary i.succ = τ) :
    let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
    ∃ p : Path Clock State, p.run T ∧ p.accepting T ∧
      visitModes p = vs.map (fun v => v.state.val.1.val) ++ [q.val.1.val] ∧
      ∃ u, T.guardsHold p.firstIncoming u ∧
        T.old e.initialState.val.2 = T.initialReset p.firstIncoming.resets u ∧
        T.TimedPath p (T.old e.initialState.val.2) (T.old q.val.2)
          (vs.map (T.visitDuration h τ) ++ [0]) := by
  let w := T.old q.val.2
  have tail : T.EndPrefixTail h τ q w [0] [q.val.1.val] := fun l =>
    ⟨.last l _,rfl,rfl,q.val.1.property,rfl,.last _ _ (ClockElapse.zero T _)⟩
  have lastFlow := T.prepend_end_visit h τ (T.typed_flow_clock_elapse h τ e i)
    (e.continuousStep i).1 jump tail
  obtain ⟨l,hi,u,hg,hv,_,_⟩ := e.initial_mem
  obtain ⟨p,hin,hfirst,hvalid,hm,ht⟩ := T.endPrefixTiming h τ e hp lastFlow l
  have hlast : p.lastState = q.val.1.val := by
    have he := endPrefixModesLast p
    rw [hm] at he
    simpa using he.symm
  refine ⟨p,⟨hvalid,by simpa only [hin,hfirst] using hi⟩,
    ⟨hvalid,hlast ▸ endGoal.1⟩,?_,u,hin ▸ hg,hin ▸ hv,?_⟩
  · simpa using hm
  · simpa [← hb,T.endPrefixFlowDuration] using ht

private theorem end_frame_modes (p : Path Clock State) (hf : ∀ s, (T.label s).Finite)
    (j : Fin (p.trace T.label hf).length) :
    ∃ hj : j.val < (visitModes p).length,
      ((p.trace T.label hf).frameAt j).locals = T.label (visitModes p)[j.val] := by
  induction p with
  | last =>
    have hz : j.val = 0 := by have := j.isLt; simp [Path.trace,Trace.length] at *
    refine ⟨by change j.val < 1; omega,?_⟩
    simp [Path.trace,Trace.frameAt,visitModes]
  | step l s p ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ⟨by simp [visitModes],rfl⟩
    · obtain ⟨hk,he⟩ := ih k
      exact ⟨Nat.succ_lt_succ hk,he⟩

theorem run_on_endGoal_cut {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs)
    (q : (New).State) (jump : (New).DiscreteStep (e.finish i) q)
    (endGoal : T.EndGoal q.val.1) (hb : e.boundary i.succ = τ)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    :
    ∃ (P : IntervalPartition ρ.domain) (p : Path Clock State),
      T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P ∧
      p.run T ∧ p.accepting T ∧ p.lastState = q.val.1.val ∧
      ∀ α, (p.trace T.label hf).holds ρ P α ⟨0,by omega⟩ := by
  let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
  have hρ : τ = ρ.horizon := hh.symm.trans proj.1
  obtain ⟨Q,qn,qa⟩ := T.cut_partition_atoms h τ e hp
    ((e.increasing Fin.castSucc_lt_succ).trans_eq hb) hb.ge
  change Q.size = vs.length at qn
  let R : IntervalPartition ρ.domain := { Q with covers := Q.covers.trans (congrArg (Set.Ico 0) hρ) }
  have rlayout : T.CutLayout h τ ρ vs τ R :=
    ⟨qn.ge, fun j => ⟨(qa j).1,(qa j).2.1,(qa j).2.2.1⟩,fun _ => qn,
      fun h => (h.ne hρ).elim⟩
  obtain ⟨p,run,acc,hm,u,hg,hv,timed⟩ := T.endGoal_cut_timed_run h τ e hp q jump endGoal hb
  change visitModes p = vs.map _ ++ [_] at hm
  have ord := T.ordinary_visits_of_initial h τ e hh hi hp
  have ordAll : ∀ v ∈ vs, v.state.val.1 ∉ T.terminalModes := by
    intro v hmem
    rcases List.mem_append.mp hmem with old | last
    · exact ord.1 v old
    · obtain rfl := List.mem_singleton.mp last
      exact ord.2
  have mode_last (s : Path Clock State) : (visitModes s).getLast? = some s.lastState := by
    induction s with
    | last => rfl
    | step l q s ih => simp [visitModes,List.getLast?_cons,ih,Path.lastState]
  have hlast := mode_last p
  rw [hm] at hlast
  refine ⟨R,p,rlayout,run,acc,by simpa using hlast.symm,?_⟩
  refine timed.forall_trace_holds_of_initialReset T T.label hf ρ R ?_ ?_ u hg hv (closed p run) ?_
  · change (vs.map (T.visitDuration h τ) ++ [0]).length ≤ Q.size+1
    simp [qn]
  · intro j hj
    change j.val+1 < (vs.map (T.visitDuration h τ) ++ [0]).length at hj
    simp only [List.length_append,List.length_map,List.length_singleton] at hj
    let k : Fin vs.length := ⟨j.val,by omega⟩
    have hl := (qa k).1
    have hr := (qa k).2.1
    have hnon := (STLTableau.Judgement.duration Q ⟨k.val,qn.symm ▸ k.isLt⟩).coe_nonneg
    change 0 ≤ (Q.interval _).right - (Q.interval _).left at hnon
    rw [hl,hr] at hnon
    rw [List.getElem_append_left (by simpa only [List.length_map] using k.isLt),List.getElem_map]
    change ((vs[k.val].right - vs[k.val].left).toNNReal : ℝ) = (Q.interval _).right - _
    rw [Real.coe_toNNReal _ hnon,hl,hr]
  · intro j β l hmem
    obtain ⟨hj,he⟩ := T.end_frame_modes p hf j
    rw [he] at hmem
    simp only [hm] at hj hmem
    by_cases hk : j.val < vs.length
    · let k : Fin vs.length := ⟨j.val,hk⟩
      rw [List.getElem_append_left (by simpa only [List.length_map] using hk),List.getElem_map] at hmem
      have hvs := List.getElem_mem (l := vs) hk
      have ha := qa k
      apply (Finiteness.normalizedReady_labels_hold_iff T _ (ready _ hvs) ρ R β _
        (show j.val < R.size from qn.symm ▸ hk)).2 _ l hmem
      refine ⟨ordAll _ hvs,fun m hm => ha.2.2.1.trans (T.label_eq_visitMarker h τ _ m hm),?_⟩
      intro a hat t ht
      let t' : σ.Time := ⟨t.val,t.property.1,t.property.2.trans_eq proj.1.symm⟩
      exact (T.atomHolds_iff a _ _ (h.atom_variables _ vs[k.val].state.val.1.property a hat)
        (proj.2 t' t rfl)).mp (ha.2.2.2 t' ht a hat)
    · have hlast : j.val = vs.length := by simp at hj; omega
      have hpos : j.val = R.size := hlast.trans qn.symm
      rw [List.getElem_append_right (by simpa only [List.length_map] using le_of_not_gt hk)] at hmem
      simp [hlast] at hmem
      rcases endGoal.2 l hmem with rfl | rfl
      · exact hpos
      · simp [Local.holds,Local.toJudgement,Section3.Judgement.holds,hpos]


end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ)
local notation "H" => T.endPositionAutomaton h τ

/-- Partitions induced by an execution of the end-position automaton. The
auxiliary prefix shares its initial state, positive flows, and times. A
horizon cut retains the final jump block. -/
inductive EndInducedPartition {σ : FiniteSignal T.TypedVar} (e : (H).Execution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain) : Prop
  | ordinary {i xs cut}
      (hp : BeforeFlow T h τ (T.oldPrefix h τ e hh) i xs)
      (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
      (goal : (e.start i).val.1 ∈ T.goalModes)
      (layout : T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P)
  | horizon {i xs}
      (hp : BeforeFlow T h τ (T.oldPrefix h τ e hh) i xs)
      (last : i.val+1 = e.count)
      (atEnd : e.boundary i.succ = τ)
      (jumps : Relation.TransGen (H).DiscreteStep (e.finish i) e.finalState)
      (layout : T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P)

theorem end_nonempty_horizon_chain {a b : (H).State}
    (chain : Relation.TransGen (H).DiscreteStep a b) (he : a.val.2 (.inl T.globalClock) = τ) :
    (H).DiscreteStep a b ∧ T.EndGoal b.val.1 := by
  obtain ⟨z,step,tail⟩ := Relation.TransGen.head'_iff.mp chain
  obtain ⟨goal,_,no⟩ := T.horizon_step_last h τ step he
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp tail with eq | tail'
  · subst b
    exact ⟨step,goal⟩
  · obtain ⟨x,bad,_⟩ := Relation.TransGen.head'_iff.mp tail'
    exact (no x bad).elim

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => localClosureGraph (Clock := Clock) X root

/-- Every partition induced by an execution of the end-position automaton is
recognized by the tableau. For a horizon cut, the run includes the final edge. -/
theorem endPosition_reverse {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).endPositionAutomaton h τ).Execution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (P : IntervalPartition ρ.domain) (induced : (U).EndInducedPartition h τ e hh ρ P) :
    (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).oldPrefix h τ e hh
  cases induced with
  | ordinary hp hl hr goal layout =>
    exact localClosure_ordinary X root h pre ρ proj hp hl hr goal hh P layout
  | @horizon i xs hp _ atEnd jumps layout =>
    have hg := ((U).end_finish_time h τ e i).trans atEnd
    obtain ⟨step,endGoal⟩ := (U).end_nonempty_horizon_chain h τ jumps hg
    obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
    obtain ⟨Q,p,hQ,hr,ha,_,hs⟩ := (U).run_on_endGoal_cut h τ pre ρ proj hp e.finalState
      step endGoal atEnd hh (finiteRootTableau_initial_nonterminal X root.val _ hi.1)
      JudgementTableau.labels_finite (localClosure_closed X root)
      (localClosure_visits_ready X root h pre hp τ)
    have he := hQ.unique (U) h τ layout (hh.symm.trans proj.1).le
    exact he ▸ (show (U).recognizes JudgementTableau.labels_finite ρ Q from ⟨p,hr,ha,hs⟩)

/-- A positive-flow cut induces a partition of the signal domain. -/
theorem endPosition_partition_of_ordinaryCut {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).endPositionAutomaton h τ).Execution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (i : Fin e.count) {cut : ℝ} (hl : e.boundary i.castSucc < cut)
    (hr : cut ≤ e.boundary i.succ) (goal : (e.start i).val.1 ∈ (U).goalModes) :
    ∃ P : IntervalPartition ρ.domain,
      (U).EndInducedPartition h τ e hh ρ P ∧ (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).oldPrefix h τ e hh
  obtain ⟨xs,hp⟩ := (U).exists_beforeFlow h τ pre i
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have hi' := finiteRootTableau_initial_nonterminal X root.val _ hi.1
  obtain ⟨past,now⟩ := (U).ordinary_visits_of_initial h τ pre hh hi' hp
  have ord : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ (U).terminalModes := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact past v old
    · obtain rfl := List.mem_singleton.mp last
      exact now
  have hc := hr.trans ((e.increasing.monotone (Fin.le_last i.succ)).trans e.last_le_horizon)
  obtain ⟨P,layout,rec⟩ := (U).ordinary_cut_layout_trace_through h τ pre ρ
    (proj.through U hc) hp hl hr goal JudgementTableau.labels_finite (localClosure_closed X root)
    (localClosure_visits_ready X root h pre hp cut) ord
  exact ⟨P,.ordinary hp hl hr goal layout,rec⟩

/-- A final nonempty jump block at the horizon has an induced partition,
including when the actual final state has a closed marker but no star. -/
theorem endPosition_partition_of_horizonCut {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).endPositionAutomaton h τ).Execution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (i : Fin e.count) (last : i.val+1=e.count) (atEnd : e.boundary i.succ = τ)
    (jumps : Relation.TransGen ((U).endPositionAutomaton h τ).DiscreteStep
      (e.finish i) e.finalState) :
    ∃ P : IntervalPartition ρ.domain,
      (U).EndInducedPartition h τ e hh ρ P ∧ (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).oldPrefix h τ e hh
  obtain ⟨xs,hp⟩ := (U).exists_beforeFlow h τ pre i
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  obtain ⟨step,endGoal⟩ := (U).end_nonempty_horizon_chain h τ jumps
    (((U).end_finish_time h τ e i).trans atEnd)
  obtain ⟨P,p,layout,hr,ha,_,hs⟩ := (U).run_on_endGoal_cut h τ pre ρ proj hp e.finalState
    step endGoal atEnd hh (finiteRootTableau_initial_nonterminal X root.val _ hi.1)
    JudgementTableau.labels_finite (localClosure_closed X root)
    (localClosure_visits_ready X root h pre hp τ)
  exact ⟨P,.horizon hp last atEnd jumps layout,p,hr,ha,hs⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``Tableau.end_nonempty_horizon_chain,``endPosition_reverse,
      ``endPosition_partition_of_ordinaryCut,``endPosition_partition_of_horizonCut] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
