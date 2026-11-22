import STLTableaux.Automata.Recognition.TypedVisitSequence
import STLTableaux.Automata.Recognition.ExecutionTraceGuards

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)

/-- Only clock coordinates are compared: a tableau-automaton jump may
change signal variables. -/
def ClockAgree (v w : T.HAVar → ℝ) : Prop :=
  (∀ c : T.clocks, v (.inr (.inl c)) = w (.inr (.inl c))) ∧
    v T.globalClock = w T.globalClock

theorem TimedPath.entry_clock_congr {p v v' w ds} (hp : T.TimedPath p v w ds)
    (hv : T.ClockAgree v v') : T.TimedPath p v' w ds := by
  have changeEntry {u d} (he : T.ClockElapse v u d) : T.ClockElapse v' u d :=
    ⟨fun c => (he.1 c).trans (by rw [hv.1 c]), he.2.trans (by rw [hv.2])⟩
  cases hp with
  | last l s he => exact .last l s (changeEntry he)
  | step l s he hg ht => exact .step l s (changeEntry he) hg ht

theorem typed_edge_clock_reset {a b : (𝓗).State} (hj : (𝓗).DiscreteStep a b) :
    ∃ l, (a.val.1.val,l,b.val.1.val) ∈ T.edges ∧ T.guardsHold l (T.old a.val.2) ∧
      T.ClockAgree (T.old b.val.2) (T.reset l.resets (T.old a.val.2)) := by
  obtain ⟨edge,hs,ht,_,_,hg,hr,hclock,_⟩ := hj
  exact ⟨edge.val.2.1, by rw [← hs, ← ht]; exact edge.property, hg,
    hr, hclock⟩

theorem typed_flow_clock_elapse {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) : T.ClockElapse (T.old (e.start i).val.2)
      (T.old (e.finish i).val.2) (e.duration i) := by
  have hc := e.continuousStep i
  have hf := ((hc.2.2.2 ⟨e.duration i,by simp⟩).1)
  rw [hc.2.2.1] at hf
  exact ⟨hf.1,hf.2.1⟩

def visitModes : Path Clock State → List State
  | .last _ s => [s]
  | .step _ s p => s :: visitModes p

/-- Prepend a real flow and its actual outgoing jump to the rest of the path.
The very same incoming label supplies the edge, its guard and its reset. -/
theorem prepend_typed_visit {a b c : (𝓗).State} {r : NNReal}
    (he : T.ClockElapse (T.old a.val.2) (T.old b.val.2) r)
    (hs : a.val.1 = b.val.1) (hj : (𝓗).DiscreteStep b c)
    {ds w qs} (tail : ∀ l : EdgeLabel Clock, ∃ p : Path Clock State,
      p.firstIncoming = l ∧ p.firstState = c.val.1.val ∧ p.valid T ∧ visitModes p = qs ∧
      T.TimedPath p (T.old c.val.2) w ds)
    (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.firstIncoming = incoming ∧ p.firstState = a.val.1.val ∧
      p.valid T ∧ visitModes p = a.val.1.val :: qs ∧
      T.TimedPath p (T.old a.val.2) w (r :: ds) := by
  obtain ⟨l,hedge,hguard,hreset⟩ := T.typed_edge_clock_reset h τ hj
  obtain ⟨p,hl,hq,hvalid,hm,ht⟩ := tail l
  refine ⟨.step incoming a.val.1.val p,rfl,rfl,⟨a.val.1.property,hvalid,?_⟩,
    congrArg (List.cons _) hm,?_⟩
  · simpa only [hl,hq,hs] using hedge
  · apply TimedPath.step _ _ he
    · simpa only [hl] using hguard
    · rw [hl]
      exact ht.entry_clock_congr T hreset

def visitDuration (v : TimedVisit T h τ) : NNReal := (v.right - v.left).toNNReal

private def Tail (s : (𝓗).State) (w : T.HAVar → ℝ) (ds : List NNReal)
    (qs : List State) : Prop := ∀ l : EdgeLabel Clock, ∃ p : Path Clock State,
  p.firstIncoming = l ∧ p.firstState = s.val.1.val ∧ p.valid T ∧ visitModes p = qs ∧
    T.TimedPath p (T.old s.val.2) w ds

private theorem flowDuration {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (i : Fin e.count) : T.visitDuration h τ
      ⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩ = e.duration i := by
  change (e.boundary i.succ - e.boundary i.castSucc).toNNReal = _
  have hd : e.boundary i.succ - e.boundary i.castSucc = e.duration i := (e.duration_eq i).symm
  rw [hd]
  simp

/-- Fold all visits preceding a flow, retaining their modes and durations. -/
private theorem prefixTiming {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {w ds qs}
    (tail : T.Tail h τ (e.start i) w ds qs) :
    T.Tail h τ e.initialState w (xs.map (T.visitDuration h τ) ++ ds)
      (xs.map (fun v => v.state.val.1.val) ++ qs) := by
  induction hp generalizing ds qs with
  | initial same => simpa [same] using tail
  | initialJump step =>
    simpa [visitDuration,Tail] using T.prepend_typed_visit h τ
      (ClockElapse.zero T _) rfl step tail
  | @direct i j xs hn pre step ih =>
    have hh := ih (T.prepend_typed_visit h τ (T.typed_flow_clock_elapse h τ e i)
      (e.continuousStep i).1 step tail)
    simpa [List.map_append,flowDuration] using hh
  | @viaPoint i j xs hn pre s enter leave ih =>
    have mid := T.prepend_typed_visit h τ (ClockElapse.zero T _) rfl leave tail
    have hh := ih (T.prepend_typed_visit h τ (T.typed_flow_clock_elapse h τ e i)
      (e.continuousStep i).1 enter mid)
    have hd : e.boundary i.succ - e.boundary i.castSucc = e.duration i := (e.duration_eq i).symm
    simpa [List.map_append,visitDuration, hd] using hh

private theorem visitModes_last (p : Path Clock State) :
    (visitModes p).getLast? = some p.lastState := by
  induction p with
  | last => rfl
  | step _ _ p ih => simp [visitModes,List.getLast?_cons,ih,Path.lastState]

/-- The run, its entering guard witness, modes and durations all come from
the specified execution prefix and cut. No whole-valuation jump equality. -/
theorem ordinary_cut_timed_run {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hgoal : (e.start i).val.1 ∈ T.goalModes) :
    let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]
    ∃ p : Path Clock State, p.run T ∧ p.accepting T ∧
      visitModes p = vs.map (fun v => v.state.val.1.val) ∧
      ∃ u w, T.guardsHold p.firstIncoming u ∧
        T.old e.initialState.val.2 = T.initialReset p.firstIncoming.resets u ∧
        T.TimedPath p (T.old e.initialState.val.2) w (vs.map (T.visitDuration h τ)) := by
  let v : TimedVisit T h τ := ⟨e.start i,e.boundary i.castSucc,cut⟩
  let d := T.visitDuration h τ v
  have hd : (d : ℝ) = cut - e.boundary i.castSucc := Real.coe_toNNReal _ (sub_nonneg.mpr hl.le)
  let z : Set.Icc (0 : ℝ) (e.duration i) := ⟨d, (d.coe_nonneg), by
    have he : (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc := e.duration_eq i
    linarith⟩
  let w := T.old (e.curve i z)
  have hf := ((e.continuousStep i).2.2.2 z).1
  have he : T.ClockElapse (T.old (e.start i).val.2) w d := ⟨hf.1,hf.2.1⟩
  have tail : T.Tail h τ (e.start i) w [d] [(e.start i).val.1.val] := fun l =>
    ⟨.last l _,rfl,rfl,(e.start i).val.1.property,rfl,.last _ _ he⟩
  obtain ⟨l,hi,u,hg,hv,_,_⟩ := e.initial_mem
  obtain ⟨p,hin,hfirst,hvalid,hm,ht⟩ := T.prefixTiming h τ e hp tail l
  have hlast : p.lastState = (e.start i).val.1.val := by
    have hh := visitModes_last p
    rw [hm] at hh
    simpa using hh.symm
  refine ⟨p,⟨hvalid,by simpa only [hin,hfirst] using hi⟩,
    ⟨hvalid,hlast ▸ hgoal⟩,?_,u,w,hin ▸ hg,hin ▸ hv,?_⟩
  · simpa using hm
  · simpa using ht

/-- Append the terminal incoming edge after the last positive flow. Its
frame is retained with duration zero; it is not an additional signal piece. -/
theorem terminal_cut_timed_run {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    {i xs} (hp : BeforeFlow T h τ e i xs)
    (jump : (𝓗).DiscreteStep (e.finish i) e.finalState)
    (hterminal : e.finalState.val.1 ∈ T.terminalModes)
    (goal : e.finalState.val.1 ∈ T.goalModes)
    (hh : σ.horizon = τ) :
    let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
    ∃ p : Path Clock State, p.run T ∧ p.accepting T ∧
      visitModes p = vs.map (fun v => v.state.val.1.val) ++ [e.finalState.val.1.val] ∧
      ∃ u, T.guardsHold p.firstIncoming u ∧
        T.old e.initialState.val.2 = T.initialReset p.firstIncoming.resets u ∧
        T.TimedPath p (T.old e.initialState.val.2) (T.old e.finalState.val.2)
          (vs.map (T.visitDuration h τ) ++ [0]) := by
  have cut := T.typed_terminal_cut h τ e hh jump hterminal
  have hb : e.boundary i.succ = τ := by
    have hf := T.typed_flow_global h τ e i
    have he := T.typed_entry_time h τ e i
    have hj := T.typed_jump_global h τ jump
    have ht := T.typed_final_time h τ e
    have hd : (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc :=
      e.duration_eq i
    linarith
  let w := T.old e.finalState.val.2
  have tail : T.Tail h τ e.finalState w [0] [e.finalState.val.1.val] := fun l =>
    ⟨.last l _,rfl,rfl,e.finalState.val.1.property,rfl,.last _ _ (ClockElapse.zero T _)⟩
  have lastFlow := T.prepend_typed_visit h τ (T.typed_flow_clock_elapse h τ e i)
    (e.continuousStep i).1 jump tail
  obtain ⟨l,hi,u,hg,hv,_,_⟩ := e.initial_mem
  obtain ⟨p,hin,hfirst,hvalid,hm,ht⟩ := T.prefixTiming h τ e hp lastFlow l
  have hlast : p.lastState = e.finalState.val.1.val := by
    have he := visitModes_last p
    rw [hm] at he
    simpa using he.symm
  refine ⟨p,⟨hvalid,by simpa only [hin,hfirst] using hi⟩,
    ⟨hvalid,hlast ▸ goal⟩,?_,u,hin ▸ hg,hin ▸ hv,?_⟩
  · simpa using hm
  · simpa [← hb,T.flowDuration] using ht

end STLTableau.Section4.Tableau
