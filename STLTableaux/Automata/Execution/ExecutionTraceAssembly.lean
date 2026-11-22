import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint
import STLTableaux.Automata.Recognition.ExecutionTraceGuards
import STLTableaux.Automata.Recognition.ExecutionObservedExtraction
import STLTableaux.Automata.Execution.ExecutionObservedLabels

/-! Assemble the clock calculation and local labels on the same path.
No alternate accepting path or external clock schedule is chosen. The execution
supplies observations and guard/reset evidence; partition alignment remains
explicit rather than being assumed to follow from structural path validity. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_trace_holds_of_timedPath
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau (Clock := Clock) X root))
    {v w : (inputTableau (Clock := Clock) X root).HAVar → ℝ}
    {ds : List NNReal}
    (ht : (inputTableau X root).pruneTerminal.TimedPath p v w ds)
    (u : (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : (inputTableau X root).pruneTerminal.guardsHold p.firstIncoming u)
    (hv : v = (inputTableau X root).pruneTerminal.initialReset p.firstIncoming.resets u)
    (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain)
    (hlen : ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩)
    (hl : ∀ (i : Fin (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length)
      (β : ClockValuation Clock), ∀ l ∈
        ((p.trace JudgementTableau.labels JudgementTableau.labels_finite).frameAt i).locals,
      l.holds ρ P β ⟨i.val, by
        have hc := ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite
        have := i.isLt
        omega⟩) :
    ∀ α, (p.trace JudgementTableau.labels JudgementTableau.labels_finite).holds
      ρ P α ⟨0, by omega⟩ := by
  exact ht.forall_trace_holds_of_initialReset _
    JudgementTableau.labels JudgementTableau.labels_finite ρ P hlen hd u hg hv
    (finiteRootTableau_trace_closed X root.val p hr) hl

/-- Goal membership supplies acceptance; the witness remains precisely `p`.
Neither a nonnegative real valuation nor an independent schedule is required. -/
theorem inputTableau_recognizes_of_timedPath
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau (Clock := Clock) X root))
    (ha : p.accepting (inputTableau (Clock := Clock) X root))
    {v w : (inputTableau (Clock := Clock) X root).HAVar → ℝ}
    {ds : List NNReal}
    (ht : (inputTableau X root).pruneTerminal.TimedPath p v w ds)
    (u : (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : (inputTableau X root).pruneTerminal.guardsHold p.firstIncoming u)
    (hv : v = (inputTableau X root).pruneTerminal.initialReset p.firstIncoming.resets u)
    (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain)
    (hlen : ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩)
    (hl : ∀ (i : Fin (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length)
      (β : ClockValuation Clock), ∀ l ∈
        ((p.trace JudgementTableau.labels JudgementTableau.labels_finite).frameAt i).locals,
      l.holds ρ P β ⟨i.val, by
        have hc := ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite
        have := i.isLt
        omega⟩) :
    (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P :=
  ⟨p, hr, ha, inputTableau_trace_holds_of_timedPath X root p hr ht u hg hv ρ P hlen hd hl⟩

/-- Extract once from a goal-reaching execution, then derive all local labels
and clock checks on any aligned partition of its projected signal. The caller
supplies no valuation schedule, atomic satisfaction or endpoint-label premise.
This is still conditional on constructing a duration/marker-aligned partition. -/
theorem pruned_execution_accepting_path_with_trace_reduction
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    (hgoal : e.finalState.val.1 ∈ (inputTableau X root).pruneTerminal.goalModes) :
    ∃ (p : Path Clock (Section3.TransitionForm Clock Var)) (ds : List NNReal),
      p.run (inputTableau X root) ∧ p.accepting (inputTableau X root) ∧
      (inputTableau X root).pruneTerminal.ExecutionPathWitness
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e.initialState e.finalState p ∧
      (inputTableau X root).pruneTerminal.TimedPath p
        e.initialState.val.2 e.finalState.val.2 ds ∧
      (inputTableau X root).pruneTerminal.ObservedPath
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e p 0 (e.boundary ⟨e.count, by omega⟩) ds ∧
      (ds.sum : ℝ) = e.boundary ⟨e.count, by omega⟩ ∧
      ∃ hc : ds.length = (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length,
      ∀ (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain)
        (_hproj : (inputTableau X root).pruneTerminal.ProjectsTo σ ρ)
        (hlen : ds.length ≤ P.size + 1),
        (∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
          (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩) →
        let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
        ((ds.sum : ℝ) < ρ.horizon →
          ∀ (i : Fin t.length) (hi : i.val < P.size), i.val + 1 = t.length →
          (P.interval ⟨i.val, hi⟩).right ≤ (ds.sum : ℝ)) →
        (∀ (i : Fin t.length) (hi : i.val < P.size) m,
          Section3.Local.marker m ∈ (t.frameAt i).locals →
            (P.interval ⟨i.val, hi⟩).leftBoundary = m) →
        (∀ α, t.holds ρ P α ⟨0, by omega⟩) ∧
          (inputTableau (Clock := Clock) X root).recognizes
            JudgementTableau.labels_finite ρ P := by
  obtain ⟨p, ds, hr, ha, hw, ht, hp, u, hg, hv⟩ :=
    (inputTableau X root).pruned_execution_accepting_observed_path h e hgoal
  have hsum := ht.total_duration (inputTableau X root).pruneTerminal
  rw [(inputTableau X root).pruneTerminal.initial_globalClock_zero
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e.initial_mem,
    (inputTableau X root).pruneTerminal.execution_final_clock
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e, zero_add] at hsum
  refine ⟨p, ds, hr, ha, hw, ht, hp, hsum.symm,
    ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite, ?_⟩
  intro ρ P hproj hlen hd t hlast hm
  have hc := ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite
  have hvalid := (hw.valid _ _ _ _).1
  have hs : ∀ α, t.holds ρ P α ⟨0, by omega⟩ := by
    apply inputTableau_trace_holds_of_timedPath X root p hr ht u hg hv ρ P hlen hd
    exact inputTableau_observed_trace_labels X root h e hr hvalid hp hproj P
      (by omega) hd hlast hm
  exact ⟨hs, p, hr, ha, hs⟩

/-- The clock calculation and observed labels combine on the same partition.
Numerical atom satisfaction and endpoint labels are conclusions, not premises.
This theorem still requires the geometric and marker alignment of that partition;
it does not claim that every extracted path admits such an alignment. -/
theorem inputTableau_trace_holds_on_observed_partition
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p r ds} (hr : p.run (inputTableau X root))
    (hvalid : p.valid (inputTableau X root).pruneTerminal)
    (ht : (inputTableau X root).pruneTerminal.TimedPath p
      e.initialState.val.2 e.finalState.val.2 ds)
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p 0 r ds)
    (u : (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : (inputTableau X root).pruneTerminal.guardsHold p.firstIncoming u)
    (hv : e.initialState.val.2 =
      (inputTableau X root).pruneTerminal.initialReset p.firstIncoming.resets u)
    {ρ : FiniteSignal Var}
    (hproj : (inputTableau X root).pruneTerminal.ProjectsTo σ ρ)
    (P : IntervalPartition ρ.domain) (hlen : ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩) :
    let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
    ((ds.sum : ℝ) < ρ.horizon →
      ∀ (i : Fin t.length) (hi : i.val < P.size), i.val + 1 = t.length →
      (P.interval ⟨i.val, hi⟩).right ≤ (ds.sum : ℝ)) →
    (∀ (i : Fin t.length) (hi : i.val < P.size) m,
      Section3.Local.marker m ∈ (t.frameAt i).locals →
        (P.interval ⟨i.val, hi⟩).leftBoundary = m) →
    ∀ α, t.holds ρ P α ⟨0, by omega⟩ := by
  intro t hlast hm
  have hc := ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite
  apply inputTableau_trace_holds_of_timedPath X root p hr ht u hg hv ρ P hlen hd
  exact inputTableau_observed_trace_labels X root h e hr hvalid hp hproj P
    (by omega) hd hlast hm

/-- Construct the ordinary partition for a terminal execution when the labels
agree with markers computed from residence times. The singleton geometry of the
ordinary prefix remains an explicit hypothesis; no terminal path frame or
actual edge is deleted. This is the canonical half-open/singleton assignment,
not an unconditional reduction for all executions. In particular, the geometric
`singletonMarkers_residence_open_iff` does not establish `hmarkers`: its left
side is a constructed marker, not the marker required by an execution label. -/
theorem inputTableau_terminal_trace_reduction
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p r ds} (hr : p.run (inputTableau X root))
    (ha : p.accepting (inputTableau X root))
    (hvalid : p.valid (inputTableau X root).pruneTerminal)
    (ht : (inputTableau X root).pruneTerminal.TimedPath p
      e.initialState.val.2 e.finalState.val.2 ds)
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p 0 r ds)
    (hterminal : Section3.Local.terminal ∈ (inputTableau X root).label p.lastState)
    (u : (inputTableau (Clock := Clock) X root).HAVar → ℝ)
    (hg : (inputTableau X root).pruneTerminal.guardsHold p.firstIncoming u)
    (hv : e.initialState.val.2 =
      (inputTableau X root).pruneTerminal.initialReset p.firstIncoming.resets u)
    {ρ : FiniteSignal Var}
    (hproj : (inputTableau X root).pruneTerminal.ProjectsTo σ ρ)
    (hisolated : ∀ (i : Fin ds.dropLast.length) (hi : i.val + 1 < ds.dropLast.length),
      ds.dropLast[i.val] = 0 → ds.dropLast[i.val + 1] ≠ 0)
    (hmarkers : ∀
      (i : Fin (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length)
      (hi : i.val < ds.dropLast.length) m,
      Section3.Local.marker m ∈
        ((p.trace JudgementTableau.labels JudgementTableau.labels_finite).frameAt i).locals →
      IntervalPartition.singletonMarkers
        (fun j : Fin (ds.dropLast.length + 1) => Tableau.residenceBoundary ds.dropLast j.val)
        ⟨i.val, by omega⟩ = m) :
    ∃ P : IntervalPartition ρ.domain, P.size = ds.dropLast.length ∧
      let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
      (∀ α, t.holds ρ P α ⟨0, by omega⟩) ∧
        (inputTableau (Clock := Clock) X root).recognizes
          JudgementTableau.labels_finite ρ P := by
  obtain ⟨P, hsize, hlength, hd, hboundary⟩ :=
    inputTableau_observed_terminal_partition X root h e hp hterminal hisolated
  have hcover : (⋃ i, (P.interval i).carrier) = ρ.domain := by
    simpa only [FiniteSignal.domain, hproj.1] using P.covers
  let Q : IntervalPartition ρ.domain := { P with covers := hcover }
  have hc := ht.frame_count _ JudgementTableau.labels JudgementTableau.labels_finite
  have hlen : ds.length ≤ Q.size + 1 := by change ds.length ≤ P.size + 1; omega
  have hd' : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration Q ⟨i.val, by omega⟩ := by
    intro i hi
    have hip : i.val < ds.dropLast.length := by simp only [List.length_dropLast]; omega
    change (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩
    simpa only [List.getElem_dropLast] using (hd ⟨i.val, hip⟩).symm
  refine ⟨Q, hsize, ?_⟩
  dsimp only
  let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
  have hs : ∀ α, t.holds ρ Q α ⟨0, by omega⟩ := by
    apply inputTableau_trace_holds_on_observed_partition
      X root h e hr hvalid ht hp u hg hv hproj Q hlen hd'
    · intro _ i hi he
      have he' : i.val + 1 = Q.size + 1 := he.trans hlength
      omega
    · intro i hi m hm
      have hip : i.val < ds.dropLast.length := by change i.val < P.size at hi; omega
      exact (hboundary ⟨i.val, hip⟩).trans (hmarkers i hip m hm)
  exact ⟨hs, p, hr, ha, hs⟩

end STLTableau.Section4.Finiteness
