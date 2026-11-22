import STLTableaux.Automata.Recognition.PrelimTracePrefix
import STLTableaux.Automata.Translation.EndPositionReverse
import STLTableaux.Automata.Translation.EmptyContinuationSupport

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "H" => T.prelimAutomaton h τ

/-- An ordinary cut retains the visits recorded by `BeforeFlow`. A horizon
certificate supplies one additional tableau frame at the terminal position. -/
inductive PrelimGoalInduced {σ : FiniteSignal T.TypedVar} (e : (H).PrelimExecution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain) : Prop
  | ordinary {i xs cut}
      (hp : BeforeFlow T h τ (T.prelimTypedPrefix h τ e hh) i xs)
      (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
      (goal : (e.start i).val.1 ∈ T.goalModes)
      (layout : T.CutLayout h τ ρ (xs ++ [⟨e.start i, e.boundary i.castSucc, cut⟩]) cut P)
  | horizon {xs}
      (hp : BeforeFlow T h τ (T.prelimTypedPrefix h τ e hh) e.lastIndex xs)
      (atEnd : e.boundary ⟨e.count, by omega⟩ = τ)
      (certificate : ∃ (l : EdgeLabel Clock) (q : T.states),
        (e.finalState.val.1.val, l, q.val) ∈ T.edges ∧
        T.guardsHold l (T.old e.finalState.val.2) ∧ T.EndGoal q)
      (layout : T.CutLayout h τ ρ
        (xs ++ [⟨e.start e.lastIndex, e.boundary e.lastIndex.castSucc, τ⟩]) τ P)

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root

/-- Every partition induced by an execution with a state goal is recognized
by a run that follows its visited modes and edges. The run satisfies the
trace for every initial clock valuation. -/
theorem empty_prelim_stateGoal_reverse {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).prelimAutomaton h τ).PrelimExecution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (P : IntervalPartition ρ.domain)
    (induced : (U).PrelimGoalInduced h τ e hh ρ P) :
    (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).prelimTypedPrefix h τ e hh
  obtain ⟨l, hi, _, _, _, _, _⟩ := e.initial_mem
  have first := finiteRootTableau_initial_nonterminal X root.val _ hi
  cases induced with
  | @ordinary i xs cut hp hl hr goal layout =>
    have hc := hr.trans (e.increasing.monotone (Fin.le_last i.succ))
    exact (U).recognizes_on_induced_ordinary_cut_through h τ pre ρ
      ((U).prefixSignal_projectsThrough h τ e ρ proj hc) hp hl hr goal
      JudgementTableau.labels_finite (emptyContinuation_closed X root)
      (emptyContinuation_visits_ready X root h pre hp cut) hh first P layout
  | @horizon xs hp atEnd cert layout =>
    have ht : e.finalState.val.2 (.inl (U).globalClock) = τ :=
      ((U).prelim_final_time h τ e).trans atEnd
    have hd : 0 < e.finalState.val.2 (U).dwell := by
      have he := (U).typed_finish_dwell h τ pre e.lastIndex
      exact he ▸ e.duration_pos e.lastIndex
    obtain ⟨b, endGoal, edge⟩ := (U).end_edge_of_prelimGoal h τ e.finalState cert ht hd
    have hend : e.boundary e.lastIndex.succ = τ := by
      have he : e.lastIndex.succ = (⟨e.count, by omega⟩ : Fin (e.count + 1)) := by
        apply Fin.ext
        change e.count - 1 + 1 = e.count
        have := e.nonempty
        omega
      exact (congrArg e.boundary he).trans atEnd
    have fullProj := (U).prefixSignal_projects_at_horizon h τ e ρ proj (atEnd.trans hh.symm)
    obtain ⟨Q, p, hQ, run, acc, _, trace⟩ := (U).run_on_endGoal_cut h τ pre ρ fullProj hp b
      edge endGoal hend hh first JudgementTableau.labels_finite (emptyContinuation_closed X root)
      (emptyContinuation_visits_ready X root h pre hp τ)
    have same := hQ.unique (U) h τ layout (hh.symm.trans proj.1).le
    exact same ▸ (show (U).recognizes JudgementTableau.labels_finite ρ Q from
      ⟨p, run, acc, trace⟩)

/-- An ordinary cut induces a partition of the signal domain. -/
theorem empty_prelim_partition_of_ordinaryCut {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).prelimAutomaton h τ).PrelimExecution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (i : Fin e.count) {cut : ℝ} (hl : e.boundary i.castSucc < cut)
    (hr : cut ≤ e.boundary i.succ) (goal : (e.start i).val.1 ∈ (U).goalModes) :
    ∃ P : IntervalPartition ρ.domain,
      (U).PrelimGoalInduced h τ e hh ρ P ∧
      (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).prelimTypedPrefix h τ e hh
  obtain ⟨xs, hp⟩ := (U).exists_beforeFlow h τ pre i
  obtain ⟨l, hi, _, _, _, _, _⟩ := e.initial_mem
  have first := finiteRootTableau_initial_nonterminal X root.val _ hi
  obtain ⟨past, now⟩ := (U).ordinary_visits_of_initial h τ pre hh first hp
  have ord : ∀ v ∈ xs ++ [⟨e.start i, e.boundary i.castSucc, cut⟩],
      v.state.val.1 ∉ (U).terminalModes := by
    intro v hv
    rcases List.mem_append.mp hv with old | last
    · exact past v old
    · obtain rfl := List.mem_singleton.mp last
      exact now
  obtain ⟨P, layout, rec⟩ := (U).ordinary_cut_layout_trace_through h τ pre ρ
    ((U).prefixSignal_projectsThrough h τ e ρ proj
      (hr.trans (e.increasing.monotone (Fin.le_last i.succ)))) hp hl hr goal
    JudgementTableau.labels_finite (emptyContinuation_closed X root)
    (emptyContinuation_visits_ready X root h pre hp cut) ord
  exact ⟨P, .ordinary hp hl hr goal layout, rec⟩

/-- A horizon certificate at the last flow endpoint induces a partition.
Its target supplies the terminal tableau frame. -/
theorem empty_prelim_partition_of_horizonGoal {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).prelimAutomaton h τ).PrelimExecution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (atEnd : e.boundary ⟨e.count, by omega⟩ = τ)
    (cert : ∃ (l : EdgeLabel Clock) (q : (U).states),
      (e.finalState.val.1.val, l, q.val) ∈ (U).edges ∧
      (U).guardsHold l ((U).old e.finalState.val.2) ∧ (U).EndGoal q) :
    ∃ P : IntervalPartition ρ.domain,
      (U).PrelimGoalInduced h τ e hh ρ P ∧
      (U).recognizes JudgementTableau.labels_finite ρ P := by
  let pre := (U).prelimTypedPrefix h τ e hh
  obtain ⟨xs, hp⟩ := (U).exists_beforeFlow h τ pre e.lastIndex
  obtain ⟨l, hi, _, _, _, _, _⟩ := e.initial_mem
  have first := finiteRootTableau_initial_nonterminal X root.val _ hi
  have ht := ((U).prelim_final_time h τ e).trans atEnd
  have hd : 0 < e.finalState.val.2 (U).dwell := by
    exact ((U).typed_finish_dwell h τ pre e.lastIndex) ▸ e.duration_pos e.lastIndex
  obtain ⟨b, endGoal, edge⟩ := (U).end_edge_of_prelimGoal h τ e.finalState cert ht hd
  have he : e.lastIndex.succ = (⟨e.count, by omega⟩ : Fin (e.count + 1)) := by
    apply Fin.ext
    change e.count - 1 + 1 = e.count
    have := e.nonempty
    omega
  have hend := (congrArg e.boundary he).trans atEnd
  have fullProj := (U).prefixSignal_projects_at_horizon h τ e ρ proj (atEnd.trans hh.symm)
  obtain ⟨P, p, layout, run, acc, _, trace⟩ := (U).run_on_endGoal_cut h τ pre ρ fullProj hp b
    edge endGoal hend hh first JudgementTableau.labels_finite (emptyContinuation_closed X root)
    (emptyContinuation_visits_ready X root h pre hp τ)
  exact ⟨P, .horizon hp atEnd cert layout, p, run, acc, trace⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``empty_prelim_stateGoal_reverse,
      ``empty_prelim_partition_of_ordinaryCut, ``empty_prelim_partition_of_horizonGoal] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
