import STLTableaux.Automata.Recognition.TypedOrdinaryTrace
import STLTableaux.Finiteness.Correctness.RootTraceClockIndependence
import STLTableaux.Automata.Execution.TerminalPruning

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)

theorem beforeFlow_preserves {σ : FiniteSignal T.TypedVar}
    (e : (T.typedAutomaton h τ).Execution σ) {S : State → Prop}
    (hi : S e.initialState.val.1.val)
    (hedge : ∀ a l b, (a,l,b) ∈ T.edges → S a → S b)
    {i xs} (hp : BeforeFlow T h τ e i xs) :
    (∀ v ∈ xs, S v.state.val.1.val) ∧ S (e.start i).val.1.val := by
  have step {a b : (T.typedAutomaton h τ).State}
      (hj : (T.typedAutomaton h τ).DiscreteStep a b) :
      S a.val.1.val → S b.val.1.val := by
    obtain ⟨l,he,_,_⟩ := T.typed_edge_clock_reset h τ hj
    exact hedge _ l _ he
  induction hp with
  | initial he => exact ⟨by simp,he ▸ hi⟩
  | initialJump hj => exact ⟨by simpa using hi,step hj hi⟩
  | @direct i j xs hn pre hj ih =>
    refine ⟨?_,step hj ((e.continuousStep i).1 ▸ ih.2)⟩
    intro v hv
    rcases List.mem_append.mp hv with ho | hv
    · exact ih.1 v ho
    · obtain rfl := List.mem_singleton.mp hv
      exact ih.2
  | @viaPoint i j xs hn pre s enter leave ih =>
    have hs := step enter ((e.continuousStep i).1 ▸ ih.2)
    refine ⟨?_,step leave hs⟩
    intro v hv
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with ho | rfl | rfl
    · exact ih.1 v ho
    · exact ih.2
    · exact hs
end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T" => (inputTableau (Clock := Clock) X root)

/-- On the unpruned normalized input graph no extra clock-closure, label-shape,
or initial-mode compatibility assumption is needed for the ordinary cut. -/
theorem normalized_input_typed_ordinary {τ : ℝ} (h : (T).TranslationReady)
    {σ : FiniteSignal (T).TypedVar} (e : ((T).typedAutomaton h τ).Execution σ)
    (ρ : FiniteSignal Var) (proj : (T).TypedProjectsTo σ ρ)
    {i xs} (hp : Tableau.BeforeFlow T h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (goal : (e.start i).val.1 ∈ (T).goalModes) (hh : σ.horizon = τ)
    (P : IntervalPartition ρ.domain)
    (induced : (T).CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P) :
    (T).recognizes JudgementTableau.labels_finite ρ P := by
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have inv := (T).beforeFlow_preserves h τ e
    (inputTableau_initial_normalizedReady X root hi)
    (fun a l b he => inputTableau_edge_normalizedReady X root (e := (a,l,b)) he) hp
  apply (T).recognizes_on_induced_ordinary_cut h τ e ρ proj hp hl hr goal
    JudgementTableau.labels_finite (finiteRootTableau_trace_closed X root.val) _ hh
    (finiteRootTableau_initial_nonterminal X root.val _ hi) P induced
  intro v hv q hq
  have hs : v.state.val.1.val.NormalizedReady := by
    rcases List.mem_append.mp hv with hx | hx
    · exact inv.1 v hx
    · obtain rfl := List.mem_singleton.mp hx
      exact inv.2
  exact hs.1 q hq.1

/-- For the terminal-compatible restriction, discharge the terminal label
and edge facts from its definition. The conclusion concerns the original
tableau (same accepting path); the execution premise is on the restriction. -/
theorem normalized_input_typed_pruned_terminal {τ : ℝ} (h : (T).TranslationReady)
    {σ : FiniteSignal (T).pruneTerminal.TypedVar}
    (e : ((T).pruneTerminal.typedAutomaton ((T).pruneTerminal_translationReady h) τ).Execution σ)
    (ρ : FiniteSignal Var) (proj : (T).pruneTerminal.TypedProjectsTo σ ρ)
    {i xs} (hp : Tableau.BeforeFlow (T).pruneTerminal
      ((T).pruneTerminal_translationReady h) τ e i xs)
    (tail : Relation.TransGen
      ((T).pruneTerminal.typedAutomaton ((T).pruneTerminal_translationReady h) τ).DiscreteStep
      (e.finish i) e.finalState)
    (term : e.finalState.val.1 ∈ (T).pruneTerminal.terminalModes)
    (goal : e.finalState.val.1 ∈ (T).pruneTerminal.goalModes) (hh : σ.horizon = τ)
    (P : IntervalPartition ρ.domain)
    (induced : (T).pruneTerminal.CutLayout ((T).pruneTerminal_translationReady h) τ ρ
      (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P) :
    (T).recognizes JudgementTableau.labels_finite ρ P := by
  let U := (T).pruneTerminal
  let hu := (T).pruneTerminal_translationReady h
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have jump := U.direct_terminal_tail_of_edges hu τ e hh tail term
    (fun _ _ _ he hs => (he.2.2.2 hs).elim)
  have inv := U.beforeFlow_preserves hu τ e
    (inputTableau_initial_normalizedReady X root hi.1)
    (fun a l b he => inputTableau_edge_normalizedReady X root (e := (a,l,b)) he.1) hp
  apply ((T).pruneTerminal_recognizes_iff JudgementTableau.labels_finite ρ P).mp
  apply U.recognizes_on_induced_terminal_cut hu τ e ρ proj hp jump term goal hh
    (finiteRootTableau_initial_nonterminal X root.val _ hi.1) JudgementTableau.labels_finite
    (fun p hr => finiteRootTableau_trace_closed X root.val p (p.run_of_pruned T hr)) _
    (e.finalState.val.1.property.2 term) P induced
  intro v hv q hq
  have hs : v.state.val.1.val.NormalizedReady := by
    rcases List.mem_append.mp hv with hx | hx
    · exact inv.1 v hx
    · obtain rfl := List.mem_singleton.mp hx
      exact inv.2
  exact hs.1 q hq.1

theorem normalized_input_typed_pruned_ordinary {τ : ℝ} (h : (T).TranslationReady)
    {σ : FiniteSignal (T).pruneTerminal.TypedVar}
    (e : ((T).pruneTerminal.typedAutomaton ((T).pruneTerminal_translationReady h) τ).Execution σ)
    (ρ : FiniteSignal Var) (proj : (T).pruneTerminal.TypedProjectsTo σ ρ)
    {i xs} (hp : Tableau.BeforeFlow (T).pruneTerminal
      ((T).pruneTerminal_translationReady h) τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (goal : (e.start i).val.1 ∈ (T).pruneTerminal.goalModes) (hh : σ.horizon = τ)
    (P : IntervalPartition ρ.domain)
    (induced : (T).pruneTerminal.CutLayout ((T).pruneTerminal_translationReady h) τ ρ
      (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P) :
    (T).recognizes JudgementTableau.labels_finite ρ P := by
  let U := (T).pruneTerminal
  let hu := (T).pruneTerminal_translationReady h
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have inv := U.beforeFlow_preserves hu τ e
    (inputTableau_initial_normalizedReady X root hi.1)
    (fun a l b he => inputTableau_edge_normalizedReady X root (e := (a,l,b)) he.1) hp
  apply ((T).pruneTerminal_recognizes_iff JudgementTableau.labels_finite ρ P).mp
  apply U.recognizes_on_induced_ordinary_cut hu τ e ρ proj hp hl hr goal
    JudgementTableau.labels_finite
    (fun p hr => finiteRootTableau_trace_closed X root.val p (p.run_of_pruned T hr)) _
    hh (finiteRootTableau_initial_nonterminal X root.val _ hi.1) P induced
  intro v hv q hq
  have hs : v.state.val.1.val.NormalizedReady := by
    rcases List.mem_append.mp hv with hx | hx
    · exact inv.1 v hx
    · obtain rfl := List.mem_singleton.mp hx
      exact inv.2
  exact hs.1 q hq.1

end STLTableau.Section4.Finiteness
