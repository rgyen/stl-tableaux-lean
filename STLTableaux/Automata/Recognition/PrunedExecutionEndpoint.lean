import STLTableaux.Automata.Translation.NormalizedInputReachability
import STLTableaux.Automata.Recognition.DirectFlowRecognition
import STLTableaux.Automata.Recognition.PrunedDwellGeometry
import STLTableaux.Automata.Recognition.ExecutionObservedPiece
import STLTableaux.Automata.Translation.TableauExecutionWitness
import STLTableaux.Automata.Recognition.ExecutionPathTiming

/-! Actual execution endpoints of the pruned normalized input translation. A final
flow endpoint and a terminal tableau position are kept distinct. No value of
the half-open signal at its horizon is evaluated. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h
      σ.horizon σ.horizon_pos).Execution σ)

/-- Goal reachability gives an accepting run of the ORIGINAL tableau purely
by the translated edges, before constructing a partition or proving satisfaction. -/
theorem pruned_execution_original_accepting_run_with_witness
    (hg : e.finalState.val.1 ∈ (inputTableau X root).pruneTerminal.goalModes) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (inputTableau X root) ∧ p.accepting (inputTableau X root) ∧
      (inputTableau X root).pruneTerminal.ExecutionPathWitness
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e.initialState e.finalState p := by
  obtain ⟨p, hr, ha, hw, _⟩ :=
    (inputTableau X root).pruneTerminal.execution_accepting_path_witness
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e hg
  exact ⟨p, p.run_of_pruned _ hr, p.accepting_of_pruned _ ha, hw⟩

/-- Forget only the execution annotation, retaining the same final state. -/
theorem pruned_execution_original_accepting_run
    (hg : e.finalState.val.1 ∈ (inputTableau X root).pruneTerminal.goalModes) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var),
      p.run (inputTableau X root) ∧ p.accepting (inputTableau X root) ∧
      p.lastState = e.finalState.val.1.val := by
  obtain ⟨p, hr, ha, hw⟩ :=
    pruned_execution_original_accepting_run_with_witness X root h e hg
  exact ⟨p, hr, ha, (hw.valid _ _ _ _).2.2⟩

/-- Residence times and guarded clock traversal accompany the very same
accepting path of the original tableau, obtained from the supplied execution. -/
theorem pruned_execution_original_accepting_timed_path
    (hg : e.finalState.val.1 ∈ (inputTableau X root).pruneTerminal.goalModes) :
    ∃ p : Path Clock (Section3.TransitionForm Clock Var), ∃ ds : List NNReal,
      p.run (inputTableau X root) ∧ p.accepting (inputTableau X root) ∧
      (inputTableau X root).pruneTerminal.ExecutionPathWitness
        ((inputTableau X root).pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e.initialState e.finalState p ∧
      (inputTableau X root).pruneTerminal.TimedPath p
        e.initialState.val.2 e.finalState.val.2 ds ∧
      (ds.sum : ℝ) = e.boundary ⟨e.count, by omega⟩ ∧
      (ds.sum : ℝ) ≤ σ.horizon ∧
      ∃ v : (inputTableau (Clock := Clock) X root).HAVar → ℝ,
        (inputTableau X root).pruneTerminal.guardsHold p.firstIncoming v ∧
        e.initialState.val.2 =
          (inputTableau X root).pruneTerminal.initialReset p.firstIncoming.resets v := by
  obtain ⟨p, ds, hr, ha, hw, ht, hsum, hle, hv⟩ :=
    (inputTableau X root).pruneTerminal.execution_accepting_timed_path
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e hg
  exact ⟨p, ds, p.run_of_pruned _ hr, p.accepting_of_pruned _ ha, hw, ht, hsum, hle, hv⟩

theorem pruned_execution_initial_nonterminal :
    Local.terminal ∉ (inputTableau X root).label e.initialState.val.1.val := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  exact finiteRootTableau_initial_nonterminal X root.val _ hl.1

theorem pruned_execution_flow_nonterminal (i : Fin e.count) :
    Local.terminal ∉ (inputTableau X root).label (e.start i).val.1.val :=
  (inputTableau X root).pruneTerminal.execution_flow_nonterminal
    ((inputTableau X root).pruneTerminal_translationReady h)
    σ.horizon σ.horizon_pos e rfl (pruned_execution_initial_nonterminal X root h e) i

/-- At the horizon the last flow either is already final, or makes one actual
jump into the terminal position. The goal premise is not needed for this split. -/
theorem pruned_execution_horizon_tail
    (hend : e.boundary ⟨e.count, by omega⟩ = σ.horizon) :
    (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩ = e.finalState ∧
      Local.terminal ∉ (inputTableau X root).label e.finalState.val.1.val) ∨
    (((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState ∧
      Local.terminal ∈ (inputTableau X root).label e.finalState.val.1.val) := by
  let T := inputTableau (Clock := Clock) X root
  let hp := T.pruneTerminal_translationReady h
  let last : Fin e.count := ⟨e.count - 1, by have := e.nonempty; omega⟩
  have hc : (e.finish last).val.2 T.globalClock = σ.horizon := by
    have hc := T.pruneTerminal.execution_finish_clock hp σ.horizon σ.horizon_pos e last
    change (e.finish last).val.2 T.globalClock = e.boundary ⟨last.val + 1, by omega⟩ at hc
    have hind : last.val + 1 = e.count := by dsimp [last]; have := e.nonempty; omega
    simpa only [hind, hend] using hc
  have hn : Local.terminal ∉ T.label (e.finish last).val.1.val := by
    have hn := pruned_execution_flow_nonterminal X root h e last
    rwa [(e.continuousStep last).1] at hn
  rcases T.pruned_discreteSteps_at_horizon h σ.horizon σ.horizon_pos e.finalSteps hc
    with heq | hj
  · exact Or.inl ⟨heq, heq ▸ hn⟩
  · refine Or.inr ⟨hj, ?_⟩
    by_contra hnot
    have hlt := T.pruneTerminal.nonterminal_entry_lt_horizon hp
      σ.horizon σ.horizon_pos hj hnot
    have hclock := T.pruneTerminal.execution_final_clock hp σ.horizon σ.horizon_pos e
    rw [hclock, hend] at hlt
    exact lt_irrefl _ hlt

theorem pruned_execution_early_final_nonterminal
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    Local.terminal ∉ (inputTableau X root).label e.finalState.val.1.val := by
  intro ht
  have heq := (inputTableau X root).pruneTerminal.execution_terminal_acceptance_exhausts
    ((inputTableau X root).pruneTerminal_translationReady h)
    σ.horizon σ.horizon_pos e rfl (pruned_execution_initial_nonterminal X root h e) ht
  exact (ne_of_lt hearly) heq

/-- Every actual observed piece lies at an ordinary tableau position. Even a
zero-time observed state is handled through its actual path to the flow/final
observation; no label-satisfaction assumption or shortcut edge is used. -/
theorem pruned_execution_observed_nonterminal
    {s : Section3.TransitionForm Clock Var} {l r : ℝ}
    (ho : (inputTableau X root).pruneTerminal.ExecutionObservedPiece
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e s l r) :
    Local.terminal ∉ (inputTableau X root).label s := by
  cases ho with
  | flow i => exact pruned_execution_flow_nonterminal X root h e i
  | beforeFlow i s hj =>
      intro ht
      have heq := (inputTableau X root).pruned_discreteSteps_from_terminal_eq
        h σ.horizon σ.horizon_pos hj ht
      exact pruned_execution_flow_nonterminal X root h e i (heq ▸ ht)
  | atFinal s hj he =>
      intro ht
      have heq := (inputTableau X root).pruned_discreteSteps_from_terminal_eq
        h σ.horizon σ.horizon_pos hj ht
      exact pruned_execution_early_final_nonterminal X root h e he (heq ▸ ht)

/-- A terminal final state satisfies its local labels at the partition's end
position, for any signal partition and clock valuation, without reading σ(τ). -/
theorem pruned_execution_terminal_labels
    (ht : Local.terminal ∈ (inputTableau X root).label e.finalState.val.1.val)
    (ρ : FiniteSignal Var) (P : IntervalPartition ρ.domain) (α : ClockValuation Clock) :
    ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
      l.holds ρ P α ⟨P.size, by omega⟩ := by
  intro l hl
  exact (local_holds_terminal_iff ρ P α l).mpr (e.finalState.val.1.property.2 ht l hl)

end STLTableau.Section4.Finiteness
