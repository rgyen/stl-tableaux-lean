import STLTableaux.ModelChecking.Preprocessing.NormalizedInputPreservation
import STLTableaux.Automata.Translation.NormalizedInputTranslation
import STLTableaux.Automata.Recognition.TableauExecutionPath

/-! States reachable from normalized inputs preserve the normalized grammar.
The invariant covers initial states and each successive transition. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_initial_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    {e : EdgeLabel Clock × Section3.TransitionForm Clock Var}
    (he : e ∈ (inputTableau (Clock := Clock) X root).initial) : e.2.NormalizedReady := by
  apply derives_normalizedReady he.1.1
  simpa only [Section3.StateForm.normalizedReady_ofLocal, Local.NormalizedReady,
    Predicate.NormalizedReady, predicateNormalizedReady] using root.property

theorem inputTableau_edge_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    {e : Section3.TransitionForm Clock Var × EdgeLabel Clock × Section3.TransitionForm Clock Var}
    (he : e ∈ (inputTableau (Clock := Clock) X root).edges)
    (hs : e.1.NormalizedReady) : e.2.2.NormalizedReady := by
  obtain ⟨_, _, N, hn, hd, _⟩ := he.1
  exact derives_normalizedReady hd (hs.2 N hn)

theorem inputTableau_valid_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hv : p.valid (inputTableau X root)) (hf : p.firstState.NormalizedReady) :
    Subgraph.AllStates {F | F.NormalizedReady} p := by
  induction p with
  | last => exact hf
  | step l s p ih =>
    exact ⟨hf, ih hv.2.1 (inputTableau_edge_normalizedReady X root hv.2.2 hf)⟩

/-- No satisfaction assumption is needed: grammar follows from graph admission
and the checked initial input, for every run, accepting or otherwise. -/
theorem inputTableau_run_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau X root)) :
    Subgraph.AllStates {F | F.NormalizedReady} p :=
  inputTableau_valid_normalizedReady X root p hr.1
    (inputTableau_initial_normalizedReady X root hr.2)

theorem inputTableau_modeSteps_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    {q q' : (inputTableau (Clock := Clock) X root).states}
    (hr : Relation.ReflTransGen (inputTableau X root).ModeStep q q')
    (hq : q.val.NormalizedReady) : q'.val.NormalizedReady := by
  induction hr with
  | refl => exact hq
  | tail _ he ih =>
    obtain ⟨l, hl⟩ := he
    exact inputTableau_edge_normalizedReady X root hl ih

omit [DecidableEq Clock] [Infinite Clock] in
theorem normalizedReady_current_not_false {F : Section3.TransitionForm Clock Var}
    (hf : F.NormalizedReady) : Local.predicate (.plain Formula.falsity) ∉ F.current.locals := by
  intro hl
  exact Formula.not_normalizedReady_falsity (hf.1 _ hl)

/-- Every actual label on every run excludes standalone false. Internal negation
inside encoded disjunction, release or always is not being excluded. -/
theorem inputTableau_run_no_false (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau X root)) :
    Subgraph.AllStates
      {F | Local.predicate (.plain Formula.falsity) ∉ (inputTableau X root).label F} p := by
  have hp := inputTableau_run_normalizedReady X root p hr
  clear hr
  induction p with
  | last => exact fun hl => normalizedReady_current_not_false hp hl.1
  | step l s p ih =>
    exact ⟨fun hl => normalizedReady_current_not_false hp.1 hl.1, ih hp.2⟩

theorem inputTableau_reachable_no_false (X : Set Var) (root : Formula.NormalizedInput Var)
    {q q' : (inputTableau (Clock := Clock) X root).states} {l : EdgeLabel Clock}
    (hi : (l, q.val) ∈ (inputTableau X root).initial)
    (hr : Relation.ReflTransGen (inputTableau X root).ModeStep q q') :
    Local.predicate (.plain Formula.falsity) ∉ (inputTableau X root).label q'.val := by
  have hq := inputTableau_modeSteps_normalizedReady X root hr
    (inputTableau_initial_normalizedReady X root hi)
  exact fun hl => normalizedReady_current_not_false hq hl.1

/-- The syntax invariant also applies to the endpoint of an actual translated
execution, using its graph reachability rather than assuming trace satisfaction. -/
theorem inputAutomaton_final_no_false (root : Formula.NormalizedInput Var)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal
      (finiteRootTableau (Clock := Clock) (rootVariables root.val : Set Var) root.val).HAVar}
    (e : (inputAutomaton (Clock := Clock) root τ hτ).Execution σ) :
    Local.predicate (.plain Formula.falsity) ∉
      (inputTableau (Clock := Clock) (rootVariables root.val : Set Var) root).label
        e.finalState.val.1.val := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  exact inputTableau_reachable_no_false (Clock := Clock)
    (rootVariables root.val : Set Var) root hl
    (Tableau.execution_modeSteps _ _ τ hτ e)

end STLTableau.Section4.Finiteness
