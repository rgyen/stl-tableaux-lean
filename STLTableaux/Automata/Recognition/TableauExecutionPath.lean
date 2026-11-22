import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence

/-! Structural run extraction from a complete finite execution. Flow segments
do not change modes; every discrete edge (including the final tail) is retained.
This does not yet extract a partition or establish trace satisfaction. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

def ModeStep (q q' : T.states) : Prop := ∃ l, (q.val, l, q'.val) ∈ T.edges

theorem discreteSteps_modeSteps {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s') :
    Relation.ReflTransGen T.ModeStep s.val.1 s'.val.1 := by
  apply hj.lift (fun s => s.val.1)
  intro a b hab
  obtain ⟨l, he, _⟩ := (T.discreteStep_iff h τ hτ).mp hab
  exact ⟨l, he⟩

theorem modeSteps_path {q q' : T.states}
    (hq : Relation.ReflTransGen T.ModeStep q q') (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.valid T ∧ p.firstState = q.val ∧
      p.firstIncoming = incoming ∧ p.lastState = q'.val := by
  induction hq using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl => exact ⟨.last incoming _, q'.property, rfl, rfl, rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨l, he⟩ := hab
    obtain ⟨p, hp, hf, hi, hl⟩ := ih l
    refine ⟨.step incoming a.val p, ⟨a.property, hp, ?_⟩, rfl, rfl, hl⟩
    simpa only [hf, hi] using he

theorem execution_start_modeSteps {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ) (i : Fin e.count) :
    Relation.ReflTransGen T.ModeStep e.initialState.val.1 (e.start i).val.1 := by
  have aux : ∀ n (hn : n < e.count),
      Relation.ReflTransGen T.ModeStep e.initialState.val.1
        (e.start ⟨n, hn⟩).val.1 := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact T.discreteSteps_modeSteps h τ hτ e.initialSteps
    | succ n ih =>
      intro hn
      have hp : n < e.count := by omega
      have prev := ih hp
      rw [(e.continuousStep ⟨n, hp⟩).1] at prev
      exact prev.trans (T.discreteSteps_modeSteps h τ hτ
        (e.discreteSteps ⟨n, hp⟩ hn).to_reflTransGen)
  exact aux i.val i.isLt

theorem execution_modeSteps {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ) :
    Relation.ReflTransGen T.ModeStep e.initialState.val.1 e.finalState.val.1 := by
  have hn : e.count - 1 < e.count := by have := e.nonempty; omega
  have prev := T.execution_start_modeSteps h τ hτ e ⟨e.count - 1, hn⟩
  rw [(e.continuousStep ⟨e.count - 1, hn⟩).1] at prev
  exact prev.trans (T.discreteSteps_modeSteps h τ hτ e.finalSteps)

/-- Every execution yields a structural tableau run, independently of any
well-behavedness or finite-variability assumption. -/
theorem execution_run {σ : FiniteSignal T.HAVar}
    (e : (T.toAutomaton h τ hτ).Execution σ) :
    ∃ p : Path Clock State, p.run T ∧ p.lastState = e.finalState.val.1.val := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  obtain ⟨p, hp, hf, hi, hend⟩ :=
    T.modeSteps_path (T.execution_modeSteps h τ hτ e) l
  refine ⟨p, ⟨hp, ?_⟩, hend⟩
  simpa only [hf, hi] using hl

theorem reaches_accepting_run {σ : FiniteSignal T.HAVar}
    (hr : (T.toAutomaton h τ hτ).Reaches σ T.goalModes) :
    ∃ p : Path Clock State, p.run T ∧ p.accepting T := by
  obtain ⟨e, hg⟩ := hr
  obtain ⟨p, hp, hend⟩ := T.execution_run h τ hτ e
  exact ⟨p, hp, hp.1, hend ▸ hg⟩

end STLTableau.Section4.Tableau
