import STLTableaux.Automata.Composition.SystemTableauJumpLift
import STLTableaux.Automata.Recognition.PrelimPartitionConnection
import STLTableaux.Automata.Recognition.ProjectedFlowAssembly

namespace STLTableau.Section4.Tableau
open Section3 HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

/-- A joint state is determined by its two actual component projections. -/
theorem systemTableau_state_ext (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.systemTableauAutomaton H h τ).State}
    (left : H.leftStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName a =
      H.leftStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName b)
    (right : H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName a =
      H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName b) : a = b := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · exact Prod.ext (congrArg (fun s => s.val.1) left) (congrArg (fun s => s.val.1) right)
  · funext x
    rcases every_joined_variable T.systemVarName T.tableauVarName x with
      ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact congrFun (congrArg (fun s => s.val.2) left) x
    · exact congrFun (congrArg (fun s => s.val.2) right) x

/-- Lift one positive recognized frame over its actual SYSTEM subflow,
starting at the already constructed product state. -/
theorem projected_system_cell (H : HybridAutomaton Mode Label Var)
    (h : T.TranslationReady) {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (R : IntervalPartition σ.domain) (fine : R.FinerThan (e.fullFlowPartition full))
    (i : Fin R.size) (positive : 0 < (STLTableau.Judgement.duration R i : ℝ))
    (flows : H.ContinuousFlows) (q : T.states) (α : ClockValuation Clock)
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ R α ⟨i.val, by omega⟩)
    (nonStrict : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → a.relation = .ge)
    (functions : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → Continuous a.function)
    (a : (T.systemTableauAutomaton H h σ.horizon).State)
    (system : H.leftStateOn (T.prelimAutomaton h σ.horizon)
      T.systemVarName T.tableauVarName a = e.cellEntryState full R fine i)
    (monitor : (H.rightStateOn (T.prelimAutomaton h σ.horizon)
      T.systemVarName T.tableauVarName a).val =
      (q, T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
        (R.interval i).leftBoundary)) :
    ∃ p : ProjectedFlowPiece (T.systemTableauAutomaton H h σ.horizon) σ T.systemCoordinate,
      p.start = a ∧ p.left = (R.interval i).left ∧
      p.duration = STLTableau.Judgement.duration R i ∧
      H.leftStateOn (T.prelimAutomaton h σ.horizon) T.systemVarName T.tableauVarName p.finish =
        e.cellExitState full R fine i ∧
      (H.rightStateOn (T.prelimAutomaton h σ.horizon)
        T.systemVarName T.tableauVarName p.finish).val =
        (q, T.forwardCurveValue
          (T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
            (R.interval i).leftBoundary)
          (STLTableau.Judgement.duration R i)
          (fun x => (e.cellExitState full R fine i).val.2 x.val)) := by
  let f := e.refinedObservedFlow full R fine i positive
  have endpoints := e.refinedObservedFlow_endpoints full R fine i positive
  have states := e.refinedObservedFlow_states full R fine i positive
  have dur : f.duration = STLTableau.Judgement.duration R i := by
    apply Subtype.ext
    have d := f.duration_eq
    rw [endpoints.1, endpoints.2] at d
    exact d
  have entryReal : f.curve ⟨0, by simp⟩ = σ.value (pieceEntry σ R i) :=
    f.step.2.1.trans ((congrArg (fun s : H.State => s.val.2) states.1).trans
      (e.cell_entry_signal full R fine i).symm)
  have exitReal : f.curve ⟨f.duration, by simp⟩ =
      (e.cellExitState full R fine i).val.2 :=
    f.step.2.2.1.trans (congrArg (fun s : H.State => s.val.2) states.2)
  let v := T.entryValue (R.interval i).left α (σ.value (pieceEntry σ R i))
    (R.interval i).leftBoundary
  have seed : T.entryValue f.beginTime α (f.curve ⟨0, by simp⟩)
      (R.interval i).leftBoundary = v := by rw [endpoints.1, entryReal]
  obtain ⟨b, c, sb, sc, mb, mc, step⟩ := T.systemTableau_flow_over_cell H h f flows
    R i endpoints.1 endpoints.2 q α α labels nonStrict functions
  have same : b = a := by
    apply T.systemTableau_state_ext H h σ.horizon
    · exact sb.trans (states.1.trans system.symm)
    · apply Subtype.ext
      exact mb.trans ((congrArg (fun w => (q, w)) seed).trans monitor.symm)
  let p : ProjectedFlowPiece (T.systemTableauAutomaton H h σ.horizon) σ T.systemCoordinate := {
    left := (R.interval i).left
    duration := f.duration
    positive := f.positive
    start := b
    finish := c
    curve := fun u => T.joinValuation (f.curve u)
      (T.clockLiftCurve (T.entryValue f.beginTime α (f.curve ⟨0, by simp⟩)
        (R.interval i).leftBoundary) f.curve u)
    step := step
    observe := by
      intro t u time before x
      change f.curve u x = σ.value t x
      exact congrFun
        (e.refinedObservedFlow_observe full R fine i positive t u time before) x }
  refine ⟨p, same, rfl, dur, sc.trans states.2, ?_⟩
  apply mc.trans
  apply congrArg (fun w => (q, w))
  change T.forwardCurveValue _ (f.duration : ℝ) (fun x => f.curve ⟨f.duration, by simp⟩ x.val) = _
  have real : (fun x : T.realVariables => f.curve ⟨f.duration, by simp⟩ x.val) =
      fun x : T.realVariables => (e.cellExitState full R fine i).val.2 x.val := by
    funext x
    exact congrFun exitReal x.val
  rw [real, seed]
  exact congrArg (fun t : ℝ => T.forwardCurveValue v t
    (fun x => (e.cellExitState full R fine i).val.2 x.val)) (congrArg NNReal.toReal dur)

run_elab do
  for n in #[``systemTableau_state_ext, ``projected_system_cell] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n}: unexpected axiom {ax}"

end STLTableau.Section4.Tableau
