import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition
import STLTableaux.Automata.Recognition.TableauSignalProjection

/-! Actual execution observations for positive pieces and singleton pieces.
An intermediate zero-time state is observed through the following flow (or
an early final endpoint). No direct shortcut edge is required. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
variable {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

/-- Evidence locating one selected state and its raw interval in an execution.
This does not select a path or claim every intermediate state needs a piece. -/
inductive ExecutionObservedPiece : State → ℝ → ℝ → Prop
  | flow (i : Fin e.count) :
      ExecutionObservedPiece (e.start i).val.1.val
        (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨i.val + 1, by omega⟩)
  | beforeFlow (i : Fin e.count) (s : (T.toAutomaton h τ hτ).State)
      (steps : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s (e.start i)) :
      ExecutionObservedPiece s.val.1.val
        (e.boundary ⟨i.val, by omega⟩) (e.boundary ⟨i.val, by omega⟩)
  | atFinal (s : (T.toAutomaton h τ hτ).State)
      (steps : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s e.finalState)
      (early : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
      ExecutionObservedPiece s.val.1.val
        (e.boundary ⟨e.count, by omega⟩) (e.boundary ⟨e.count, by omega⟩)

/-- An observed piece begins inside the signal domain, never at its horizon. -/
theorem ExecutionObservedPiece.left_lt_horizon
    {s : State} {l r : ℝ} (ho : T.ExecutionObservedPiece h τ hτ e s l r) :
    l < σ.horizon := by
  cases ho with
  | flow i | beforeFlow i _ _ =>
      exact (e.increasing (show
        (⟨i.val, by omega⟩ : Fin (e.count + 1)) < ⟨e.count, by omega⟩ from i.isLt)).trans_le
          e.last_le_horizon
  | atFinal _ _ he => exact he

theorem ExecutionObservedPiece.left_le_right
    {s : State} {l r : ℝ} (ho : T.ExecutionObservedPiece h τ hτ e s l r) : l ≤ r := by
  cases ho with
  | flow i => exact e.increasing.monotone (by change i.val ≤ i.val + 1; omega)
  | beforeFlow | atFinal => exact le_rfl

/-- Raw atomic observations are consequences of invariants and real-variable
preservation along the actual discrete chain, not extra semantic premises. -/
theorem ExecutionObservedPiece.atom
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {s : State} {l r : ℝ} (ho : T.ExecutionObservedPiece h τ hτ e s l r)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s)
    (u : ρ.Time) (hu : u.val ∈ (if l = r then {l} else Set.Ico l r)) :
    a.Holds (ρ.value u) := by
  let t : σ.Time := ⟨u.val, u.property.1, hp.1.symm ▸ u.property.2⟩
  cases ho with
  | flow i =>
    have hlt := e.increasing (show (⟨i.val, by omega⟩ : Fin (e.count + 1)) <
      ⟨i.val + 1, by omega⟩ by change i.val < i.val + 1; omega)
    rw [if_neg (ne_of_lt hlt)] at hu
    exact T.execution_projected_atom h τ hτ e hp i t u rfl hu a ha
  | beforeFlow i s hj =>
    have hu' : u.val = e.boundary ⟨i.val, by omega⟩ := by simpa using hu
    exact T.execution_projected_preflow_atom h τ hτ e hp i hj t u rfl hu' a ha
  | atFinal s hj _ =>
    have hu' : u.val = e.boundary ⟨e.count, by omega⟩ := by simpa using hu
    exact T.execution_projected_final_atom h τ hτ e hp hj t u rfl hu' a ha

/-- An observed flow also supplies its endpoint atoms whenever that endpoint
is in the signal domain. Intermediate jumps preserve real variables; an early
last endpoint is read by `final_signal_eq`. No signal value at the horizon is
introduced. Consequently either adjacent interval may own a shared point. -/
theorem ExecutionObservedPiece.closed_atom
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {s : State} {l r : ℝ} (ho : T.ExecutionObservedPiece h τ hτ e s l r)
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s)
    (u : ρ.Time) (hu : u.val ∈ Set.Icc l r) :
    a.Holds (ρ.value u) := by
  let t : σ.Time := ⟨u.val, u.property.1, hp.1.symm ▸ u.property.2⟩
  cases ho with
  | flow i =>
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact T.execution_projected_atom h τ hτ e hp i t u rfl ⟨hu.1, hlt⟩ a ha
    · by_cases hi : i.val + 1 < e.count
      · exact T.execution_projected_finish_atom h τ hτ e hp i hi t u rfl heq a ha
      · have hilast : i = ⟨e.count - 1, by have := e.nonempty; omega⟩ :=
          Fin.ext (by change i.val = e.count - 1; have := i.isLt; omega)
        have hend : (⟨i.val + 1, by omega⟩ : Fin (e.count + 1)) =
            ⟨e.count, by omega⟩ :=
          Fin.ext (by change i.val + 1 = e.count; have := i.isLt; omega)
        have ha' : Section3.Local.predicate (.plain (.atom a)) ∈
            T.label (e.finish i).val.1.val := by
          rwa [← (e.continuousStep i).1]
        rw [hilast] at ha'
        exact T.execution_projected_final_atom h τ hτ e hp e.finalSteps t u rfl
          (heq.trans (congrArg e.boundary hend)) a ha'
  | beforeFlow i s hj =>
    exact T.execution_projected_preflow_atom h τ hτ e hp i hj t u rfl
      (le_antisymm hu.2 hu.1) a ha
  | atFinal s hj _ =>
    exact T.execution_projected_final_atom h τ hτ e hp hj t u rfl
      (le_antisymm hu.2 hu.1) a ha

theorem ExecutionObservedPiece.raw_atom
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin n) {s : State}
    (ho : T.ExecutionObservedPiece h τ hτ e s
      (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩))
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label s)
    (u : ρ.Time) (hu : u.val ∈ IntervalPartition.rawBoundaryPiece b i) :
    a.Holds (ρ.value u) :=
  ho.atom T h τ hτ e hp a ha u hu

end STLTableau.Section4.Tableau
