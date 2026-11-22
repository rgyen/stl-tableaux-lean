import STLTableaux.Automata.Execution.ExecutionProjection

/-! Both component projections preserve the whole observed prefix, exact stop
and every state visit. Standard trajectory closure handles component idles.
In particular full-horizon trajectories project to full-horizon trajectories.
This is the projection direction, not the converse/pasting theorem. -/
namespace STLTableau.HybridAutomaton
variable {Mode₁ Label₁ Var₁ Mode₂ Label₂ Var₂ Name : Type*}
variable (H₁ : HybridAutomaton Mode₁ Label₁ Var₁)
variable (H₂ : HybridAutomaton Mode₂ Label₂ Var₂)
variable (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name)
local notation "P" => H₁.parallelOn H₂ ι₁ ι₂
local notation "L" => H₁.leftStateOn H₂ ι₁ ι₂
local notation "R" => H₁.rightStateOn H₂ ι₁ ι₂

def leftExecutionProjection : ExecutionProjection (P) H₁ where
  mode := Prod.fst
  coordinate := leftVar ι₁ ι₂
  state := L
  state_val := fun _ => rfl
  initial := fun _ h => h.1
  flow := H₁.parallelOn_continuous_left H₂ ι₁ ι₂
  discrete := fun step => H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ (.single step)

def rightExecutionProjection : ExecutionProjection (P) H₂ where
  mode := Prod.snd
  coordinate := rightVar ι₁ ι₂
  state := R
  state_val := fun _ => rfl
  initial := fun _ h => h.2
  flow := H₁.parallelOn_continuous_right H₂ ι₁ ι₂
  discrete := fun step => H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ (.single step)

namespace PrelimExecution
variable {H₁ H₂ ι₁ ι₂} {σ : FiniteSignal (JoinedVar ι₁ ι₂)}

theorem leftGoalProjection (e : (P).PrelimExecution σ) :
    ∃ out : H₁.PrelimExecution (σ.reindex (leftVar ι₁ ι₂)),
      out.finalState = L e.finalState ∧
      out.boundary ⟨out.count, by omega⟩ = e.boundary ⟨e.count, by omega⟩ ∧
      ∀ s, e.VisitsState s → out.VisitsState (L s) :=
  (H₁.leftExecutionProjection H₂ ι₁ ι₂).execution e

theorem rightGoalProjection (e : (P).PrelimExecution σ) :
    ∃ out : H₂.PrelimExecution (σ.reindex (rightVar ι₁ ι₂)),
      out.finalState = R e.finalState ∧
      out.boundary ⟨out.count, by omega⟩ = e.boundary ⟨e.count, by omega⟩ ∧
      ∀ s, e.VisitsState s → out.VisitsState (R s) :=
  (H₁.rightExecutionProjection H₂ ι₁ ι₂).execution e

theorem leftFullProjection (e : (P).PrelimExecution σ) (full : e.ReachesHorizon) :
    ∃ out : H₁.PrelimExecution (σ.reindex (leftVar ι₁ ι₂)), out.ReachesHorizon ∧
      out.finalState = L e.finalState ∧
      ∀ s, e.VisitsState s → out.VisitsState (L s) :=
  (H₁.leftExecutionProjection H₂ ι₁ ι₂).full_execution e full

theorem rightFullProjection (e : (P).PrelimExecution σ) (full : e.ReachesHorizon) :
    ∃ out : H₂.PrelimExecution (σ.reindex (rightVar ι₁ ι₂)), out.ReachesHorizon ∧
      out.finalState = R e.finalState ∧
      ∀ s, e.VisitsState s → out.VisitsState (R s) :=
  (H₁.rightExecutionProjection H₂ ι₁ ι₂).full_execution e full

end PrelimExecution

theorem parallelOn_trajectory_left {σ : FiniteSignal (JoinedVar ι₁ ι₂)}
    (full : (P).IsPrelimTrajectory σ) :
    H₁.IsPrelimTrajectory (σ.reindex (leftVar ι₁ ι₂)) :=
  (H₁.leftExecutionProjection H₂ ι₁ ι₂).trajectory full

theorem parallelOn_trajectory_right {σ : FiniteSignal (JoinedVar ι₁ ι₂)}
    (full : (P).IsPrelimTrajectory σ) :
    H₂.IsPrelimTrajectory (σ.reindex (rightVar ι₁ ι₂)) :=
  (H₁.rightExecutionProjection H₂ ι₁ ι₂).trajectory full

theorem parallelOn_reachesState_left
    (σ : FiniteSignal (JoinedVar ι₁ ι₂)) (goal : Set H₁.State)
    (reached : (P).PrelimReachesState σ {s | L s ∈ goal}) :
    H₁.PrelimReachesState (σ.reindex (leftVar ι₁ ι₂)) goal :=
  (H₁.leftExecutionProjection H₂ ι₁ ι₂).reaches goal reached

theorem parallelOn_reachesState_right
    (σ : FiniteSignal (JoinedVar ι₁ ι₂)) (goal : Set H₂.State)
    (reached : (P).PrelimReachesState σ {s | R s ∈ goal}) :
    H₂.PrelimReachesState (σ.reindex (rightVar ι₁ ι₂)) goal :=
  (H₁.rightExecutionProjection H₂ ι₁ ι₂).reaches goal reached

run_elab do
  for n in #[``PrelimExecution.leftGoalProjection, ``PrelimExecution.rightGoalProjection,
      ``PrelimExecution.leftFullProjection, ``PrelimExecution.rightFullProjection,
      ``parallelOn_trajectory_left, ``parallelOn_trajectory_right,
      ``parallelOn_reachesState_left, ``parallelOn_reachesState_right] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.HybridAutomaton

namespace STLTableau.Section4.Tableau
variable {Clock Var State Mode Label SystemVar Name : Type*}
variable (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ)
variable (H : HybridAutomaton Mode Label SystemVar)
variable (ι₁ : SystemVar ↪ Name) (ι₂ : T.TypedVar ↪ Name)

/-- Project a goal visit of the shared product onto `prelimAutomaton`. -/
theorem parallel_prelim_goal_projection
    (σ : FiniteSignal (HybridAutomaton.JoinedVar ι₁ ι₂))
    (reached : (H.parallelOn (T.prelimAutomaton h τ) ι₁ ι₂).PrelimReachesState σ
      {s | H.rightStateOn (T.prelimAutomaton h τ) ι₁ ι₂ s ∈ T.prelimGoal h τ}) :
    (T.prelimAutomaton h τ).PrelimReachesState
      (σ.reindex (HybridAutomaton.rightVar ι₁ ι₂)) (T.prelimGoal h τ) :=
  H.parallelOn_reachesState_right (T.prelimAutomaton h τ) ι₁ ι₂
    σ (T.prelimGoal h τ) reached

end STLTableau.Section4.Tableau
