import STLTableaux.Automata.Composition.SystemTableauComposition
import STLTableaux.Automata.Translation.PrelimStateGoalCorrectness
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition

/-! From a goal in the product, derive satisfaction of the tableau input.
The system projection realizes the whole signal when the product execution
reaches the horizon. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root
variable (H : HybridAutomaton Mode Label Var)

theorem empty_systemTableau_goal_recognizes {τ : ℝ} (h : (U).TranslationReady)
    (σ : FiniteSignal (U).CompositionVar) (horizon : σ.horizon = τ)
    (reached : ((U).systemTableauAutomaton H h τ).PrelimReachesState σ
      ((U).systemTableauGoal H h τ)) :
    H.IsPrelimPrefix ((U).systemSignal σ) ∧
      ∃ P : IntervalPartition ((U).systemSignal σ).domain,
        (U).recognizes JudgementTableau.labels_finite ((U).systemSignal σ) P := by
  obtain ⟨system, monitor, projection⟩ := (U).systemTableau_goal_projections H h τ σ reached
  obtain ⟨e, s, goal, visit⟩ := monitor
  obtain ⟨P, _, recognized⟩ := empty_prelim_partition_of_goal_visit X root h e horizon
    ((U).systemSignal σ) projection s goal visit
  exact ⟨system, P, recognized⟩

theorem empty_systemTableau_goal_formula {τ : ℝ} (h : (U).TranslationReady)
    (σ : FiniteSignal (U).CompositionVar) (horizon : σ.horizon = τ)
    (reached : ((U).systemTableauAutomaton H h τ).PrelimReachesState σ
      ((U).systemTableauGoal H h τ)) :
    H.IsPrelimPrefix ((U).systemSignal σ) ∧
      ((U).systemSignal σ).Satisfies root.val
        ⟨0, le_rfl, ((U).systemSignal σ).horizon_pos⟩ := by
  obtain ⟨system, P, recognized⟩ :=
    empty_systemTableau_goal_recognizes X root H h σ horizon reached
  exact ⟨system, formula_of_emptyContinuation_recognizes X root _ P recognized⟩

/-- Readiness is derived from the finite variable support; the caller supplies
only a genuine goal-reaching execution of the concrete composed automaton. -/
theorem finite_systemTableau_goal_formula (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ((U).systemTableauAutomaton H h σ.horizon).PrelimReachesState σ
        ((U).systemTableauGoal H h σ.horizon) →
      H.IsPrelimPrefix ((U).systemSignal σ) ∧
        ((U).systemSignal σ).Satisfies root.val
          ⟨0, le_rfl, ((U).systemSignal σ).horizon_pos⟩ := by
  intro h reached
  exact empty_systemTableau_goal_formula X root H h σ rfl reached

/-- An existential product goal yields a system execution prefix whose signal
satisfies the tableau input. -/
theorem finite_systemTableau_goal_exists (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    (∃ σ : FiniteSignal (U).CompositionVar,
      ((U).systemTableauAutomaton H h σ.horizon).PrelimReachesState σ
        ((U).systemTableauGoal H h σ.horizon)) →
      ∃ ρ : FiniteSignal Var, H.IsPrelimPrefix ρ ∧
        ρ.Satisfies root.val ⟨0, le_rfl, ρ.horizon_pos⟩ := by
  intro h reached
  obtain ⟨σ, goal⟩ := reached
  obtain ⟨system, formula⟩ := finite_systemTableau_goal_formula X root H hX vars σ goal
  exact ⟨(U).systemSignal σ, system, formula⟩

/-- A goal in a full product execution gives a system trajectory satisfying the
tableau input. The goal may occur before the last flow endpoint. -/
theorem empty_systemTableau_full_goal_formula {τ : ℝ} (h : (U).TranslationReady)
    (σ : FiniteSignal (U).CompositionVar) (horizon : σ.horizon = τ)
    (e : ((U).systemTableauAutomaton H h τ).PrelimExecution σ) (full : e.ReachesHorizon)
    {s : ((U).systemTableauAutomaton H h τ).State}
    (goal : s ∈ (U).systemTableauGoal H h τ) (visit : e.VisitsState s) :
    H.IsPrelimTrajectory ((U).systemSignal σ) ∧
      ((U).systemSignal σ).Satisfies root.val
        ⟨0, le_rfl, ((U).systemSignal σ).horizon_pos⟩ := by
  obtain ⟨system, _, monitor, projection⟩ :=
    (U).systemTableau_full_goal_projections H h τ σ e full goal visit
  obtain ⟨out, state, reached, visited⟩ := monitor
  obtain ⟨P, _, recognized⟩ := empty_prelim_partition_of_goal_visit X root h out horizon
    ((U).systemSignal σ) projection state reached visited
  exact ⟨system, formula_of_emptyContinuation_recognizes X root _ P recognized⟩

theorem finite_systemTableau_full_goal_formula (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ∀ e : ((U).systemTableauAutomaton H h σ.horizon).PrelimExecution σ,
      e.ReachesHorizon →
      (∃ s ∈ (U).systemTableauGoal H h σ.horizon, e.VisitsState s) →
      H.IsPrelimTrajectory ((U).systemSignal σ) ∧
        ((U).systemSignal σ).Satisfies root.val
          ⟨0, le_rfl, ((U).systemSignal σ).horizon_pos⟩ := by
  intro h e full ⟨s, goal, visit⟩
  exact empty_systemTableau_full_goal_formula X root H h σ rfl e full goal visit

theorem finite_systemTableau_full_goal_exists (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    (∃ (σ : FiniteSignal (U).CompositionVar)
      (e : ((U).systemTableauAutomaton H h σ.horizon).PrelimExecution σ),
      e.ReachesHorizon ∧ ∃ s ∈ (U).systemTableauGoal H h σ.horizon, e.VisitsState s) →
      ∃ ρ : FiniteSignal Var, H.IsPrelimTrajectory ρ ∧
        ρ.Satisfies root.val ⟨0, le_rfl, ρ.horizon_pos⟩ := by
  intro h ⟨σ, e, full, goal⟩
  obtain ⟨system, formula⟩ := finite_systemTableau_full_goal_formula X root H hX vars σ e full goal
  exact ⟨(U).systemSignal σ, system, formula⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``empty_systemTableau_goal_recognizes, ``empty_systemTableau_goal_formula,
      ``finite_systemTableau_goal_formula, ``finite_systemTableau_goal_exists,
      ``empty_systemTableau_full_goal_formula, ``finite_systemTableau_full_goal_formula,
      ``finite_systemTableau_full_goal_exists] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
