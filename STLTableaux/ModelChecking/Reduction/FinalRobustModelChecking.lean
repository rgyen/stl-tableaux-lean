import STLTableaux.ModelChecking.Preprocessing.ClosedTableauInput
import STLTableaux.ModelChecking.Reduction.ModelCheckingConverse
import STLTableaux.ModelChecking.Reduction.SourceTrajectoryGoal

/-! Robustness bounds using `robustCounterInput`, the normalized tableau
input obtained from the negation of the `ε`-strengthening with non-strict
atomic predicates. The system execution covers the whole signal. The
goal-reaching execution of the composed automaton may end earlier. -/
namespace STLTableau.Section4.Finiteness
open Section3 HybridAutomaton
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (φ : Formula Var) (ε : ℝ)
local notation "Q" => Formula.robustCounterInput φ ε
local notation "U" => withEmptyContinuation (Clock := Clock) X Q

/-- A product goal yields a system execution prefix and a robustness upper
bound for its signal. -/
theorem final_robust_product_goal_counterexample (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (aug : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX (Q).val vars)
    ((U).systemTableauAutomaton H h aug.horizon).PrelimReachesState aug
        ((U).systemTableauGoal H h aug.horizon) →
      H.IsPrelimPrefix ((U).systemSignal aug) ∧
        ((U).systemSignal aug).Robustness φ
          ⟨0, le_rfl, ((U).systemSignal aug).horizon_pos⟩ ≤ (ε : EReal) := by
  intro h reached
  obtain ⟨system, truth⟩ := finite_systemTableau_goal_formula X Q H hX vars aug reached
  exact ⟨system, Formula.robustness_le_of_satisfies_robustCounterInput
    φ ε nonStrict _ _ truth⟩

/-- A product goal gives a robustness upper bound on the supplied full system
trajectory, even if the goal occurs before the horizon. -/
theorem final_robust_goal_on_source_trajectory (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (aug : FiniteSignal (U).CompositionVar) (projection : (U).systemSignal aug = σ) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX (Q).val vars)
    ((U).systemTableauAutomaton H h aug.horizon).PrelimReachesState aug
        ((U).systemTableauGoal H h aug.horizon) →
      H.IsPrelimTrajectory σ ∧ σ.Robustness φ ⟨0, le_rfl, σ.horizon_pos⟩ ≤ (ε : EReal) := by
  intro h reached
  obtain ⟨system, truth⟩ := finite_systemTableau_goal_on_source_trajectory
    X Q H hX vars σ e full aug projection reached
  exact ⟨system, Formula.robustness_le_of_satisfies_robustCounterInput
    φ ε nonStrict σ _ truth⟩

/-- A violation of the strengthened formula yields a goal-reaching product
prefix when the signal has finite variability for `robustCounterInput`. -/
theorem final_robust_product_prefix_of_violation (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (finiteVariability : σ.HasFiniteVariability (Q).val)
    (violation : ¬ σ.Satisfies (φ.thresholdShift ε) ⟨0, le_rfl, σ.horizon_pos⟩) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX (Q).val vars)
    ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon) := by
  exact finite_systemTableau_prefix_of_finiteVariability X Q H hX vars σ e full direct n bound
    flows (φ.robustCounterInput_functions_continuous ε nonStrict functions)
    (Formula.closedTableauInput_atoms_ge _) finiteVariability
    (φ.satisfies_robustCounterInput_of_violation ε σ _ violation)

/-- If the product cannot reach a goal, the supplied system trajectory satisfies
the robustness lower bound. Finite variability is for `robustCounterInput`. -/
theorem final_robust_no_goal_lower_bound (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (finiteVariability : σ.HasFiniteVariability (Q).val) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX (Q).val vars)
    (¬ ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon)) →
      (ε : EReal) ≤ σ.Robustness φ ⟨0, le_rfl, σ.horizon_pos⟩ := by
  classical
  intro h noGoal
  have truth : σ.Satisfies (φ.thresholdShift ε) ⟨0, le_rfl, σ.horizon_pos⟩ := by
    by_contra violation
    exact noGoal (final_robust_product_prefix_of_violation X φ ε H hX vars nonStrict
      functions σ e full direct n bound flows finiteVariability violation)
  exact σ.robustness_ge_of_satisfies_strengthening φ nonStrict ε _ truth

run_elab do
  for name in #[``final_robust_product_goal_counterexample,
      ``final_robust_goal_on_source_trajectory, ``final_robust_product_prefix_of_violation,
      ``final_robust_no_goal_lower_bound] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
