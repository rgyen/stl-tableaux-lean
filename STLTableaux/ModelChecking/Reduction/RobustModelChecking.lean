import STLTableaux.ModelChecking.Reduction.ModelCheckingNegation
import STLTableaux.Semantics.Robustness.RobustnessShift

/-! Robustness bounds using a Boolean-equivalent normalization of the
negation of the `ε`-strengthening. The no-goal direction assumes finite
variability of the normalized negation and a full system execution
starting in its first continuous transition. -/
namespace STLTableau.Section4.Finiteness
open Section3 HybridAutomaton
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (φ : Formula Var) (ε : ℝ)
variable (ready : (Formula.neg (φ.thresholdShift ε)).normalizeForTableau.NormalizedReady)
local notation "N" => Formula.normalizeForTableau (Formula.neg (φ.thresholdShift ε))
local notation "Q" => (Subtype.mk N ready : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X Q

/-- A goal-reaching product prefix gives a non-strict upper bound on the
robustness of the projected system signal. -/
theorem robust_product_goal_counterexample (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (aug : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    ((U).systemTableauAutomaton H h aug.horizon).PrelimReachesState aug
        ((U).systemTableauGoal H h aug.horizon) →
      H.IsPrelimPrefix ((U).systemSignal aug) ∧
        ((U).systemSignal aug).Robustness φ
          ⟨0, le_rfl, ((U).systemSignal aug).horizon_pos⟩ ≤ (ε : EReal) := by
  intro h reached
  obtain ⟨system, violation⟩ :=
    normalized_negation_product_goal X (φ.thresholdShift ε) ready H hX vars aug reached
  exact ⟨system, ((U).systemSignal aug).robustness_le_of_not_satisfies_strengthening
    φ nonStrict ε _ violation⟩

/-- Absence of a goal of the composed automaton yields a non-strict lower
bound on robustness for a full system trajectory. -/
theorem robust_no_goal_lower_bound (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) N → Continuous a.function)
    (counterNonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (finiteVariability : σ.HasFiniteVariability N) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    (¬ ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon)) →
      (ε : EReal) ≤ σ.Robustness φ ⟨0, le_rfl, σ.horizon_pos⟩ := by
  intro h noGoal
  have truth := normalized_negation_no_goal_satisfies X (φ.thresholdShift ε) ready H
    hX vars σ e full direct n bound flows functions counterNonStrict finiteVariability noGoal
  exact σ.robustness_ge_of_satisfies_strengthening φ nonStrict ε _ truth

run_elab do
  for name in #[``robust_product_goal_counterexample, ``robust_no_goal_lower_bound] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
