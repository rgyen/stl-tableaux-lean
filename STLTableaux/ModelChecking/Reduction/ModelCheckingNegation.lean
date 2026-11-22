import STLTableaux.ModelChecking.Preprocessing.NormalizedViolation
import STLTableaux.Finiteness.Correctness.NormalizedRootTableau
import STLTableaux.ModelChecking.Reduction.ModelCheckingForward
import STLTableaux.ModelChecking.Reduction.ModelCheckingConverse

/-! Exact Boolean connections for normalized raw negation. Recognition works
in the mixed grammar. Product results require the normalized input
grammar; construction retains normalized-root FV and non-strictness premises.
No robustness equivalence or unconditional arbitrary-input reduction is claimed. -/
namespace STLTableau.Section4.Finiteness
open Section3 HybridAutomaton
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (raw : Formula Var)

theorem normalized_negation_recognizes_iff (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (stable : σ.StablePartition (Formula.neg raw).normalizeForTableau P) :
    (normalizedRootTableau (Clock := Clock) X (Formula.neg raw)).recognizes
      JudgementTableau.labels_finite σ P ↔
      ¬ σ.Satisfies raw ⟨0, le_rfl, σ.horizon_pos⟩ := by
  simpa only [FiniteSignal.Satisfies] using
    normalizedRootTableau_recognizes_iff (Clock := Clock) X (Formula.neg raw) σ P stable

theorem normalized_negation_recognition_sound (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (recognized : (normalizedRootTableau (Clock := Clock) X (Formula.neg raw)).recognizes
      JudgementTableau.labels_finite σ P) :
    ¬ σ.Satisfies raw ⟨0, le_rfl, σ.horizon_pos⟩ :=
  normalizedRootTableau_sound X (Formula.neg raw) σ P recognized

variable (ready : (Formula.neg raw).normalizeForTableau.NormalizedReady)
local notation "N" => Formula.normalizeForTableau (Formula.neg raw)
local notation "Q" => (Subtype.mk N ready : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X Q

/-- A goal-reaching execution of the composed automaton supplies a system
execution prefix. The projected signal violates the input formula at time
zero. -/
theorem normalized_negation_product_goal (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (aug : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    ((U).systemTableauAutomaton H h aug.horizon).PrelimReachesState aug
        ((U).systemTableauGoal H h aug.horizon) →
      H.IsPrelimPrefix ((U).systemSignal aug) ∧
        ¬ ((U).systemSignal aug).Satisfies raw
          ⟨0, le_rfl, ((U).systemSignal aug).horizon_pos⟩ := by
  intro h reached
  obtain ⟨system, truth⟩ := finite_systemTableau_goal_formula X Q H hX vars aug reached
  exact ⟨system, (Formula.satisfies_normalizeViolation raw _ _).mp truth⟩

/-- A goal visit in a full execution of the composed automaton yields a full system trajectory. -/
theorem normalized_negation_full_product_goal (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (aug : FiniteSignal (U).CompositionVar) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    ∀ e : ((U).systemTableauAutomaton H h aug.horizon).PrelimExecution aug,
      e.ReachesHorizon →
      (∃ s ∈ (U).systemTableauGoal H h aug.horizon, e.VisitsState s) →
      H.IsPrelimTrajectory ((U).systemSignal aug) ∧
        ¬ ((U).systemSignal aug).Satisfies raw
          ⟨0, le_rfl, ((U).systemSignal aug).horizon_pos⟩ := by
  intro h e full visit
  obtain ⟨system, truth⟩ :=
    finite_systemTableau_full_goal_formula X Q H hX vars aug e full visit
  exact ⟨system, (Formula.satisfies_normalizeViolation raw _ _).mp truth⟩

/-- A raw violation constructs an actual bounded-extension product prefix
when its normalized negation meets the existing construction's hypotheses. -/
theorem normalized_violation_product_prefix (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) N → Continuous a.function)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (finiteVariability : σ.HasFiniteVariability N)
    (violation : ¬ σ.Satisfies raw ⟨0, le_rfl, σ.horizon_pos⟩) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon) := by
  exact finite_systemTableau_prefix_of_finiteVariability X Q H hX vars σ e full direct
    n bound flows functions nonStrict finiteVariability
    ((Formula.satisfies_normalizeViolation raw σ _).mpr violation)

/-- No projected goal prefix implies raw satisfaction only under the
explicit normalized-negation construction hypotheses above. -/
theorem normalized_negation_no_goal_satisfies (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) N → Continuous a.function)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (finiteVariability : σ.HasFiniteVariability N) :
    let h := withEmptyContinuation_ready (Clock := Clock) X Q
      (finiteRootTableau_translationReady X hX N vars)
    (¬ ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon)) →
      σ.Satisfies raw ⟨0, le_rfl, σ.horizon_pos⟩ := by
  intro h noGoal
  have absent := finite_systemTableau_no_goal_excludes_root X Q H hX vars σ e full
    direct n bound flows functions nonStrict finiteVariability noGoal
  by_contra violation
  exact absent ((Formula.satisfies_normalizeViolation raw σ _).mpr violation)

run_elab do
  for name in #[``normalized_negation_recognizes_iff, ``normalized_negation_recognition_sound,
      ``normalized_negation_product_goal, ``normalized_negation_full_product_goal,
      ``normalized_violation_product_prefix, ``normalized_negation_no_goal_satisfies] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
