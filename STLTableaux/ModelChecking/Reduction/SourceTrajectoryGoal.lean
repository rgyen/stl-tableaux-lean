import STLTableaux.ModelChecking.Reduction.ModelCheckingForward

/-! A goal-reaching PRODUCT prefix can be interpreted on its supplied full
SYSTEM trajectory. No continuation or full-horizon PRODUCT witness is required. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root

theorem finite_systemTableau_goal_on_source_trajectory
    (H : HybridAutomaton Mode Label Var) (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (aug : FiniteSignal (U).CompositionVar) (projection : (U).systemSignal aug = σ) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ((U).systemTableauAutomaton H h aug.horizon).PrelimReachesState aug
        ((U).systemTableauGoal H h aug.horizon) →
      H.IsPrelimTrajectory σ ∧ σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ := by
  intro h reached
  obtain ⟨_, truth⟩ := finite_systemTableau_goal_formula X root H hX vars aug reached
  refine ⟨⟨e, full⟩, ?_⟩
  subst σ
  exact truth

run_elab do
  for ax in ← Lean.collectAxioms ``finite_systemTableau_goal_on_source_trajectory do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
