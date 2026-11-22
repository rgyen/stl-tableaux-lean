import STLTableaux.Automata.Composition.SystemTableauForwardExecution
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Automata.Translation.EmptyContinuationSupport

/-! Construct actual composed goal-reaching prefixes for checked normalized inputs.
The SYSTEM witness is full, but the constructed product may stop at an early
goal. No full product trajectory or arbitrary-input normalization is asserted. -/
namespace STLTableau.Section4.Finiteness
open Section3 HybridAutomaton
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root

/-- Refine a supplied stable partition by the actual SYSTEM flow cells,
obtain a recognized finite-tableau path, and construct its product prefix. -/
theorem finite_systemTableau_prefix_of_stable
    (H : HybridAutomaton Mode Label Var) (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (P : IntervalPartition σ.domain) (stable : σ.StablePartition root.val P)
    (truth : σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug
        ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon) := by
  intro h
  obtain ⟨R, _, fine, stableR⟩ :=
    e.exists_common_stable_flow_refinement full P root.val stable
  have recognized : (U).recognizes JudgementTableau.labels_finite σ R :=
    (emptyContinuation_recognizes_iff (Clock := Clock) X root σ R).2
      ((inputTableau_recognizes_iff (Clock := Clock) X root σ R stableR).2 truth)
  obtain ⟨empty, _, goal, labels, continuation⟩ :=
    empty_continuation_data (Clock := Clock) X root
  apply (U).systemTableau_forward_of_bounded_recognized H h e full direct n bound R fine
    root.val flows functions JudgementTableau.labels_finite recognized _
    empty goal labels continuation
  intro q a ha
  have sub := emptyContinuation_atom_subformula X root q a ha
  exact ⟨nonStrict a sub, sub⟩

/-- Finite variability supplies exactly the stable partition required above.
No stability of a different normalized formula is inferred. -/
theorem finite_systemTableau_prefix_of_finiteVariability
    (H : HybridAutomaton Mode Label Var) (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (finiteVariability : σ.HasFiniteVariability root.val)
    (truth : σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug
        ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon) := by
  obtain ⟨P, stable⟩ := finiteVariability
  exact finite_systemTableau_prefix_of_stable X root H hX vars σ e full direct n bound
    flows functions nonStrict P stable truth

/-- Absence of a projected product goal prefix excludes the normalized input
on the given finite-variable SYSTEM trajectory. This is not an
arbitrary raw-formula negation or normalization theorem. -/
theorem finite_systemTableau_no_goal_excludes_root
    (H : HybridAutomaton Mode Label Var) (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (σ : FiniteSignal Var) (e : H.PrelimExecution σ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩)
    (n : ℕ) (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (finiteVariability : σ.HasFiniteVariability root.val) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    (¬ ∃ aug, (U).systemSignal aug = σ ∧
      ((U).systemTableauAutomaton (H.boundedZeroTimeExtension n) h σ.horizon).PrelimReachesState
        aug
        ((U).systemTableauGoal (H.boundedZeroTimeExtension n) h σ.horizon)) →
      ¬ σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ := by
  intro h noGoal truth
  exact noGoal (finite_systemTableau_prefix_of_finiteVariability X root H hX vars
    σ e full direct n bound flows functions nonStrict finiteVariability truth)

run_elab do
  for name in #[``finite_systemTableau_prefix_of_stable,
      ``finite_systemTableau_prefix_of_finiteVariability,
      ``finite_systemTableau_no_goal_excludes_root] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
