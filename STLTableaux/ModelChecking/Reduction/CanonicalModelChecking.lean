/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Semantics.Intervals.CanonicalPartitionRefinement
import STLTableaux.Automata.Translation.CanonicalTranslationCorrectness
import STLTableaux.ModelChecking.Preprocessing.NormalizedVariability
import STLTableaux.ModelChecking.Preprocessing.ClosedTableauInput
import STLTableaux.ModelChecking.Preprocessing.NormalizedViolation

/-! Theorem 5.7 and Corollary 5.8 use an admissible property execution
synchronized with a prefix of a system execution that realizes the whole signal. -/
namespace STLTableau.Section4.Finiteness
open Section3 HybridAutomaton
variable {Clock Var Mode Label : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var)

theorem canonicalReady (root : Formula.NormalizedInput Var) (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X) :
    (finiteTableau (Clock := Clock) X root.val).TranslationReady :=
  finiteTableau_translationReady X root.val hX vars

section Boolean
variable (root : Formula.NormalizedInput Var)
local notation "U" => finiteTableau (Clock := Clock) X root.val

/-- Used in the proof of Theorem 5.7(1). A synchronized goal witness
yields a system trajectory satisfying the tableau input. -/
theorem canonical_goal_formula (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (σ : FiniteSignal Var) :
    (U).CanonicalReaches H (canonicalReady X root hX vars) σ →
      H.IsPrelimTrajectory σ ∧ σ.Satisfies root.val ⟨0,le_rfl,σ.horizon_pos⟩ := by
  rintro ⟨e,d,goal⟩
  refine ⟨⟨d.system,d.full⟩,?_⟩
  have hgoal : e.VisitsGoal := e.visitsGoal_of_end (d.monitor_goal_of_jointGoal goal)
  obtain ⟨P,_,recognized⟩ :=
    (canonical_translation_correctness (Clock := Clock) X root hX vars nonStrict σ).2.2 e hgoal
  exact finiteTableau_sound X root.val σ P recognized

/-- Used in the contrapositive proof of Theorem 5.7(2). Refine at system
flow boundaries and synchronize a recognizing path on that refinement
with the system flows and bounded jumps. -/
theorem canonical_goal_of_formula (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (σ : FiniteSignal Var) (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0, sys.nonempty⟩) (n : ℕ)
    (bounded : ∀ (k : Fin sys.count) (live : k.val + 1 < sys.count),
      H.BoundedZeroTime n (sys.finish k) (sys.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (fv : σ.HasFiniteVariability root.val)
    (truth : σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩) :
    (U).CanonicalReaches (H.boundedZeroTimeExtension n) (canonicalReady X root hX vars) σ := by
  obtain ⟨P,stable⟩ := fv
  obtain ⟨R,_,fine,stableR⟩ := sys.exists_common_stable_flow_refinement full P root.val stable
  obtain ⟨Q,finer,form⟩ := R.exists_canonical_refinement σ
  have stableQ := stableR.of_finer finer
  have recognized : (U).recognizes Generated.labels_finite σ Q :=
    (finiteTableau_recognizes_normalized_input X root σ Q stableQ).2 truth
  let sys' := sys.inZeroTimeExtension H n
  have single (k : Fin sys'.count) (live : k.val+1 < sys'.count) :
      (H.boundedZeroTimeExtension n).DiscreteStep (sys'.finish k) (sys'.start ⟨k.val+1,live⟩) :=
    (H.extension_step_iff n).2 (Or.inr (bounded k live))
  obtain ⟨empty, g, l, continuation⟩ :=
    finiteTableau_final_continuation (Clock := Clock) X root.val
  obtain ⟨e,goal,⟨d⟩⟩ := (U).canonical_forward_with_system
    (canonicalReady X root hX vars) σ Q sys' full direct single flows
    (IntervalPartition.finerThan_trans finer fine) form Generated.labels_finite recognized
    (fun q a ha => let sub := finiteTableau_atom_subformula X root.val q a ha
                   ⟨nonStrict a sub,functions a sub⟩) empty g l continuation
  exact ⟨e,d,d.jointGoal goal⟩

/-- The reachability-to-formula implication also applies to the bounded
extension: its original system projection is recovered by unfolding. -/
theorem canonical_bounded_goal_formula (H : HybridAutomaton Mode Label Var) (n : ℕ)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (σ : FiniteSignal Var)
    (reached : (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X root hX vars) σ) :
    H.IsPrelimTrajectory σ ∧ σ.Satisfies root.val ⟨0,le_rfl,σ.horizon_pos⟩ := by
  obtain ⟨full,truth⟩ := canonical_goal_formula (Clock := Clock) X root
    (H.boundedZeroTimeExtension n) hX vars nonStrict σ reached
  exact ⟨(H.boundedZeroTimeExtension_trajectory_iff n σ).1 full,truth⟩

/-- Boolean absence of goals for the actual tableau input. This theorem
does not assume that preprocessing a raw negation is Boolean-exact. -/
theorem canonical_no_goal_excludes_formula (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (σ : FiniteSignal Var) (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0, sys.nonempty⟩) (n : ℕ)
    (bounded : ∀ (k : Fin sys.count) (live : k.val + 1 < sys.count),
      H.BoundedZeroTime n (sys.finish k) (sys.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (fv : σ.HasFiniteVariability root.val)
    (noGoal : ¬ (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X root hX vars) σ) :
    ¬ σ.Satisfies root.val ⟨0,le_rfl,σ.horizon_pos⟩ :=
  fun truth => noGoal (canonical_goal_of_formula X root H hX vars nonStrict functions
    σ sys full direct n bounded flows fv truth)

end Boolean

section Negation
variable (φ : Formula Var)
variable (ready : (Formula.neg φ).normalizeForTableau.NormalizedReady)
local notation "N" => Formula.normalizeForTableau (Formula.neg φ)
local notation "Q" => (Subtype.mk N ready : Formula.NormalizedInput Var)
local notation "U" => finiteTableau (Clock := Clock) X N

/-- Used in the proof of Theorem 5.7(1). A goal for the tableau of the Boolean-equivalent
normalized negation gives a system trajectory that violates the property. -/
theorem canonical_negation_goal (H : HybridAutomaton Mode Label Var) (n : ℕ)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (σ : FiniteSignal Var)
    (goal : (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X Q hX vars) σ) :
    H.IsPrelimTrajectory σ ∧ ¬ σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  obtain ⟨full,truth⟩ := canonical_bounded_goal_formula (Clock := Clock) X Q H n hX vars
    nonStrict σ goal
  exact ⟨full,(Formula.satisfies_normalizeViolation φ σ _).1 truth⟩

theorem canonical_negation_no_goal (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) N → Continuous a.function)
    (σ : FiniteSignal Var) (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0, sys.nonempty⟩) (n : ℕ)
    (bounded : ∀ (k : Fin sys.count) (live : k.val + 1 < sys.count),
      H.BoundedZeroTime n (sys.finish k) (sys.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (fv : σ.HasFiniteVariability φ)
    (noGoal : ¬ (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X Q hX vars) σ) :
    σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  classical
  by_contra violation
  exact canonical_no_goal_excludes_formula X Q H hX vars nonStrict functions
    σ sys full direct n bounded flows (fv.normalizeViolation ready nonStrict) noGoal
    ((Formula.satisfies_normalizeViolation φ σ _).2 violation)

/-- Theorem 5.7 at a fixed horizon. The initial condition includes the initial
jump closure. The end of each flow and the start of the next must admit
a chain of one to `n` zero-time jumps. The no-goal direction assumes
finite variability of the original formula `φ`. -/
theorem canonical_model_checking (H : HybridAutomaton Mode Label Var) (τ : ℝ) (n : ℕ)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables N, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) N → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) N → Continuous a.function)
    (flows : H.ContinuousFlows)
    (bounded : ∀ (σ : FiniteSignal Var), σ.horizon = τ →
      ∀ e : H.PrelimExecution σ, e.ReachesHorizon →
        ∀ (k : Fin e.count) (live : k.val+1 < e.count),
          H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val+1,live⟩)) :
    let reaches := ∃ σ : FiniteSignal Var, σ.horizon = τ ∧
      (U).CanonicalReaches (H.withInitialJumpClosure.boundedZeroTimeExtension n)
        (canonicalReady X Q hX vars) σ
    (reaches → ∃ σ : FiniteSignal Var, σ.horizon = τ ∧ H.IsPrelimTrajectory σ ∧
      ¬ σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) ∧
    (¬ reaches → ∀ σ : FiniteSignal Var, σ.horizon = τ → H.IsPrelimTrajectory σ →
      σ.HasFiniteVariability φ → σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) := by
  dsimp only
  constructor
  · rintro ⟨σ,hτ,goal⟩
    obtain ⟨full, violation⟩ :=
      canonical_negation_goal X φ ready H.withInitialJumpClosure n hX vars nonStrict σ goal
    exact ⟨σ, hτ, (H.initialJumpClosure_trajectory_iff σ).mp full, violation⟩
  · intro noGoal σ hτ trajectory fv
    obtain ⟨e,full⟩ := trajectory
    exact canonical_negation_no_goal X φ ready H.withInitialJumpClosure hX vars nonStrict functions
      σ (e.startWithFlow H) full rfl n (bounded σ hτ e full) flows fv
      (fun goal => noGoal ⟨σ,hτ,goal⟩)

end Negation

section Robust
variable (φ : Formula Var) (ε : ℝ)
local notation "Q" => Formula.robustCounterInput φ ε
local notation "U" =>
  finiteTableau (Clock := Clock) X (Subtype.val (Formula.robustCounterInput φ ε))

theorem canonical_robust_goal_upper_bound (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var) :
    (U).CanonicalReaches H (canonicalReady X Q hX vars) σ →
      H.IsPrelimTrajectory σ ∧ σ.Robustness φ ⟨0,le_rfl,σ.horizon_pos⟩ ≤ (ε : EReal) := by
  intro goal
  obtain ⟨trajectory,truth⟩ := canonical_goal_formula (Clock := Clock) X Q H hX vars
    (Formula.closedTableauInput_atoms_ge _) σ goal
  exact ⟨trajectory,Formula.robustness_le_of_satisfies_robustCounterInput φ ε nonStrict σ _ truth⟩

theorem canonical_robust_bounded_goal_upper_bound (H : HybridAutomaton Mode Label Var) (n : ℕ)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (σ : FiniteSignal Var)
    (reached : (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X Q hX vars) σ) :
    H.IsPrelimTrajectory σ ∧ σ.Robustness φ ⟨0,le_rfl,σ.horizon_pos⟩ ≤ (ε : EReal) := by
  obtain ⟨trajectory,truth⟩ := canonical_bounded_goal_formula (Clock := Clock) X Q H n hX vars
    (Formula.closedTableauInput_atoms_ge _) σ reached
  exact ⟨trajectory,Formula.robustness_le_of_satisfies_robustCounterInput φ ε nonStrict σ _ truth⟩

theorem canonical_robust_no_goal_lower_bound (H : HybridAutomaton Mode Label Var)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (σ : FiniteSignal Var) (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0, sys.nonempty⟩) (n : ℕ)
    (bounded : ∀ (k : Fin sys.count) (live : k.val + 1 < sys.count),
      H.BoundedZeroTime n (sys.finish k) (sys.start ⟨k.val + 1, live⟩))
    (flows : H.ContinuousFlows) (fv : σ.HasFiniteVariability (Q).val)
    (noGoal : ¬ (U).CanonicalReaches (H.boundedZeroTimeExtension n)
      (canonicalReady X Q hX vars) σ) :
    (ε : EReal) ≤ σ.Robustness φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  classical
  have truth : σ.Satisfies (φ.thresholdShift ε) ⟨0,le_rfl,σ.horizon_pos⟩ := by
    by_contra violation
    exact canonical_no_goal_excludes_formula X Q H hX vars (Formula.closedTableauInput_atoms_ge _)
      (φ.robustCounterInput_functions_continuous ε nonStrict functions) σ sys full direct n bounded
      flows fv noGoal (φ.satisfies_robustCounterInput_of_violation ε σ _ violation)
  exact σ.robustness_ge_of_satisfies_strengthening φ nonStrict ε _ truth

/-- Corollary 5.8 at a fixed horizon. The lower bound in the no-goal case
assumes finite variability for `robustCounterInput`. -/
theorem canonical_robust_model_checking (H : HybridAutomaton Mode Label Var) (τ : ℝ) (n : ℕ)
    (hX : X.Finite) (vars : ∀ x ∈ rootVariables (Q).val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge)
    (functions : ∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function)
    (flows : H.ContinuousFlows)
    (bounded : ∀ (σ : FiniteSignal Var), σ.horizon = τ →
      ∀ e : H.PrelimExecution σ, e.ReachesHorizon →
        ∀ (k : Fin e.count) (live : k.val+1 < e.count),
          H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val+1,live⟩)) :
    let reaches := ∃ σ : FiniteSignal Var, σ.horizon = τ ∧
      (U).CanonicalReaches (H.withInitialJumpClosure.boundedZeroTimeExtension n)
        (canonicalReady X Q hX vars) σ
    (reaches → ∃ σ : FiniteSignal Var, σ.horizon = τ ∧ H.IsPrelimTrajectory σ ∧
      σ.Robustness φ ⟨0,le_rfl,σ.horizon_pos⟩ ≤ (ε : EReal)) ∧
    (¬ reaches → ∀ σ : FiniteSignal Var, σ.horizon = τ → H.IsPrelimTrajectory σ →
      σ.HasFiniteVariability (Q).val → (ε : EReal) ≤ σ.Robustness φ ⟨0,le_rfl,σ.horizon_pos⟩) := by
  dsimp only
  constructor
  · rintro ⟨σ,hτ,goal⟩
    obtain ⟨full, upper⟩ := canonical_robust_bounded_goal_upper_bound X φ ε
      H.withInitialJumpClosure n hX vars nonStrict σ goal
    exact ⟨σ, hτ, (H.initialJumpClosure_trajectory_iff σ).mp full, upper⟩
  · intro noGoal σ hτ trajectory fv
    obtain ⟨e,full⟩ := trajectory
    exact canonical_robust_no_goal_lower_bound X φ ε H.withInitialJumpClosure hX vars nonStrict
      functions σ (e.startWithFlow H) full rfl n (bounded σ hτ e full) flows fv
      (fun goal => noGoal ⟨σ,hτ,goal⟩)

end Robust

run_elab do
  for decl in #[``canonical_goal_formula, ``canonical_goal_of_formula,
      ``canonical_bounded_goal_formula, ``canonical_no_goal_excludes_formula,
      ``canonical_negation_goal, ``canonical_negation_no_goal, ``canonical_model_checking,
      ``canonical_robust_goal_upper_bound, ``canonical_robust_bounded_goal_upper_bound,
      ``canonical_robust_no_goal_lower_bound, ``canonical_robust_model_checking] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness
