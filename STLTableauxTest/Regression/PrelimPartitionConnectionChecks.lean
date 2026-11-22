import STLTableaux.Automata.Recognition.PrelimBoundedPartition
import STLTableaux.ModelChecking.Reduction.ModelCheckingConverse
import STLTableaux.ModelChecking.Reduction.ModelCheckingNegation
import STLTableaux.ModelChecking.Reduction.RobustModelChecking
import STLTableaux.ModelChecking.Reduction.FinalRobustModelChecking
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

/-! Two system flows with a jump that resets the physical value from 1 to 2.
In the refinement `[0,1), {1}, (1,2)`, the singleton uses the post-jump
value and the first flow ends at the pre-jump value. -/
namespace PrelimPartitionConnectionChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton Bool Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(false, (), true)}
  initial := {s | s.1 = false ∧ s.2 () = 0}
  invariant := Set.univ
  flow := fun s t v => ∀ x, v x = s.2 x + t
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total x
        dsimp only [Prod.snd] at *
        rw [total x, first x]; push_cast; ring)
    (by intro q v a b r s first second x
        dsimp only [Prod.snd] at *
        rw [second x, first x]; push_cast; ring)
  jump := fun _ a b => a.2 () = 1 ∧ b.2 () = 2
def state (m : Bool) (x : ℝ) : H.State := ⟨(m, fun _ => x), Set.mem_univ _⟩
theorem jump : H.DiscreteStep (state false 1) (state true 2) :=
  ⟨⟨(false, (), true), rfl⟩, rfl, rfl, rfl, rfl⟩
noncomputable def σ : FiniteSignal Unit :=
  ⟨2, by norm_num, fun t _ => if t.val < 1 then t.val else t.val + 1⟩
noncomputable def e : H.PrelimExecution σ where
  count := 2
  nonempty := by decide
  initialState := state false 0
  initial_mem := ⟨rfl, rfl⟩
  start := fun i => if i.val = 0 then state false 0 else state true 2
  finish := fun i => if i.val = 0 then state false 1 else state true 3
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i <;> norm_num
  curve := fun i u _ => if i.val = 0 then u.val else 2 + u.val
  continuousStep := by
    intro i
    fin_cases i
    · refine ⟨rfl, rfl, rfl, ?_⟩
      intro u
      refine ⟨fun _ => ?_, Set.mem_univ _⟩
      change u.val = 0 + u.val
      ring
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · funext x; norm_num [state]
      · funext x; norm_num [state]
      · intro u; exact ⟨fun _ => rfl, Set.mem_univ _⟩
  initialSteps := .refl
  discreteSteps := by
    intro i hi
    have h : i.val = 0 := by omega
    have index : i = ⟨0, by decide⟩ := Fin.ext h
    subst i
    exact .single jump
  signal_eq := by
    intro i t ht
    funext x
    fin_cases i
    · have h : t.val < 1 := by simpa using ht.2
      simp [σ, h]
    · have h : ¬ t.val < 1 := not_lt.mpr (by simpa using ht.1)
      simp [σ, h]
      ring
theorem full : e.ReachesHorizon := by
  unfold PrelimExecution.ReachesHorizon
  dsimp only [e]
  norm_num [σ]
def bs : Fin 4 → ℝ := ![0, 1, 1, 2]
def ms : Fin 4 → Marker := ![●, ●, ○, ●]
def R : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; change i.val ≤ j.val at hij
        fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i <;> norm_num [bs, ms] at *) rfl rfl

theorem fine : R.FinerThan (e.fullFlowPartition full) := by
  intro i
  fin_cases i
  · refine ⟨⟨0, by decide⟩, ?_⟩
    intro t ht
    simpa [R, IntervalPartition.ofSingletonBoundaries, IntervalPartition.markedBoundaryPiece,
      PrelimExecution.fullFlowPartition, IntervalPartition.ofBoundaries,
      MarkedInterval.mem_iff, bs, ms, e] using ht
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro t ht
    change (1 < t ∨ 1 = t ∧ True) ∧ (t < 1 ∨ t = 1 ∧ True) at ht
    simp only [PrelimExecution.fullFlowPartition, IntervalPartition.ofBoundaries,
      MarkedInterval.carrier_eq, Set.mem_Ico]
    dsimp only [e]
    norm_num only
    have equal : t = 1 := by
      rcases ht.1 with h | ⟨h, _⟩ <;>
        rcases ht.2 with h' | ⟨h', _⟩ <;> linarith
    subst t
    constructor <;> norm_num
  · refine ⟨⟨1, by decide⟩, ?_⟩
    intro t ht
    change (1 < t ∨ 1 = t ∧ False) ∧ (t < 2 ∨ t = 2 ∧ False) at ht
    simp only [PrelimExecution.fullFlowPartition, IntervalPartition.ofBoundaries,
      MarkedInterval.carrier_eq, Set.mem_Ico]
    dsimp only [e]
    norm_num only
    rcases ht.1 with lower | ⟨_, impossible⟩
    · refine ⟨lower.le, ?_⟩
      rcases ht.2 with upper | ⟨_, impossible⟩
      · exact upper
      · exact impossible.elim
    · exact impossible.elim

theorem singleton_next_idle :
    e.cellExitState full R fine ⟨1, by decide⟩ =
      e.cellEntryState full R fine ⟨2, by decide⟩ :=
  e.singleton_next_idle full R fine _ _ rfl (by change (1 : ℝ) - 1 = 0; ring)

theorem actual_connector : Relation.ReflTransGen H.DiscreteStep
    (e.cellExitState full R fine ⟨0, by decide⟩)
    (e.cellEntryState full R fine ⟨1, by decide⟩) :=
  e.cell_connector full R fine _ _ rfl

theorem singleton_observes_postjump :
    (e.cellEntryState full R fine ⟨1, by decide⟩).val.2 () = 2 := by
  rw [← e.cell_entry_signal full R fine]
  change (if (1 : ℝ) < 1 then 1 else 1 + 1) = 2
  norm_num

theorem signal_at_jump : σ.value ⟨1, by norm_num, by norm_num [σ]⟩ () = 2 := by
  dsimp only [σ]
  norm_num

theorem singleton_exit_is_entry :
    e.cellExitState full R fine ⟨1, by decide⟩ =
      e.cellEntryState full R fine ⟨1, by decide⟩ :=
  e.singleton_cell_state full R fine _ (by change (1 : ℝ) - 1 = 0; ring)

theorem first_owner : e.cellOwner full R fine ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
  have bounds := e.cell_mem_bounds full R fine ⟨0, by decide⟩ (t := 0) (by
    exact ⟨Or.inr ⟨rfl, trivial⟩, Or.inl (by change (0 : ℝ) < 1; norm_num)⟩)
  have lower : ((e.cellOwner full R fine ⟨0, by decide⟩).val : ℝ) ≤ 0 := bounds.1
  apply Fin.ext
  exact_mod_cast le_antisymm lower (Nat.cast_nonneg _)

theorem first_exit_prejump :
    (e.cellExitState full R fine ⟨0, by decide⟩).val.2 () = 1 := by
  change (if (e.cellOwner full R fine ⟨0, by decide⟩).val = 0 then
    (R.interval ⟨0, by decide⟩).right - e.boundary (e.cellOwner full R fine ⟨0, by decide⟩).castSucc
    else 2 + ((R.interval ⟨0, by decide⟩).right -
      e.boundary (e.cellOwner full R fine ⟨0, by decide⟩).castSucc)) = 1
  rw [first_owner]
  dsimp only [R, IntervalPartition.ofSingletonBoundaries,
    IntervalPartition.markedBoundaryPiece, bs, e]
  norm_num

theorem boundary_values_differ :
    (e.cellExitState full R fine ⟨0, by decide⟩).val.2 () ≠
      (e.cellEntryState full R fine ⟨1, by decide⟩).val.2 () := by
  rw [first_exit_prejump, singleton_observes_postjump]
  norm_num

theorem bounded : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
    H.BoundedZeroTime 1 (e.finish k) (e.start ⟨k.val + 1, live⟩) := by
  intro k live
  have index : k = ⟨0, by decide⟩ := Fin.ext (by
    change k.val = 0
    change k.val + 1 < 2 at live
    omega)
  subst k
  exact H.boundedZeroTime_single (by decide) jump

theorem bounded_boundary_action : (H.boundedZeroTimeExtension 1).DiscreteStep
    (e.cellExitState full R fine ⟨0, by decide⟩)
    (e.cellEntryState full R fine ⟨1, by decide⟩) := by
  rcases e.cell_action_zeroTimeExtension full R fine 1 bounded
      ⟨0, by decide⟩ ⟨1, by decide⟩ rfl with idle | action
  · exact (boundary_values_differ (congrArg (fun s : H.State => s.val.2 ()) idle)).elim
  · exact action

theorem extended_positive_curve_unchanged :
    ((e.inZeroTimeExtension H 1).refinedObservedFlow full R fine ⟨0, by decide⟩
      (by change (0 : ℝ) < 1 - 0; norm_num)).curve =
      (e.refinedObservedFlow full R fine ⟨0, by decide⟩
        (by change (0 : ℝ) < 1 - 0; norm_num)).curve :=
  (e.refinedObservedFlow_inZeroTimeExtension full R fine 1 ⟨0, by decide⟩
    (by change (0 : ℝ) < 1 - 0; norm_num)).2.2

theorem refined_actual_observation (t : σ.Time)
    (u : Set.Icc (0 : ℝ) (e.refinedObservedFlow full R fine ⟨2, by decide⟩
      (by change (0 : ℝ) < 2 - 1; norm_num)).duration)
    (time : (R.interval ⟨2, by decide⟩).left + u.val = t.val)
    (before : u.val < (e.refinedObservedFlow full R fine ⟨2, by decide⟩
      (by change (0 : ℝ) < 2 - 1; norm_num)).duration) :
    (e.refinedObservedFlow full R fine ⟨2, by decide⟩
      (by change (0 : ℝ) < 2 - 1; norm_num)).curve u = σ.value t :=
  e.refinedObservedFlow_observe full R fine _ _ t u time before

open STLTableau.Section4 STLTableau.Section4.Finiteness

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : T.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp))

theorem atom_true (t : σ.Time) : σ.Satisfies root.val t := by
  change (if t.val < 1 then t.val else t.val + 1) ≥ 0
  split_ifs
  · exact t.property.1
  · linarith [t.property.1]

theorem stable : σ.StablePartition root.val R := by
  intro i χ sub t u ht hu
  cases sub
  exact iff_of_true (atom_true t) (atom_true u)

/-- Construct a product goal from the stable partition of the two-flow
system execution. -/
theorem actual_finite_product_goal :
    ∃ aug, T.systemSignal aug = σ ∧
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready σ.horizon).PrelimReachesState
        aug
        (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready σ.horizon) := by
  apply finite_systemTableau_prefix_of_stable (Clock := Nat)
    Set.univ root H Set.finite_univ (by simp) σ e full rfl 1 bounded
    continuous_flows _ _ R stable (atom_true _)
  · intro a sub
    cases sub
    exact continuous_apply (0 : Fin 1)
  · intro a sub
    cases sub
    rfl

def rawNegative : Formula Unit := .atom { p with relation := .lt }

theorem raw_normalized_root :
    (Formula.neg rawNegative).normalizeForTableau = root.val := rfl

theorem raw_normalized_ready :
    (Formula.neg rawNegative).normalizeForTableau.NormalizedReady := .atom p

theorem actual_raw_violation :
    ¬ σ.Satisfies rawNegative ⟨0, le_rfl, σ.horizon_pos⟩ := by
  change ¬ (if (0 : ℝ) < 1 then 0 else 0 + 1) < 0
  norm_num

set_option maxHeartbeats 800000 in
/-- The violation of the raw formula yields a product goal for its
normalized negation. -/
theorem actual_raw_violation_product_goal :
    ∃ aug, T.systemSignal aug = σ ∧
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready σ.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready σ.horizon) := by
  exact normalized_violation_product_prefix (Clock := Nat) Set.univ rawNegative
    raw_normalized_ready H Set.finite_univ (by simp) σ e full rfl 1 bounded
    continuous_flows
    (by intro a sub; cases sub; exact continuous_apply (0 : Fin 1))
    (by intro a sub; cases sub; rfl) ⟨R, stable⟩ actual_raw_violation

set_option maxHeartbeats 800000 in
theorem actual_product_implies_raw_violation :
    ∃ aug, T.systemSignal aug = σ ∧
      (H.boundedZeroTimeExtension 1).IsPrelimPrefix (T.systemSignal aug) ∧
      ¬ (T.systemSignal aug).Satisfies rawNegative
        ⟨0, le_rfl, (T.systemSignal aug).horizon_pos⟩ := by
  obtain ⟨aug, proj, reached⟩ := actual_raw_violation_product_goal
  have horizon : aug.horizon = σ.horizon := congrArg FiniteSignal.horizon proj
  have reachedH :
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready aug.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready aug.horizon) := by
    rw [horizon]
    exact reached
  obtain ⟨system, violation⟩ := normalized_negation_product_goal (Clock := Nat)
    Set.univ rawNegative raw_normalized_ready (H.boundedZeroTimeExtension 1)
    Set.finite_univ (by simp) aug reachedH
  exact ⟨aug, proj, system, violation⟩

set_option maxHeartbeats 800000 in
theorem actual_no_goal_implies_raw_truth :
    (¬ ∃ aug, T.systemSignal aug = σ ∧
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready σ.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready σ.horizon)) →
      σ.Satisfies rawNegative ⟨0, le_rfl, σ.horizon_pos⟩ := by
  exact normalized_negation_no_goal_satisfies (Clock := Nat) Set.univ rawNegative
    raw_normalized_ready H Set.finite_univ (by simp) σ e full rfl 1 bounded
    continuous_flows
    (by intro a sub; cases sub; exact continuous_apply (0 : Fin 1))
    (by intro a sub; cases sub; rfl) ⟨R, stable⟩

def robustAtom : AtomicProposition Unit :=
  ⟨1, fun _ => (), fun v => v 0 - 1, .ge⟩
def robustProperty : Formula Unit := .neg (.atom robustAtom)

theorem robust_normalized_root :
    (Formula.neg (robustProperty.thresholdShift 1)).normalizeForTableau = root.val := by
  have functions : (fun v : Fin 1 → ℝ => (v 0 - 1) - -(1 : ℝ)) =
      (fun v : Fin 1 → ℝ => v 0) := by funext v; ring
  change Formula.atom ⟨1, (fun _ => ()), (fun v => (v 0 - 1) - -(1 : ℝ)), .ge⟩ =
    Formula.atom p
  rw [functions]
  rfl

theorem robust_normalized_ready :
    (Formula.neg (robustProperty.thresholdShift 1)).normalizeForTableau.NormalizedReady := by
  rw [robust_normalized_root]
  exact root.property

theorem robust_nonStrict : ∀ atom, Formula.IsSubformula (.atom atom) robustProperty →
    atom.relation = .ge := by
  intro atom sub
  cases sub with
  | neg sub => cases sub; rfl

set_option maxHeartbeats 1200000 in
/-- A goal of the composed automaton gives a robustness upper bound of 1 on
the full system trajectory using the Boolean-equivalent normalized negation. -/
theorem actual_numeric_robust_counterexample :
    H.IsPrelimTrajectory σ ∧
      σ.Robustness robustProperty ⟨0, le_rfl, σ.horizon_pos⟩ ≤ (1 : EReal) := by
  have bridge : ∀ aug : FiniteSignal T.CompositionVar,
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready aug.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready aug.horizon) →
      (H.boundedZeroTimeExtension 1).IsPrelimPrefix (T.systemSignal aug) ∧
        (T.systemSignal aug).Robustness robustProperty
          ⟨0, le_rfl, (T.systemSignal aug).horizon_pos⟩ ≤ (1 : EReal) := by
    have roots : (⟨(Formula.neg (robustProperty.thresholdShift 1)).normalizeForTableau,
        robust_normalized_ready⟩ : Formula.NormalizedInput Unit) = root :=
      Subtype.ext robust_normalized_root
    let U := withEmptyContinuation (Clock := Nat) Set.univ
      (⟨(Formula.neg (robustProperty.thresholdShift 1)).normalizeForTableau,
        robust_normalized_ready⟩ : Formula.NormalizedInput Unit)
    have all : ∀ h : U.TranslationReady, ∀ aug : FiniteSignal U.CompositionVar,
        (U.systemTableauAutomaton (H.boundedZeroTimeExtension 1) h aug.horizon).PrelimReachesState
          aug (U.systemTableauGoal (H.boundedZeroTimeExtension 1) h aug.horizon) →
        (H.boundedZeroTimeExtension 1).IsPrelimPrefix (U.systemSignal aug) ∧
          (U.systemSignal aug).Robustness robustProperty
            ⟨0, le_rfl, (U.systemSignal aug).horizon_pos⟩ ≤ (1 : EReal) := by
      intro h aug
      exact robust_product_goal_counterexample (Clock := Nat) Set.univ robustProperty 1
        robust_normalized_ready (H.boundedZeroTimeExtension 1) Set.finite_univ
        (by simp [robust_normalized_root]) robust_nonStrict aug
    have graph : U = T := congrArg (withEmptyContinuation (Clock := Nat) Set.univ) roots
    rw [graph] at all
    exact all ready
  obtain ⟨aug, projection, reached⟩ := actual_finite_product_goal
  have horizon : aug.horizon = σ.horizon := congrArg FiniteSignal.horizon projection
  have reachedH :
      (T.systemTableauAutomaton (H.boundedZeroTimeExtension 1) ready aug.horizon).PrelimReachesState
        aug (T.systemTableauGoal (H.boundedZeroTimeExtension 1) ready aug.horizon) := by
    rw [horizon]
    exact reached
  have numeric := (bridge aug reachedH).2
  refine ⟨⟨e, full⟩, ?_⟩
  rw [projection] at numeric
  exact numeric

theorem robust_final_input_eq : Formula.robustCounterInput robustProperty 1 = root := by
  apply Subtype.ext
  change (Formula.eliminateFalsity
    (Formula.neg (robustProperty.thresholdShift 1)).normalizeForTableau
    (Formula.mixedReady_normalizeForTableau _)).val.closeNonStrictAtoms = root.val
  rw [Formula.eliminateFalsity_eq_of_normalizedReady _ _ robust_normalized_ready,
    robust_normalized_root]
  rfl

noncomputable def finalT :=
  withEmptyContinuation (Clock := Nat) Set.univ (Formula.robustCounterInput robustProperty 1)

theorem final_ready : finalT.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ _ (by simp))

theorem robust_functions : ∀ atom, Formula.IsSubformula (.atom atom) robustProperty →
    Continuous atom.function := by
  intro atom sub
  cases sub with
  | neg sub => cases sub; exact (continuous_apply (0 : Fin 1)).sub continuous_const

theorem final_finiteVariability :
    σ.HasFiniteVariability (Formula.robustCounterInput robustProperty 1).val := by
  rw [robust_final_input_eq]
  exact ⟨R, stable⟩

theorem strengthening_violated :
    ¬ σ.Satisfies (robustProperty.thresholdShift 1) ⟨0, le_rfl, σ.horizon_pos⟩ := by
  change ¬ ¬ ((if (0 : ℝ) < 1 then 0 else 0 + 1) - 1 - -(1 : ℝ)) ≥ 0
  norm_num

set_option maxHeartbeats 1200000 in
/-- Construct a product goal using `robustCounterInput` for robustness threshold 1. -/
theorem actual_final_product_goal :
    ∃ aug, finalT.systemSignal aug = σ ∧
      PrelimReachesState
        (finalT.systemTableauAutomaton (H.boundedZeroTimeExtension 1) final_ready σ.horizon) aug
        (finalT.systemTableauGoal (H.boundedZeroTimeExtension 1) final_ready σ.horizon) := by
  exact final_robust_product_prefix_of_violation (Clock := Nat) Set.univ robustProperty 1
    H Set.finite_univ (by simp) robust_nonStrict robust_functions σ e full rfl 1 bounded
    continuous_flows final_finiteVariability strengthening_violated

set_option maxHeartbeats 1200000 in
/-- With `robustCounterInput`, a goal of the composed automaton yields a
robustness upper bound on the full system trajectory. -/
theorem actual_final_robust_counterexample :
    H.IsPrelimTrajectory σ ∧
      σ.Robustness robustProperty ⟨0, le_rfl, σ.horizon_pos⟩ ≤ (1 : EReal) := by
  obtain ⟨aug, projection, reached⟩ := actual_final_product_goal
  have horizon : aug.horizon = σ.horizon := congrArg FiniteSignal.horizon projection
  have reachedH :
      PrelimReachesState
        (finalT.systemTableauAutomaton (H.boundedZeroTimeExtension 1) final_ready aug.horizon) aug
        (finalT.systemTableauGoal (H.boundedZeroTimeExtension 1) final_ready aug.horizon) := by
    rw [horizon]
    exact reached
  obtain ⟨system, numeric⟩ := final_robust_goal_on_source_trajectory (Clock := Nat)
    Set.univ robustProperty 1 (H.boundedZeroTimeExtension 1) Set.finite_univ (by simp)
    robust_nonStrict σ (e.inZeroTimeExtension H 1) full aug projection reachedH
  exact ⟨(H.boundedZeroTimeExtension_trajectory_iff 1 σ).mp system, numeric⟩

set_option maxHeartbeats 1200000 in
theorem actual_final_no_goal_lower_bound :
    (¬ ∃ aug, finalT.systemSignal aug = σ ∧
      PrelimReachesState
        (finalT.systemTableauAutomaton (H.boundedZeroTimeExtension 1) final_ready σ.horizon) aug
        (finalT.systemTableauGoal (H.boundedZeroTimeExtension 1) final_ready σ.horizon)) →
      (1 : EReal) ≤ σ.Robustness robustProperty ⟨0, le_rfl, σ.horizon_pos⟩ := by
  exact final_robust_no_goal_lower_bound (Clock := Nat) Set.univ robustProperty 1 H
    Set.finite_univ (by simp) robust_nonStrict robust_functions σ e full rfl 1 bounded
    continuous_flows final_finiteVariability

theorem truth_final_input_eq :
    (Formula.robustCounterInput (Formula.truth : Formula Unit) 1).val =
      .atom Formula.falseAtom := by
  have spec := Formula.eliminateFalsity_spec
    (Formula.neg ((Formula.truth : Formula Unit).thresholdShift 1)).normalizeForTableau
    (Formula.mixedReady_normalizeForTableau _)
  change Formula.FalsityElimination Formula.falsity _ at spec
  have unique : ∀ ψ : Formula Unit, Formula.FalsityElimination Formula.falsity ψ →
      ψ = .atom Formula.falseAtom := by
    intro ψ h
    cases h
    rfl
  have equal := unique _ spec
  change (Formula.eliminateFalsity _ _).val.closeNonStrictAtoms = _
  rw [equal]
  rfl

noncomputable def truthT :=
  withEmptyContinuation (Clock := Nat) Set.univ
    (Formula.robustCounterInput (Formula.truth : Formula Unit) 1)

theorem truth_ready : truthT.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ _ (by simp))

theorem truth_finiteVariability :
    σ.HasFiniteVariability (Formula.robustCounterInput (Formula.truth : Formula Unit) 1).val := by
  rw [truth_final_input_eq]
  refine ⟨R, ?_⟩
  intro i ψ sub t u ht hu
  cases sub
  change ((-1 : ℝ) ≥ 0) ↔ ((-1 : ℝ) ≥ 0)
  rfl

set_option maxHeartbeats 1200000 in
theorem actual_truth_no_goal :
    ¬ ∃ aug, truthT.systemSignal aug = σ ∧
      PrelimReachesState
        (truthT.systemTableauAutomaton (H.boundedZeroTimeExtension 1) truth_ready σ.horizon) aug
        (truthT.systemTableauGoal (H.boundedZeroTimeExtension 1) truth_ready σ.horizon) := by
  rintro ⟨aug, projection, reached⟩
  have horizon : aug.horizon = σ.horizon := congrArg FiniteSignal.horizon projection
  have reachedH :
      PrelimReachesState
        (truthT.systemTableauAutomaton (H.boundedZeroTimeExtension 1) truth_ready aug.horizon) aug
        (truthT.systemTableauGoal (H.boundedZeroTimeExtension 1) truth_ready aug.horizon) := by
    rw [horizon]
    exact reached
  have numeric := (final_robust_product_goal_counterexample (Clock := Nat)
    Set.univ (Formula.truth : Formula Unit) 1 (H.boundedZeroTimeExtension 1)
    Set.finite_univ (by simp) (by intro a sub; cases sub) aug reachedH).2
  change (⊤ : EReal) ≤ (1 : EReal) at numeric
  exact (not_le_of_gt (EReal.coe_lt_top 1)) numeric

set_option maxHeartbeats 1200000 in
/-- Absence of a goal of the composed automaton gives the robustness lower bound
for the truth formula. -/
theorem actual_truth_no_goal_lower_bound :
    (1 : EReal) ≤ σ.Robustness (Formula.truth : Formula Unit)
      ⟨0, le_rfl, σ.horizon_pos⟩ := by
  exact final_robust_no_goal_lower_bound (Clock := Nat) Set.univ Formula.truth 1 H
    Set.finite_univ (by simp) (by intro a sub; cases sub) (by intro a sub; cases sub)
    σ e full rfl 1 bounded continuous_flows truth_finiteVariability actual_truth_no_goal

run_elab do
  for name in #[``full, ``fine, ``singleton_next_idle, ``actual_connector,
      ``singleton_observes_postjump, ``first_exit_prejump, ``boundary_values_differ,
      ``signal_at_jump, ``singleton_exit_is_entry,
      ``bounded_boundary_action, ``extended_positive_curve_unchanged,
      ``refined_actual_observation, ``actual_finite_product_goal,
      ``raw_normalized_root, ``raw_normalized_ready, ``actual_raw_violation,
      ``actual_raw_violation_product_goal, ``actual_product_implies_raw_violation,
      ``actual_no_goal_implies_raw_truth, ``robust_normalized_root,
      ``robust_normalized_ready, ``robust_nonStrict,
      ``actual_numeric_robust_counterexample, ``robust_final_input_eq, ``robust_functions,
      ``final_finiteVariability, ``strengthening_violated, ``actual_final_product_goal,
      ``actual_final_robust_counterexample, ``actual_final_no_goal_lower_bound,
      ``truth_final_input_eq, ``truth_finiteVariability, ``actual_truth_no_goal,
      ``actual_truth_no_goal_lower_bound] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end PrelimPartitionConnectionChecks
