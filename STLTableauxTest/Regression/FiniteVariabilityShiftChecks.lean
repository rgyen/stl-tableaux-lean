import STLTableaux.ModelChecking.Preprocessing.NormalizedViolation
import STLTableaux.ModelChecking.Preprocessing.NonStrictAtoms
import STLTableaux.Semantics.Robustness.RobustnessShift
import STLTableaux.Semantics.Partitions.PartitionDurationAlignment
import STLTableaux.Semantics.Partitions.BoundaryPartition
import STLTableaux.Automata.Execution.WellBehaved
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Formula-specific finite variability is not preserved by a positive
threshold shift, even for a continuous ge atom over the continuous ramp.
This refutes an automatic premise-transfer lemma, not the entire manuscript's
model-checking conclusion. -/
namespace FiniteVariabilityShiftChecks
open STLTableau

noncomputable def wiggle (x : ℝ) : ℝ :=
  (1 - x) * Real.sin (1 / (1 - x))
noncomputable def margin (x : ℝ) : ℝ := 1 + wiggle x
def σ : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => t.val⟩
noncomputable def atom : AtomicProposition Unit :=
  ⟨1, fun _ => (), fun v => margin (v 0), .ge⟩
noncomputable def φ : Formula Unit := .atom atom

theorem wiggle_bound (x : ℝ) : |wiggle x| ≤ |1 - x| := by
  rw [wiggle, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / (1 - x))) (abs_nonneg (1 - x))

theorem continuous_wiggle : Continuous wiggle := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases equal : x = 1
  · subst x
    apply Metric.continuousAt_iff.mpr
    intro ε positive
    refine ⟨ε, positive, ?_⟩
    intro y near
    have zero : wiggle 1 = 0 := by simp [wiggle]
    rw [zero, Real.dist_eq, sub_zero]
    exact (wiggle_bound y).trans_lt (by simpa only [Real.dist_eq, abs_sub_comm] using near)
  · have denominator : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm equal)
    exact (continuousAt_const.sub continuousAt_id).mul
      (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) denominator))

theorem continuous_margin : Continuous margin := continuous_const.add continuous_wiggle
theorem continuous_atom : Continuous atom.function :=
  continuous_margin.comp (continuous_apply (0 : Fin 1))

theorem original_true (t : σ.Time) : σ.Satisfies φ t := by
  change 0 ≤ 1 + (1 - t.val) * Real.sin (1 / (1 - t.val))
  have upper : t.val < 1 := t.property.2
  have lower := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (1 / (1 - t.val)))
    (by linarith : 0 ≤ 1 - t.val)
  linarith [t.property.1]

def P : IntervalPartition σ.domain :=
  IntervalPartition.ofBoundaries (n := 1) ![(0 : ℝ), 1] (by
    intro i j order
    fin_cases i <;> fin_cases j <;> norm_num at *)

theorem original_finite_variability : σ.HasFiniteVariability φ := by
  refine ⟨P, ?_⟩
  intro i ψ sub
  cases sub
  intro t u _ _
  exact iff_of_true (original_true t) (original_true u)

/-- A finite interval partition necessarily has a stable open tail. -/
private theorem stable_tail {Var : Type*} {s : FiniteSignal Var} {ψ : Formula Var}
    (finite : s.HasFiniteVariability ψ) :
    ∃ a < s.horizon, ∀ t u : s.Time, a < t.val → a < u.val →
      (s.Satisfies ψ t ↔ s.Satisfies ψ u) := by
  obtain ⟨Q, stable⟩ := finite
  have size := Q.size_pos_of_domain_nonempty
    (show s.domain.Nonempty from ⟨0, le_rfl, s.horizon_pos⟩)
  let i : Fin Q.size := ⟨Q.size - 1, by omega⟩
  have last : i.val + 1 = Q.size := by dsimp [i]; omega
  have right := Q.last_right_eq_domain_right i last
  obtain ⟨x, member⟩ := Q.nonempty i
  have domain : x ∈ s.domain := by
    rw [← Q.covers]
    exact Set.mem_iUnion.mpr ⟨i, member⟩
  refine ⟨(Q.interval i).left, (MarkedInterval.left_le_of_mem member).trans_lt domain.2, ?_⟩
  intro t u lower lower'
  exact (stable i).stable t u
    ⟨Or.inl lower, Or.inl (right.symm ▸ t.property.2)⟩
    ⟨Or.inl lower', Or.inl (right.symm ▸ u.property.2)⟩

noncomputable def sample (θ : ℝ) (n : ℕ) : ℝ :=
  1 - 1 / (θ + n * (2 * Real.pi))

theorem wiggle_sample (θ : ℝ) (n : ℕ) :
    wiggle (sample θ n) = (1 / (θ + n * (2 * Real.pi))) * Real.sin θ := by
  unfold wiggle sample
  have cancel : 1 - (1 - 1 / (θ + n * (2 * Real.pi))) =
      1 / (θ + n * (2 * Real.pi)) := by ring
  rw [cancel, one_div_one_div, Real.sin_add_nat_mul_two_pi]

private theorem sample_in_tail (a θ : ℝ) (before : a < 1) (positive : 0 < θ) :
    ∃ n : ℕ, a < sample θ n ∧ 0 ≤ sample θ n ∧ sample θ n < 1 := by
  obtain ⟨n, large⟩ := exists_nat_gt (max (1 : ℝ) (1 / (1 - a)))
  have nlarge : (1 : ℝ) < n := (le_max_left _ _).trans_lt large
  have inverse : (1 : ℝ) / (1 - a) < n := (le_max_right _ _).trans_lt large
  have factor : (1 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  have denominator : (n : ℝ) < θ + n * (2 * Real.pi) := by nlinarith
  have pos : 0 < θ + n * (2 * Real.pi) := by linarith
  have small : (1 : ℝ) / (θ + n * (2 * Real.pi)) < 1 :=
    (div_lt_iff₀ pos).2 (by linarith)
  have cutoff : (1 : ℝ) / (θ + n * (2 * Real.pi)) < 1 - a := by
    apply (div_lt_iff₀ pos).2
    have larger := (div_lt_iff₀ (by linarith : 0 < 1 - a)).1 (inverse.trans denominator)
    nlinarith
  refine ⟨n, ?_, ?_, ?_⟩
  · dsimp [sample]; linarith
  · dsimp [sample]; linarith
  · dsimp [sample]
    have positiveInverse := one_div_pos.mpr pos
    linarith

theorem opposite_margins_in_every_tail (a : ℝ) (before : a < 1) :
    ∃ t u : σ.Time, a < t.val ∧ a < u.val ∧ 0 < wiggle t.val ∧ wiggle u.val < 0 := by
  obtain ⟨n, after, nonneg, below⟩ := sample_in_tail a (Real.pi / 2) before (by
    linarith [Real.pi_pos])
  obtain ⟨m, after', nonneg', below'⟩ := sample_in_tail a (Real.pi / 2 + Real.pi) before (by
    linarith [Real.pi_pos])
  refine ⟨⟨sample (Real.pi / 2) n, nonneg, below⟩,
    ⟨sample (Real.pi / 2 + Real.pi) m, nonneg', below'⟩, after, after', ?_, ?_⟩
  · rw [wiggle_sample, Real.sin_pi_div_two, mul_one]
    apply one_div_pos.mpr
    positivity
  · rw [wiggle_sample, Real.sin_add_pi, Real.sin_pi_div_two]
    have positive : 0 < 1 / (Real.pi / 2 + Real.pi + (m : ℝ) * (2 * Real.pi)) := by
      positivity
    nlinarith

theorem strengthening_not_finite_variability :
    ¬ σ.HasFiniteVariability (φ.thresholdShift 1) := by
  intro finite
  obtain ⟨a, before, stable⟩ := stable_tail finite
  obtain ⟨t, u, after, after', positive, negative⟩ := opposite_margins_in_every_tail a before
  have yes : σ.Satisfies (φ.thresholdShift 1) t := by
    change 0 ≤ (1 + wiggle t.val) - 1
    linarith
  have no : ¬ σ.Satisfies (φ.thresholdShift 1) u := by
    change ¬ 0 ≤ (1 + wiggle u.val) - 1
    linarith
  exact no ((stable t u after after').mp yes)

theorem normalized_violation_not_finite_variability :
    ¬ σ.HasFiniteVariability (Formula.neg (φ.thresholdShift 1)).normalizeForTableau := by
  intro finite
  obtain ⟨a, before, stable⟩ := stable_tail finite
  obtain ⟨t, u, after, after', positive, negative⟩ := opposite_margins_in_every_tail a before
  have yes : σ.Satisfies (φ.thresholdShift 1) t := by
    change 0 ≤ (1 + wiggle t.val) - 1
    linarith
  have no : ¬ σ.Satisfies (φ.thresholdShift 1) u := by
    change ¬ 0 ≤ (1 + wiggle u.val) - 1
    linarith
  have source := (Formula.satisfies_normalizeViolation (φ.thresholdShift 1) σ u).2 no
  have target := (stable t u after after').mpr source
  exact ((Formula.satisfies_normalizeViolation (φ.thresholdShift 1) σ t).1 target) yes

noncomputable def squareAtom : AtomicProposition Unit :=
  ⟨1, fun _ => (), fun v => (wiggle (v 0)) ^ 2, .ge⟩
noncomputable def exactNegative : Formula Unit :=
  (Formula.neg (.atom squareAtom)).normalizeForTableau

theorem continuous_square_atom : Continuous squareAtom.function :=
  (continuous_wiggle.pow 2).comp (continuous_apply (0 : Fin 1))

theorem square_input_true (t : σ.Time) : σ.Satisfies (.atom squareAtom) t :=
  sq_nonneg _

theorem square_input_finite_variability : σ.HasFiniteVariability (.atom squareAtom) := by
  refine ⟨P, ?_⟩
  intro i ψ sub
  cases sub
  intro t u _ _
  exact iff_of_true (square_input_true t) (square_input_true u)

theorem exact_negative_false (t : σ.Time) : ¬ σ.Satisfies exactNegative t := by
  change ¬ (wiggle t.val) ^ 2 < 0
  exact not_lt_of_ge (sq_nonneg _)

theorem exact_negative_finite_variability : σ.HasFiniteVariability exactNegative := by
  refine ⟨P, ?_⟩
  intro i ψ sub
  cases sub
  intro t u _ _
  exact iff_of_false (exact_negative_false t) (exact_negative_false u)

/-- Even an exact negated ge atom with FV can lose FV at non-strict closure.
The source ge atom and its strict Boolean complement both have constant truth. -/
theorem closed_negative_not_finite_variability :
    ¬ σ.HasFiniteVariability exactNegative.closeNonStrictAtoms := by
  intro finite
  obtain ⟨a, before, stable⟩ := stable_tail finite
  obtain ⟨n, after, nonneg, below⟩ := sample_in_tail a Real.pi before Real.pi_pos
  let t : σ.Time := ⟨sample Real.pi n, nonneg, below⟩
  have zero : wiggle t.val = 0 := by
    change wiggle (sample Real.pi n) = 0
    rw [wiggle_sample, Real.sin_pi, mul_zero]
  have yes : σ.Satisfies exactNegative.closeNonStrictAtoms t := by
    change 0 ≤ -(wiggle t.val) ^ 2
    rw [zero]
    norm_num
  obtain ⟨u, _, after', _, positive, _⟩ := opposite_margins_in_every_tail a before
  have no : ¬ σ.Satisfies exactNegative.closeNonStrictAtoms u := by
    change ¬ 0 ≤ -(wiggle u.val) ^ 2
    have square := sq_pos_of_pos positive
    linarith
  exact no ((stable t u after after').mp yes)

/-- The signal is a genuine full direct-start continuous SYSTEM trajectory;
the failure above is not caused by an unobserved or discontinuous suffix. -/
def H : STLTableau.HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 0}
  invariant := Set.univ
  flow := fun s t v => ∀ x, v x = s.2 x + t
  trajectory_closed := STLTableau.HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total x
        dsimp only [Prod.snd] at *
        rw [total x, first x]; push_cast; ring)
    (by intro q v a b r s first second x
        dsimp only [Prod.snd] at *
        rw [second x, first x]; push_cast; ring)
  jump := fun _ _ _ => False

def state (x : ℝ) : H.State := ⟨((), fun _ => x), Set.mem_univ _⟩
def e : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := state 0
  initial_mem := rfl
  start := fun _ => state 0
  finish := fun _ => state 1
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j order
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from order)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ u _ => u.val
  continuousStep := by
    intro i
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro u
    exact ⟨fun _ => (zero_add u.val).symm, Set.mem_univ _⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := by
    intro i t ht
    fin_cases i
    funext x
    norm_num [σ]
    rfl

theorem full_system_witness : e.ReachesHorizon := by
  unfold STLTableau.HybridAutomaton.PrelimExecution.ReachesHorizon e
  norm_num [σ]
theorem direct_system_start : e.initialState = e.start ⟨0, e.nonempty⟩ := rfl
theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

theorem continuous_full_system_shift_failure :
    H.ContinuousFlows ∧ H.IsPrelimTrajectory σ ∧
      (∀ a, Formula.IsSubformula (.atom a) φ → Continuous a.function) ∧
      (∀ a, Formula.IsSubformula (.atom a) φ → a.relation = .ge) ∧
      σ.HasFiniteVariability φ ∧ ¬ σ.HasFiniteVariability (φ.thresholdShift 1) := by
  refine ⟨continuous_flows, ⟨e, full_system_witness⟩, ?_, ?_,
    original_finite_variability, strengthening_not_finite_variability⟩
  · intro a sub
    cases sub
    exact continuous_atom
  · intro a sub
    cases sub
    rfl

run_elab do
  for name in #[``continuous_wiggle, ``continuous_margin, ``continuous_atom,
      ``original_finite_variability, ``opposite_margins_in_every_tail,
      ``strengthening_not_finite_variability, ``normalized_violation_not_finite_variability,
      ``continuous_square_atom, ``square_input_finite_variability,
      ``exact_negative_finite_variability,
      ``closed_negative_not_finite_variability,
      ``full_system_witness, ``direct_system_start, ``continuous_flows,
      ``continuous_full_system_shift_failure] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end FiniteVariabilityShiftChecks
