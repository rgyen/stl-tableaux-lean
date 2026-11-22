import STLTableaux.ModelChecking.Reduction.ModelCheckingForward
import STLTableaux.Semantics.Partitions.BoundaryPartition
import STLTableaux.ModelChecking.Preprocessing.NormalizedInput
import STLTableaux.Automata.Execution.BoundedZeroTimeExtension
import Mathlib.Topology.Algebra.Polynomial

/-! The ramp is realizable on a short system prefix. The system invariant
rules it out over the full horizon. The zero signal yields a full system
trajectory and reaches a goal before the horizon. -/
namespace SynchronizationPrefixAudit
open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 0}
  invariant := {s | s.2 () = 0}
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ _ => False

noncomputable def I : BoundedTimeInterval := ⟨1, 3 / 2, by norm_num, by norm_num⟩
def atom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0 - 1, .ge⟩
noncomputable def root : Formula.NormalizedInput Unit :=
  ⟨.eventually I (.atom atom), .eventually I (.atom atom)⟩
def X : Set Unit := Set.univ
noncomputable abbrev U := withEmptyContinuation (Clock := Nat) X root

theorem ready : U.TranslationReady :=
  withEmptyContinuation_ready X root
    (finiteRootTableau_translationReady X (Set.toFinite _) root.val (fun _ _ => trivial))

noncomputable def σ : FiniteSignal Unit :=
  ⟨2, by norm_num, fun t _ => max 0 (2 * t.val - 1)⟩

def zero : H.State := ⟨((), fun _ => 0), rfl⟩

/-- A genuine positive prefix of the same horizon-2 signal. -/
noncomputable def shortExecution : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := zero
  initial_mem := rfl
  start := fun _ => zero
  finish := fun _ => zero
  boundary := fun i => i.val / 4
  first_zero := by norm_num
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1 / 4
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; exact False.elim (by omega)
  signal_eq := by
    intro i t ht
    fin_cases i
    funext x
    change max 0 (2 * t.val - 1) = 0
    apply max_eq_left
    have bound : t.val < (1 : ℝ) / 4 := by simpa using ht.2
    linarith

theorem system_prefix : H.IsPrelimPrefix σ := ⟨shortExecution⟩

/-- At time 1, the ramp violates the system invariant. -/
theorem not_system_trajectory : ¬ H.IsPrelimTrajectory σ := by
  intro trajectory
  let t : σ.Time := ⟨1, by norm_num [σ]⟩
  obtain ⟨q, invariant⟩ := trajectory.invariant_at t
  change max 0 (2 * (1 : ℝ) - 1) = 0 at invariant
  norm_num at invariant

theorem prefix_not_trajectory : H.IsPrelimPrefix σ ∧ ¬ H.IsPrelimTrajectory σ :=
  ⟨system_prefix, not_system_trajectory⟩

theorem not_extended_system_trajectory (n : ℕ) :
    ¬ (H.boundedZeroTimeExtension n).IsPrelimTrajectory σ := by
  intro trajectory
  exact not_system_trajectory ((H.boundedZeroTimeExtension_trajectory_iff n σ).mp trajectory)

noncomputable def zeroSignal : FiniteSignal Unit := ⟨2, by norm_num, fun _ _ => 0⟩

noncomputable def zeroExecution (r : NNReal) (positive : 0 < (r : ℝ))
    (within : (r : ℝ) ≤ 2) : H.PrelimExecution zeroSignal where
  count := 1
  nonempty := by decide
  initialState := zero
  initial_mem := rfl
  start := fun _ => zero
  finish := fun _ => zero
  boundary := fun i => if i.val = 0 then 0 else r
  first_zero := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := within
  duration := fun _ => r
  duration_eq := by intro i; fin_cases i; simp
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; exact False.elim (by omega)
  signal_eq := fun _ _ _ => rfl

/-- Full system membership and early goal checking coexist. The goal
witness stops at 1/4, while the actual system signal is realized through 2. -/
theorem full_signal_with_early_goal :
    H.IsPrelimTrajectory zeroSignal ∧ H.PrelimReachesState zeroSignal {zero} := by
  refine ⟨⟨zeroExecution 2 (by norm_num) le_rfl, rfl⟩, ?_⟩
  let early := zeroExecution (1 / 4) (by norm_num) (by norm_num)
  exact ⟨early, zero, rfl, early.visits_finalState⟩

theorem all_flows_continuous {a b : H.State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → Unit → ℝ} (step : H.ContinuousStep a b r γ) :
    Continuous γ := by
  have constant : γ = fun _ => a.val.2 := by
    funext t
    exact (step.2.2.2 t).1
  rw [constant]
  exact continuous_const

theorem flows_add : H.FlowAdd := by
  intro q v v₁ v₂ r s first second
  exact second.trans first

theorem no_discrete_step (a b : H.State) : ¬ H.DiscreteStep a b := by
  rintro ⟨e, _⟩
  exact e.property

theorem atomic_function_continuous : Continuous atom.function := by
  change Continuous (fun v : Fin 1 → ℝ => v 0 - 1)
  fun_prop

theorem atom_subformula {a : AtomicProposition Unit}
    (sub : Formula.IsSubformula (.atom a) root.val) : a = atom := by
  change Formula.IsSubformula (.atom a) (.until I .truth (.atom atom)) at sub
  cases sub with
  | until_left sub => cases sub
  | until_right sub => cases sub; rfl

theorem signal_wellBehaved : SignalAtomRightContinuous σ root.val := by
  intro a sub t
  have same := atom_subformula sub
  subst a
  have continuous : Continuous (atomValue σ atom) := by
    change Continuous (fun t : σ.Time => max 0 (2 * t.val - 1) - 1)
    fun_prop
  exact continuous.continuousWithinAt

theorem atom_holds_iff (t : σ.Time) : σ.Satisfies (.atom atom) t ↔ 1 ≤ t.val := by
  change max 0 (2 * t.val - 1) - 1 ≥ 0 ↔ 1 ≤ t.val
  constructor
  · intro h
    by_contra hn
    have lt : max 0 (2 * t.val - 1) < 1 := max_lt (by norm_num) (by linarith)
    linarith
  · intro h
    have le := le_max_right (0 : ℝ) (2 * t.val - 1)
    linarith

theorem eventually_holds_iff (t : σ.Time) : σ.Satisfies root.val t ↔ t.val < 1 := by
  rw [show root.val = Formula.eventually I (.atom atom) from rfl,
    FiniteSignal.satisfies_eventually_iff]
  constructor
  · rintro ⟨u, delay, _⟩
    change 1 ≤ u.val - t.val ∧ u.val - t.val ≤ 3 / 2 at delay
    have bound : u.val < 2 := u.property.2
    linarith [delay.1]
  · intro h
    let u : σ.Time := ⟨t.val + 1, by
      change 0 ≤ t.val + 1 ∧ t.val + 1 < 2
      constructor <;> linarith [t.property.1]⟩
    refine ⟨u, ?_, (atom_holds_iff u).mpr ?_⟩
    · change 1 ≤ t.val + 1 - t.val ∧ t.val + 1 - t.val ≤ 3 / 2
      constructor <;> linarith
    · dsimp [u]
      linarith [t.property.1]

theorem root_true : σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ :=
  (eventually_holds_iff _).mpr (by norm_num)

noncomputable def P : IntervalPartition σ.domain :=
  let Q := IntervalPartition.ofBoundaries (![(0 : ℝ), 1, 2]) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *)
  { Q with covers := Q.covers.trans (by rfl) }

theorem subformula_cases {φ : Formula Unit} (sub : Formula.IsSubformula φ root.val) :
    φ = root.val ∨ φ = .truth ∨ φ = .atom atom := by
  change Formula.IsSubformula φ (.until I .truth (.atom atom)) at sub
  cases sub with
  | refl => exact Or.inl rfl
  | until_left sub => cases sub; exact Or.inr (Or.inl rfl)
  | until_right sub => cases sub; exact Or.inr (Or.inr rfl)

private theorem right_open {l r x : ℝ} (h : x ∈ (⟨l, r, ●, ○⟩ : MarkedInterval)) :
    x < r := h.2.elim id (fun h => h.2.elim)

theorem stable : σ.StablePartition root.val P := by
  intro i φ sub u v hu hv
  rcases subformula_cases sub with rfl | rfl | rfl
  · rw [eventually_holds_iff, eventually_holds_iff]
    fin_cases i
    · simp only [P, IntervalPartition.ofBoundaries] at hu hv
      exact iff_of_true (right_open hu) (right_open hv)
    · simp only [P, IntervalPartition.ofBoundaries] at hu hv
      exact iff_of_false (not_lt_of_ge (MarkedInterval.left_le_of_mem hu))
        (not_lt_of_ge (MarkedInterval.left_le_of_mem hv))
  · exact Iff.rfl
  · rw [atom_holds_iff, atom_holds_iff]
    fin_cases i
    · simp only [P, IntervalPartition.ofBoundaries] at hu hv
      exact iff_of_false (not_le_of_gt (right_open hu)) (not_le_of_gt (right_open hv))
    · simp only [P, IntervalPartition.ofBoundaries] at hu hv
      exact iff_of_true (MarkedInterval.left_le_of_mem hu) (MarkedInterval.left_le_of_mem hv)

theorem finite_variability : σ.HasFiniteVariability root.val := ⟨P, stable⟩

/-- Both individual components really have the required witnesses. -/
theorem monitor_goal_exists :
    ∃ aug, U.TypedProjectsTo aug σ ∧
      (U.prelimAutomaton ready σ.horizon).PrelimReachesState aug
        (U.prelimGoal ready σ.horizon) := by
  have recognized : U.recognizes JudgementTableau.labels_finite σ P :=
    (emptyContinuation_recognizes_iff X root σ P).mpr
      ((inputTableau_recognizes_iff X root σ P stable).mpr root_true)
  apply empty_prelim_stateGoal_forward X root ready σ signal_wellBehaved _ P recognized
  intro a sub
  exact atom_subformula sub ▸ rfl

/-- Set the real-valued system variables to zero and retain the horizon,
clocks, and endpoint marker. -/
noncomputable def zeroReals (aug : FiniteSignal U.CompositionVar) :
    FiniteSignal U.CompositionVar :=
  { aug with value := fun t x => match x.val with
    | .inl _ => 0
    | .inr _ => aug.value t x }

theorem no_composed_goal_for {Mode Label : Type*} (K : HybridAutomaton Mode Label Unit)
    (fixed : ∀ s ∈ K.invariant, s.2 () = 0) (aug : FiniteSignal U.CompositionVar) :
    ¬ (U.systemTableauAutomaton K ready aug.horizon).PrelimReachesState aug
      (U.systemTableauGoal K ready aug.horizon) := by
  rintro ⟨e, s, goal, visit⟩
  let e' : (U.systemTableauAutomaton K ready aug.horizon).PrelimExecution (zeroReals aug) :=
    { e with
      signal_eq := by
        intro i t ht
        let z : Set.Icc (0 : ℝ) (e.duration i) :=
          ⟨t.val - e.boundary ⟨i.val, by omega⟩, by
          constructor
          · linarith [ht.1]
          · linarith [ht.2, e.duration_eq i]⟩
        funext x
        have value := congrFun (e.signal_eq i t ht) x
        have realZero : e.curve i z (U.systemCoordinate ()) = 0 :=
          fixed _ ((e.continuousStep i).2.2.2 z).2.1
        change (match x.val with
          | .inl _ => 0
          | .inr _ => aug.value t x) = e.curve i z x
        cases name : x.val with
        | inl a =>
          cases a
          have same : x = U.systemCoordinate () := Subtype.ext name
          simpa only [name, same] using realZero.symm
        | inr a => simpa only [name] using value }
  have reached : (U.systemTableauAutomaton K ready (zeroReals aug).horizon).PrelimReachesState
      (zeroReals aug) (U.systemTableauGoal K ready (zeroReals aug).horizon) :=
    ⟨e', s, goal, visit⟩
  have truth := (finite_systemTableau_goal_formula X root K (Set.toFinite _)
    (fun _ _ => trivial) (zeroReals aug) reached).2
  obtain ⟨t, _, atomTrue⟩ :=
    (FiniteSignal.satisfies_eventually_iff _ I (.atom atom) _).mp truth
  change (0 : ℝ) - 1 ≥ 0 at atomTrue
  norm_num at atomTrue

theorem no_composed_goal (aug : FiniteSignal U.CompositionVar) :
    ¬ (U.systemTableauAutomaton H ready aug.horizon).PrelimReachesState aug
      (U.systemTableauGoal H ready aug.horizon) :=
  no_composed_goal_for H (fun _ fixed => fixed) aug

/-- Bounded zero-time extension cannot repair an unconstrained signal suffix.
It retains exactly the same system invariant and continuous dynamics. -/
theorem no_extended_composed_goal (n : ℕ) (aug : FiniteSignal U.CompositionVar) :
    ¬ HybridAutomaton.PrelimReachesState
      (U.systemTableauAutomaton (H.boundedZeroTimeExtension n) ready aug.horizon) aug
      (U.systemTableauGoal (H.boundedZeroTimeExtension n) ready aug.horizon) :=
  no_composed_goal_for (H.boundedZeroTimeExtension n) (fun _ fixed => fixed) aug

/-- A signal with finite variability and right-continuous atoms can be
observed on a system prefix and reach a goal in the translated automaton
without a corresponding goal in the composed automaton. -/
theorem prefix_synchronization_obstruction :
    H.IsPrelimPrefix σ ∧ SignalAtomRightContinuous σ root.val ∧ σ.HasFiniteVariability root.val ∧
      σ.Satisfies root.val ⟨0, le_rfl, σ.horizon_pos⟩ ∧
      (∃ aug, U.TypedProjectsTo aug σ ∧
        (U.prelimAutomaton ready σ.horizon).PrelimReachesState aug
          (U.prelimGoal ready σ.horizon)) ∧
      ¬ (∃ aug : FiniteSignal U.CompositionVar,
        U.systemSignal aug = σ ∧
        (U.systemTableauAutomaton H ready aug.horizon).PrelimReachesState aug
          (U.systemTableauGoal H ready aug.horizon)) := by
  refine ⟨system_prefix, signal_wellBehaved, finite_variability, root_true,
    monitor_goal_exists, ?_⟩
  rintro ⟨aug, _, goal⟩
  exact no_composed_goal aug goal

noncomputable def specification : Formula Unit := .neg root.val

theorem negated_specification_normalizes :
    (Formula.neg specification).normalizeForTableau = root.val := rfl

theorem specification_stable : σ.StablePartition specification P := by
  intro i ψ sub
  change Formula.IsSubformula ψ (.neg root.val) at sub
  cases sub with
  | refl =>
    intro u v hu hv
    exact not_congr (stable i root.val (.refl _) u v hu hv)
  | neg sub => exact stable i ψ sub

theorem specification_finite_variability : σ.HasFiniteVariability specification :=
  ⟨P, specification_stable⟩

theorem specification_violated : ¬ σ.Satisfies specification ⟨0, le_rfl, σ.horizon_pos⟩ :=
  fun assumption => assumption root_true

theorem specification_atoms_continuous (a : AtomicProposition Unit)
    (sub : Formula.IsSubformula (.atom a) specification) : Continuous a.function := by
  change Formula.IsSubformula (.atom a) (.neg root.val) at sub
  cases sub with
  | neg sub =>
    have same := atom_subformula sub
    subst a
    exact atomic_function_continuous

/-- Replacing full trajectory membership by PREFIX membership would make
the reverse implication false. This is a regression, not a manuscript counterexample. -/
theorem prefix_reverse_obstruction :
    (∀ aug : FiniteSignal U.CompositionVar,
      ¬ (U.systemTableauAutomaton H ready aug.horizon).PrelimReachesState aug
        (U.systemTableauGoal H ready aug.horizon)) ∧
      H.IsPrelimPrefix σ ∧ σ.HasFiniteVariability specification ∧
      ¬ σ.Satisfies specification ⟨0, le_rfl, σ.horizon_pos⟩ ∧
      (Formula.neg specification).normalizeForTableau = root.val :=
  ⟨no_composed_goal, system_prefix, specification_finite_variability,
    specification_violated, negated_specification_normalizes⟩

theorem bounded_prefix_reverse_obstruction (n : ℕ) :
    (∀ aug : FiniteSignal U.CompositionVar,
      ¬ HybridAutomaton.PrelimReachesState
        (U.systemTableauAutomaton (H.boundedZeroTimeExtension n) ready aug.horizon) aug
        (U.systemTableauGoal (H.boundedZeroTimeExtension n) ready aug.horizon)) ∧
      (H.boundedZeroTimeExtension n).IsPrelimPrefix σ ∧
      σ.HasFiniteVariability specification ∧
      ¬ σ.Satisfies specification ⟨0, le_rfl, σ.horizon_pos⟩ :=
  ⟨no_extended_composed_goal n, ⟨shortExecution.inZeroTimeExtension H n⟩,
    specification_finite_variability, specification_violated⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``system_prefix, ``not_system_trajectory, ``prefix_not_trajectory,
      ``not_extended_system_trajectory, ``full_signal_with_early_goal,
      ``all_flows_continuous, ``flows_add,
      ``atomic_function_continuous, ``signal_wellBehaved, ``root_true,
      ``finite_variability, ``monitor_goal_exists, ``no_composed_goal_for, ``no_composed_goal,
      ``no_extended_composed_goal,
      ``prefix_synchronization_obstruction, ``negated_specification_normalizes,
      ``specification_finite_variability, ``specification_atoms_continuous,
      ``specification_violated, ``prefix_reverse_obstruction,
      ``bounded_prefix_reverse_obstruction] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end SynchronizationPrefixAudit
