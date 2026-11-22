import STLTableaux.ModelChecking.Reduction.ModelCheckingForward
import STLTableaux.Semantics.Partitions.BoundaryPartition

namespace ModelCheckingForwardChecks
open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

def atom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom atom, .atom atom⟩
def X : Set Unit := Set.univ
noncomputable abbrev U := withEmptyContinuation (Clock := Nat) X root

def system : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun _ _ _ => True
  trajectory_closed := HybridFlow.Closed.unconstrained _
  jump := fun _ _ _ => False

theorem ready : U.TranslationReady :=
  withEmptyContinuation_ready X root
    (finiteRootTableau_translationReady X (Set.toFinite _) root.val (fun _ _ => trivial))

/-- The clocks advance at rate one and the real-valued system variable is negative. -/
noncomputable def negative : FiniteSignal U.CompositionVar :=
  ⟨2, by norm_num, fun t x => match x.val with
    | .inl _ => -1
    | .inr (.inl _) => t.val
    | .inr (.inr b) => if b then 1 else t.val⟩

def systemState : system.State := ⟨((), fun _ => -1), Set.mem_univ _⟩

/-- The negative real signal is a genuine system trajectory, so rejection
is not obtained by assuming that the system has no trajectories. -/
noncomputable def negativeSystemExecution :
    system.PrelimExecution (U.systemSignal negative) where
  count := 1
  nonempty := by decide
  initialState := systemState
  initial_mem := Set.mem_univ _
  start := fun _ => systemState
  finish := fun _ => systemState
  boundary := fun i => 2 * i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [negative, Tableau.systemSignal, FiniteSignal.reindex]
  duration := fun _ => 2
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => -1
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; exact False.elim (by omega)
  signal_eq := fun _ _ _ => rfl

theorem negative_system_trajectory : system.IsPrelimTrajectory (U.systemSignal negative) :=
  ⟨negativeSystemExecution, by
    unfold HybridAutomaton.PrelimExecution.ReachesHorizon
    dsimp only [negativeSystemExecution]
    norm_num [Tableau.systemSignal, FiniteSignal.reindex, negative]⟩

theorem negative_not_reached :
    ¬ (U.systemTableauAutomaton system ready negative.horizon).PrelimReachesState negative
      (U.systemTableauGoal system ready negative.horizon) := by
  intro reached
  have formula := (finite_systemTableau_goal_formula X root system
    (Set.toFinite _) (fun _ _ => trivial) negative reached).2
  change (-1 : ℝ) ≥ 0 at formula
  norm_num at formula

noncomputable def positive : FiniteSignal Unit := ⟨2, by norm_num, fun _ _ => 1⟩

noncomputable def positivePartition : IntervalPartition positive.domain :=
  let P := IntervalPartition.ofBoundaries (![(0 : ℝ), 2]) (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *)
  { P with covers := P.covers.trans (by rfl) }

theorem positive_stable : positive.StablePartition root.val positivePartition := by
  intro i φ subformula
  change Formula.IsSubformula φ (.atom atom) at subformula
  cases subformula
  intro u v hu hv
  rfl

theorem positive_recognized : U.recognizes JudgementTableau.labels_finite
    positive positivePartition := by
  apply (emptyContinuation_recognizes_iff X root positive positivePartition).2
  apply (inputTableau_recognizes_iff X root positive positivePartition positive_stable).2
  change (1 : ℝ) ≥ 0
  norm_num

/-- The soundness call itself has no stable/FV premise. -/
theorem positive_from_recognition : positive.Satisfies root.val
    ⟨0, le_rfl, positive.horizon_pos⟩ :=
  formula_of_emptyContinuation_recognizes X root positive positivePartition positive_recognized

/-- Project a full product execution to a system trajectory satisfying the
tableau input. -/
theorem negative_no_full_goal :
    ¬ ∃ e : (U.systemTableauAutomaton system ready negative.horizon).PrelimExecution negative,
      e.ReachesHorizon ∧ ∃ s ∈ U.systemTableauGoal system ready negative.horizon,
        e.VisitsState s := by
  rintro ⟨e, full, s, goal, visit⟩
  have result := finite_systemTableau_full_goal_formula X root system
    (Set.toFinite _) (fun _ _ => trivial) negative e full ⟨s, goal, visit⟩
  have formula := result.2
  change (-1 : ℝ) ≥ 0 at formula
  norm_num at formula

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``negativeSystemExecution, ``negative_system_trajectory,
      ``negative_not_reached, ``positive_stable,
      ``positive_recognized, ``positive_from_recognition,
      ``finite_systemTableau_goal_formula, ``finite_systemTableau_goal_exists,
      ``negative_no_full_goal, ``finite_systemTableau_full_goal_formula,
      ``finite_systemTableau_full_goal_exists] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end ModelCheckingForwardChecks
