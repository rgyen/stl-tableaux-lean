import STLTableaux.Automata.Execution.PrelimExecution
import STLTableaux.Automata.Execution.BoundedZeroTimeExtension
import STLTableaux.Automata.Recognition.ProjectedFlowWord
import STLTableaux.Automata.Execution.FlowSignalContinuity

/-! A raw initial jump does not own an observation in the general trajectory.
The following flow supplies time zero and every later time in its interval. -/
namespace InitialJumpSynchronizationChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton Bool Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(false, (), true)}
  initial := {s | s.1 = false ∧ s.2 () = 0}
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ s' => s'.2 () = 1

def before : H.State := ⟨(false, fun _ => 0), Set.mem_univ _⟩
def after : H.State := ⟨(true, fun _ => 1), Set.mem_univ _⟩
theorem jump : H.DiscreteStep before after := ⟨⟨(false, (), true), rfl⟩, rfl, rfl, rfl⟩

noncomputable def σ : FiniteSignal Unit :=
  ⟨1, by norm_num, fun _ _ => 1⟩
noncomputable def preJumpObserved : FiniteSignal Unit :=
  ⟨1, by norm_num, fun t _ => if t.val = 0 then 0 else 1⟩

noncomputable def execution : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := before
  initial_mem := ⟨rfl, rfl⟩
  start := fun _ => after
  finish := fun _ => after
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 1
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  initialSteps := .single jump
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := fun _ _ _ => rfl

theorem full_system_trajectory : H.IsPrelimTrajectory σ := by
  refine ⟨execution, ?_⟩
  unfold PrelimExecution.ReachesHorizon
  dsimp only [execution]
  norm_num [σ]

theorem pre_jump_observation_rejected : ¬ H.IsPrelimPrefix preJumpObserved := by
  rintro ⟨e⟩
  let i : Fin e.count := ⟨0, e.nonempty⟩
  have zero : e.boundary i.castSucc = 0 := e.first_zero
  have pos := e.increasing (show i.castSucc < i.succ by simp)
  rw [zero] at pos
  obtain ⟨u, hu, upper⟩ := exists_between pos
  let t : preJumpObserved.Time := ⟨u, hu.le, upper.trans_le
    ((e.increasing.monotone (Fin.le_last _)).trans e.last_le_horizon)⟩
  have start : (e.start i).val.2 () = 0 := by
    simpa [preJumpObserved, i] using congrFun e.signal_at_zero.symm ()
  have inside : e.boundary i.castSucc ≤ t.val ∧ t.val < e.boundary i.succ :=
    ⟨zero.symm ▸ hu.le, upper⟩
  have observed := e.signal_eq i t inside
  have eq := (congrFun observed ()).trans
    ((congrFun (((e.continuousStep i).2.2.2 _).1) ()).trans start)
  simp [preJumpObserved, t, hu.ne'] at eq

def atom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0 - 1, .ge⟩

theorem atom_true_at_zero :
    σ.Satisfies (.atom atom) ⟨0, le_rfl, σ.horizon_pos⟩ := by
  change (1 : ℝ) - 1 ≥ 0
  norm_num

/-- All flows are constant even though the initial jump changes x. -/
theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  have same : γ = fun _ => γ ⟨0, by simp⟩ := by
    funext u
    exact (evolves u).1
  rw [same]
  exact continuous_const

theorem continuous_atomic_function : Continuous atom.function :=
  (continuous_apply (0 : Fin 1)).sub continuous_const

/-- The sufficient-condition lemma accepts the actual jump-before-flow
execution, without imposing continuity across that jump. -/
theorem execution_wellBehaved : execution.WellBehaved (.atom atom) := by
  apply execution.wellBehaved_of_continuousFlows (.atom atom) continuous_flows
  intro a sub
  cases sub
  exact continuous_atomic_function

theorem trajectory_has_wellBehaved_execution :
    ∃ e : H.PrelimExecution σ, e.ReachesHorizon ∧ e.WellBehaved (.atom atom) := by
  apply IsPrelimTrajectory.exists_wellBehaved_execution H full_system_trajectory
    (.atom atom) continuous_flows
  intro a sub
  cases sub
  exact continuous_atomic_function

/-- The initial reset does not obstruct right continuity at time zero. -/
theorem signalAtomRightContinuous : SignalAtomRightContinuous σ (.atom atom) := by
  apply execution_wellBehaved.signalAtomRightContinuous
  unfold PrelimExecution.ReachesHorizon
  dsimp only [execution]
  norm_num [σ]

noncomputable def zeroSignal : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩
noncomputable def noJumpExecution : H.PrelimExecution zeroSignal where
  count := 1
  nonempty := by decide
  initialState := before
  initial_mem := ⟨rfl, rfl⟩
  start := fun _ => before
  finish := fun _ => before
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [zeroSignal]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := fun _ _ _ => rfl

theorem no_initial_jump_allowed : H.IsPrelimTrajectory zeroSignal :=
  ⟨noJumpExecution, by
    unfold PrelimExecution.ReachesHorizon
    dsimp only [noJumpExecution]
    norm_num [zeroSignal]⟩

theorem bounded_full_system_trajectory (n : ℕ) :
    (H.boundedZeroTimeExtension n).IsPrelimTrajectory σ :=
  (H.boundedZeroTimeExtension_trajectory_iff n σ).mpr full_system_trajectory

theorem initial_jump_in_init (n : ℕ) :
    ∃ w : (H.withInitialJumpClosure.boundedZeroTimeExtension n).PrelimExecution σ,
      w.ReachesHorizon ∧ w.initialState = after ∧ w.initialState = w.start ⟨0, w.nonempty⟩ := by
  let w := (execution.startWithFlow H).inZeroTimeExtension H.withInitialJumpClosure n
  refine ⟨w, ?_, rfl, rfl⟩
  unfold PrelimExecution.ReachesHorizon
  change ((1 : ℕ) : ℝ) = 1
  norm_num

run_elab do
  for name in #[``full_system_trajectory, ``pre_jump_observation_rejected,
      ``atom_true_at_zero, ``no_initial_jump_allowed, ``initial_jump_in_init,
      ``bounded_full_system_trajectory, ``continuous_flows, ``continuous_atomic_function,
      ``execution_wellBehaved, ``trajectory_has_wellBehaved_execution,
      ``signalAtomRightContinuous] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

/- This example assembles the observed flows into a `FlowWord`. -/
namespace Packing
open STLTableau.Section4
def T : Tableau Unit Unit Bool where
  realVariables := Set.univ
  clocks := ∅
  states := Set.univ
  edges := ∅
  initial := ∅
  final := ∅
  label := fun _ => ∅
  label_atomic := fun _ _ h => h.elim

def A : HybridAutomaton T.states (EdgeLabel Unit) T.TypedVar where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := Set.univ
  initial := Set.univ
  invariant := Set.univ
  flow := fun _ _ v => v = fun _ => 0
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (fun _ _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h)
  jump := fun _ _ _ => True

noncomputable def before : A.State :=
  ⟨(⟨false, Set.mem_univ _⟩, fun x => if x = T.bit then 1 else 0), Set.mem_univ _⟩
def after : A.State := ⟨(⟨true, Set.mem_univ _⟩, fun _ => 0), Set.mem_univ _⟩
theorem jump : A.DiscreteStep before after :=
  ⟨⟨(before.val.1, ⟨∅, Set.finite_empty, ClockResetSet.empty⟩, after.val.1), Set.mem_univ _⟩,
    rfl, rfl, trivial⟩

def piece : T.FlowPiece A zeroSignal where
  left := 0
  duration := 1
  positive := by norm_num
  start := after
  finish := after
  curve := fun _ _ => 0
  flow := ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  obs := fun _ _ _ _ _ => rfl

theorem packed_initial_bit :
    ∃ aug, T.TypedProjectsTo aug zeroSignal ∧
      ∃ e : A.PrelimExecution aug,
        e.initialState = before ∧ e.start ⟨0, e.nonempty⟩ = after ∧
        aug.value ⟨0, le_rfl, aug.horizon_pos⟩ T.bit = 0 ∧
        (∀ t : aug.Time, aug.value t T.bit = 0) := by
  have word : T.FlowWord A zeroSignal after 0 after 1 := by
    simpa [piece] using (Tableau.FlowWord.last piece)
  obtain ⟨aug, proj, e, initial, first, final, stop⟩ :=
    word.prelim_execution_with_entries before (Set.mem_univ _) (.single jump)
      (by norm_num [zeroSignal])
  refine ⟨aug, proj, e, initial, first, ?_, ?_⟩
  · rw [e.signal_at_zero, first]
    rfl
  · intro t
    have bounds : t.val ∈ Set.Ico (e.boundary 0) (e.boundary ⟨e.count, by omega⟩) := by
      constructor
      · have zero : e.boundary 0 = 0 := e.first_zero
        rw [zero]
        exact t.property.1
      · rw [stop]
        have horizon := proj.1
        change aug.horizon = 1 at horizon
        exact t.property.2.trans_eq horizon
    obtain ⟨i, lo, hi⟩ := IntervalPartition.exists_boundary_piece e.boundary bounds
    rw [e.signal_eq i t ⟨lo, hi⟩]
    exact congrFun (((e.continuousStep i).2.2.2 _).1) T.bit

run_elab do
  for ax in ← Lean.collectAxioms ``packed_initial_bit do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"
end Packing
end InitialJumpSynchronizationChecks
