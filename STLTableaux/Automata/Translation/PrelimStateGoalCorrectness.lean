import STLTableaux.Automata.Translation.PrelimStateGoalForward
import STLTableaux.Automata.Translation.PrelimStateGoalReverse
import STLTableaux.Automata.Recognition.PrelimGoalVisits

/-! Translation correctness for the formulation with horizon certificates.
The forward direction uses right continuity of atomic predicates, which
follows from well-behavedness of a full system execution. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => withEmptyContinuation (Clock := Clock) X root

/-- Construct an induced partition and a recognizing run from a visited goal
state, including a singleton goal or a horizon certificate. -/
theorem empty_prelim_partition_of_goal_visit {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).prelimAutomaton h τ).PrelimExecution σ)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    (s : ((U).prelimAutomaton h τ).State) (goal : s ∈ (U).prelimGoal h τ)
    (visit : e.VisitsState s) :
    ∃ P : IntervalPartition ρ.domain,
      (U).PrelimGoalInduced h τ e hh ρ P ∧
      (U).recognizes JudgementTableau.labels_finite ρ P := by
  rcases (U).prelim_goal_visit_cases h τ (emptyContinuation_final_successor X root)
    e hh s goal visit with ⟨i, ordinary⟩ | ⟨atEnd, cert⟩
  · exact empty_prelim_partition_of_ordinaryCut X root h e hh ρ proj i
      (e.increasing Fin.castSucc_lt_succ) le_rfl ordinary
  · exact empty_prelim_partition_of_horizonGoal X root h e hh ρ proj atEnd cert

/-- Translation correctness for the tableau with empty continuation and
horizon certificates. Every induced partition is recognized, and a visited
goal supplies an induced partition. -/
theorem prelim_stateGoal_correctness (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (ρ : FiniteSignal Var) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    (SignalAtomRightContinuous ρ root.val → ∀ P : IntervalPartition ρ.domain,
      (U).recognizes JudgementTableau.labels_finite ρ P →
      ∃ aug, (U).TypedProjectsTo aug ρ ∧
        ((U).prelimAutomaton h ρ.horizon).PrelimReachesState aug
          ((U).prelimGoal h ρ.horizon)) ∧
    (∀ (aug : FiniteSignal (U).TypedVar)
      (e : ((U).prelimAutomaton h ρ.horizon).PrelimExecution aug)
      (proj : (U).TypedProjectsTo aug ρ) (P : IntervalPartition ρ.domain),
      (U).PrelimGoalInduced h ρ.horizon e proj.1 ρ P →
      (U).recognizes JudgementTableau.labels_finite ρ P) ∧
    (∀ (aug : FiniteSignal (U).TypedVar), (U).TypedProjectsTo aug ρ →
      ((U).prelimAutomaton h ρ.horizon).PrelimReachesState aug
        ((U).prelimGoal h ρ.horizon) →
      ∃ P : IntervalPartition ρ.domain,
        (U).recognizes JudgementTableau.labels_finite ρ P) := by
  intro h
  refine ⟨?_, ?_, ?_⟩
  · intro hw P recognized
    exact empty_prelim_stateGoal_forward X root h ρ hw nonStrict P recognized
  · intro aug e proj P induced
    exact empty_prelim_stateGoal_reverse X root h e proj.1 ρ proj P induced
  · intro aug proj reached
    obtain ⟨e, s, goal, visit⟩ := reached
    obtain ⟨P, _, recognized⟩ :=
      empty_prelim_partition_of_goal_visit X root h e proj.1 ρ proj s goal visit
    exact ⟨P, recognized⟩

/-- Derive the atomic right-continuity premise from a full system execution
and apply the forward translation with horizon certificates. -/
theorem prelim_stateGoal_forward_of_initialFlow {Mode Label : Type*}
    {H : HybridAutomaton Mode Label Var} (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (ρ : FiniteSignal Var) (e : H.PrelimExecution ρ) (full : e.ReachesHorizon)
    (_direct : e.initialState = e.start ⟨0, e.nonempty⟩) (hw : e.WellBehaved root.val)
    (P : IntervalPartition ρ.domain)
    (recognized : (U).recognizes JudgementTableau.labels_finite ρ P) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ∃ aug, (U).TypedProjectsTo aug ρ ∧
      ((U).prelimAutomaton h ρ.horizon).PrelimReachesState aug
        ((U).prelimGoal h ρ.horizon) := by
  intro h
  exact empty_prelim_stateGoal_forward X root h ρ
    (hw.signalAtomRightContinuous full) nonStrict P recognized

/-- Derive well-behavedness from the continuity of system flows and atomic
functions and apply the forward translation with horizon certificates. -/
theorem prelim_stateGoal_forward_of_continuousInitialFlow {Mode Label : Type*}
    {H : HybridAutomaton Mode Label Var} (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root.val, x ∈ X)
    (nonStrict : ∀ a, Formula.IsSubformula (.atom a) root.val → a.relation = .ge)
    (ρ : FiniteSignal Var) (e : H.PrelimExecution ρ) (full : e.ReachesHorizon)
    (direct : e.initialState = e.start ⟨0, e.nonempty⟩) (flows : H.ContinuousFlows)
    (functions : ∀ a, Formula.IsSubformula (.atom a) root.val → Continuous a.function)
    (P : IntervalPartition ρ.domain)
    (recognized : (U).recognizes JudgementTableau.labels_finite ρ P) :
    let h := withEmptyContinuation_ready (Clock := Clock) X root
      (finiteRootTableau_translationReady X hX root.val vars)
    ∃ aug, (U).TypedProjectsTo aug ρ ∧
      ((U).prelimAutomaton h ρ.horizon).PrelimReachesState aug
        ((U).prelimGoal h ρ.horizon) :=
  prelim_stateGoal_forward_of_initialFlow X root hX vars nonStrict ρ e full direct
    (e.wellBehaved_of_continuousFlows root.val flows functions) P recognized

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``empty_prelim_partition_of_goal_visit,
      ``prelim_stateGoal_correctness, ``prelim_stateGoal_forward_of_initialFlow,
      ``prelim_stateGoal_forward_of_continuousInitialFlow] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.Section4.Finiteness
