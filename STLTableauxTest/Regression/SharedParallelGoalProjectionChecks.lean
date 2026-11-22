import STLTableaux.Automata.Composition.SharedParallelGoalProjection

namespace SharedParallelGoalProjectionChecks
open STLTableau STLTableau.HybridAutomaton

def constant (M : Type*) [Finite M] (edges : Bool) : HybridAutomaton M Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := if edges then Set.univ else ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ s s' => s'.2 = s.2

theorem constant_add (M : Type*) [Finite M] (edges : Bool) : (constant M edges).FlowAdd := by
  intro q v v₁ v₂ r s first second
  exact second.trans first

def ι : Unit ↪ Unit := Function.Embedding.refl _

noncomputable def signal {V : Type*} (v : V → ℝ) : FiniteSignal V :=
  ⟨3, by norm_num, fun _ => v⟩

noncomputable def twoFlows {M L V : Type*} (H : HybridAutomaton M L V)
    (s : H.State) (initial : s.val ∈ H.initial)
    (flow : H.ContinuousStep s s 1 (fun _ => s.val.2))
    (jump : Relation.TransGen H.DiscreteStep s s) : H.PrelimExecution (signal s.val.2) where
  count := 2
  nonempty := by decide
  initialState := s
  initial_mem := initial
  start := fun _ => s
  finish := fun _ => s
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i <;> norm_num
  curve := fun _ _ => s.val.2
  continuousStep := fun _ => flow
  initialSteps := .refl
  discreteSteps := fun _ _ => jump
  signal_eq := fun _ _ _ => rfl

local notation "I" => parallelOn (constant Unit true) (constant Unit false) ι ι

def idleState : (I).State :=
  ⟨(((), ()), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

theorem idleStep : (I).DiscreteStep idleState idleState := by
  let old : {e // e ∈ (constant Unit true).edge} := ⟨((), (), ()), Set.mem_univ _⟩
  let e : {e // e ∈ (I).edge} :=
    ⟨(((), ()), (some (), none), ((), ())), by exact ⟨by decide, Set.mem_univ _, rfl⟩⟩
  exact ⟨e, rfl, rfl, ⟨old, rfl, rfl⟩, rfl⟩

noncomputable def idleExecution := twoFlows (I) idleState
  ⟨Set.mem_univ _, Set.mem_univ _⟩
  ⟨rfl, rfl, rfl, fun _ => ⟨⟨rfl, rfl⟩, Set.mem_univ _, Set.mem_univ _⟩⟩
  (.single idleStep)

theorem no_nonempty (a b : (constant Unit false).State) :
    ¬ Relation.TransGen (constant Unit false).DiscreteStep a b := by
  intro steps
  have noStep : ∀ a b, ¬ (constant Unit false).DiscreteStep a b := by
    rintro a b ⟨e, _⟩
    exact e.property
  induction steps with
  | single step => exact noStep _ _ step
  | tail _ step _ => exact noStep _ _ step

/-- Unlike first-flow-prefix projection, idle contraction retains stop=2. -/
theorem idle_goal_same_stop :
    ∃ out : (constant Unit false).PrelimExecution
        ((signal idleState.val.2).reindex (rightVar ι ι)),
      out.count = 1 ∧ out.boundary ⟨out.count, by omega⟩ = 2 ∧
      out.VisitsState
        ((constant Unit true).rightStateOn (constant Unit false) ι ι idleState) := by
  obtain ⟨out, final, time, visits⟩ :=
    idleExecution.rightGoalProjection
  have count : out.count = 1 := by
    by_contra hn
    have hi : 1 < out.count := by have := out.nonempty; omega
    exact no_nonempty _ _ (out.discreteSteps ⟨0, by omega⟩ hi)
  refine ⟨out, count, ?_, ?_⟩
  · simpa [idleExecution, twoFlows] using time
  · exact visits idleExecution.finalState idleExecution.visits_finalState

local notation "C" => parallelOn (constant Unit false) (constant Bool true) ι ι

def cycleState (q : Bool) : (C).State :=
  ⟨(((), q), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

theorem cycleStep (a b : Bool) : (C).DiscreteStep (cycleState a) (cycleState b) := by
  let old : {e // e ∈ (constant Bool true).edge} := ⟨(a, (), b), Set.mem_univ _⟩
  let e : {e // e ∈ (C).edge} :=
    ⟨(((), a), (none, some ()), ((), b)), by
      exact ⟨by change (none, some ()) ≠ ((none : Option Unit), none); decide,
        rfl, Set.mem_univ _⟩⟩
  exact ⟨e, rfl, rfl, rfl, old, rfl, rfl⟩

noncomputable def cycleExecution := twoFlows (C) (cycleState false)
  ⟨Set.mem_univ _, Set.mem_univ _⟩
  ⟨rfl, rfl, rfl, fun _ => ⟨⟨rfl, rfl⟩, Set.mem_univ _, Set.mem_univ _⟩⟩
  ((Relation.TransGen.single (cycleStep false true)).tail (cycleStep true false))

theorem skipped_goal_visit : cycleExecution.VisitsState (cycleState true) :=
  Or.inr (Or.inr ⟨⟨0, by change 0 < 2; decide⟩, by change 0 + 1 < 2; decide,
    .single (cycleStep false true), .single (cycleStep true false)⟩)

theorem initial_skipped_goal_visit : cycleExecution.VisitsState (cycleState true) :=
  Or.inr (Or.inl ⟨.single (cycleStep false true), .single (cycleStep true false)⟩)

/-- A same-endpoint cycle is not contracted away: its skipped goal survives. -/
theorem skipped_goal_preserved :
    ∃ out : (constant Bool true).PrelimExecution
        ((signal (cycleState false).val.2).reindex (rightVar ι ι)),
      out.finalState =
        (constant Unit false).rightStateOn (constant Bool true) ι ι (cycleState false) ∧
      out.boundary ⟨out.count, by omega⟩ = 2 ∧
      out.VisitsState
        ((constant Unit false).rightStateOn (constant Bool true) ι ι (cycleState true)) := by
  obtain ⟨out, final, time, visits⟩ :=
    cycleExecution.rightGoalProjection
  refine ⟨out, final, ?_, visits _ skipped_goal_visit⟩
  simpa [cycleExecution, twoFlows] using time

theorem initial_skipped_goal_preserved :
    (constant Bool true).PrelimReachesState
      ((signal (cycleState false).val.2).reindex (rightVar ι ι))
      {s | s.val.1 = true} := by
  apply (constant Unit false).parallelOn_reachesState_right
    (constant Bool true) ι ι
  exact ⟨cycleExecution, cycleState true, rfl, initial_skipped_goal_visit⟩

theorem interflow_skipped_goal_preserved :
    (constant Bool true).PrelimReachesState
      ((signal (cycleState false).val.2).reindex (rightVar ι ι))
      {s | s.val.1 = true} := by
  apply (constant Unit false).parallelOn_reachesState_right
    (constant Bool true) ι ι
  exact ⟨cycleExecution, cycleState true, rfl, skipped_goal_visit⟩

/-- Full-horizon version of the same example. The goal is visited only
inside the jump block at time 1; the execution continues until time 3. -/
noncomputable def fullCycleExecution : (C).PrelimExecution
    (signal (cycleState false).val.2) where
  count := 2
  nonempty := by decide
  initialState := cycleState false
  initial_mem := ⟨Set.mem_univ _, Set.mem_univ _⟩
  start := fun _ => cycleState false
  finish := fun _ => cycleState false
  boundary := fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else 3
  first_zero := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [signal]
  duration := fun i => if i.val = 0 then 1 else 2
  duration_eq := by intro i; fin_cases i <;> norm_num
  curve := fun _ _ => (cycleState false).val.2
  continuousStep := fun _ =>
    ⟨rfl, rfl, rfl, fun _ => ⟨⟨rfl, rfl⟩, Set.mem_univ _, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := fun _ _ =>
    (Relation.TransGen.single (cycleStep false true)).tail (cycleStep true false)
  signal_eq := fun _ _ _ => rfl

theorem fullCycle_full : fullCycleExecution.ReachesHorizon := by
  unfold PrelimExecution.ReachesHorizon
  dsimp only [fullCycleExecution]
  norm_num [signal]

theorem early_skipped_visit : fullCycleExecution.VisitsState (cycleState true) :=
  Or.inr (Or.inr ⟨⟨0, by decide⟩, by decide,
    .single (cycleStep false true), .single (cycleStep true false)⟩)

theorem full_left_projection :
    ∃ out : (constant Unit false).PrelimExecution
        ((signal (cycleState false).val.2).reindex (leftVar ι ι)),
      out.count = 1 ∧ out.ReachesHorizon := by
  obtain ⟨out, full, _, _⟩ := fullCycleExecution.leftFullProjection fullCycle_full
  refine ⟨out, ?_, full⟩
  by_contra hn
  have hi : 1 < out.count := by have := out.nonempty; omega
  exact no_nonempty _ _ (out.discreteSteps ⟨0, by omega⟩ hi)

theorem full_right_preserves_early_goal :
    ∃ out : (constant Bool true).PrelimExecution
        ((signal (cycleState false).val.2).reindex (rightVar ι ι)),
      out.ReachesHorizon ∧ out.finalState.val.1 = false ∧
      out.VisitsState
        ((constant Unit false).rightStateOn (constant Bool true) ι ι (cycleState true)) := by
  obtain ⟨out, full, final, preserve⟩ := fullCycleExecution.rightFullProjection fullCycle_full
  refine ⟨out, full, ?_, preserve _ early_skipped_visit⟩
  rw [final]
  rfl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``constant_add, ``twoFlows, ``idleStep, ``idleExecution,
      ``no_nonempty, ``idle_goal_same_stop, ``cycleStep, ``cycleExecution,
      ``skipped_goal_visit, ``skipped_goal_preserved, ``initial_skipped_goal_visit,
      ``initial_skipped_goal_preserved, ``interflow_skipped_goal_preserved,
      ``fullCycle_full, ``full_left_projection, ``full_right_preserves_early_goal] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end SharedParallelGoalProjectionChecks
