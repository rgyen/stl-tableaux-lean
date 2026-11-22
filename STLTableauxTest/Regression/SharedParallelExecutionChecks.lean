import STLTableaux.Automata.Composition.SharedParallelExecution

/-! Projection regressions only. The identity-only left boundary below
can be removed for this constant-flow example. This is not a counterexample
to trajectory projection or to Theorem 5.7. -/
namespace SharedParallelExecutionChecks
open STLTableau STLTableau.HybridAutomaton

def H (loop : Bool) : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := if loop then Set.univ else ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ s s' => s = s'

def ι : Unit ↪ Unit := Function.Embedding.refl _
local notation "P" => parallelOn (H false) (H true) ι ι

def s : (P).State :=
  ⟨(((), ()), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

theorem product_step : (P).DiscreteStep s s := by
  let old : {e // e ∈ (H true).edge} := ⟨((), (), ()), Set.mem_univ _⟩
  let e : {e // e ∈ (P).edge} :=
    ⟨(((), ()), (none, some ()), ((), ())), by exact ⟨by decide, rfl, Set.mem_univ _⟩⟩
  exact ⟨e, rfl, rfl, rfl, old, rfl, rfl⟩

theorem left_no_step (a b : (H false).State) : ¬ (H false).DiscreteStep a b := by
  rintro ⟨e, _⟩
  exact e.property

theorem left_no_nonempty (a b : (H false).State) :
    ¬ Relation.TransGen (H false).DiscreteStep a b := by
  intro steps
  induction steps with
  | single step => exact left_no_step _ _ step
  | tail _ step _ => exact left_no_step _ _ step

noncomputable def σ : FiniteSignal (JoinedVar ι ι) :=
  ⟨3, by norm_num, fun _ _ => 0⟩

/-- Both positive flows are separated by a right-component self-loop. -/
noncomputable def execution : (P).PrelimExecution σ where
  count := 2
  nonempty := by decide
  initialState := s
  initial_mem := ⟨Set.mem_univ _, Set.mem_univ _⟩
  start := fun _ => s
  finish := fun _ => s
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by
    intro i
    fin_cases i <;> norm_num
  curve := fun _ _ _ => 0
  continuousStep := fun _ =>
    ⟨rfl, rfl, rfl, fun _ => ⟨⟨rfl, rfl⟩, Set.mem_univ _, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := fun _ _ => .single product_step
  signal_eq := fun _ _ _ => rfl

theorem projected_left_block_is_reflexive :
    Relation.ReflTransGen (H false).DiscreteStep
      ((H false).leftStateOn (H true) ι ι s) ((H false).leftStateOn (H true) ι ι s) :=
  (H false).parallelOn_nonemptyClosure_left (H true) ι ι (.single product_step)

theorem projected_left_block_is_not_nonempty :
    ¬ Relation.TransGen (H false).DiscreteStep
      ((H false).leftStateOn (H true) ι ι s) ((H false).leftStateOn (H true) ι ι s) :=
  left_no_nonempty _ _

/-- Equal endpoints do not prevent a real self-loop from satisfying `·+`. -/
theorem right_loop : (H true).DiscreteStep
    ((H false).rightStateOn (H true) ι ι s) ((H false).rightStateOn (H true) ι ι s) :=
  ⟨⟨((), (), ()), Set.mem_univ _⟩, rfl, rfl, rfl⟩

theorem right_blocks : ∀ (i : Fin execution.count) (hi : i.val + 1 < execution.count),
    Relation.TransGen (H true).DiscreteStep
      ((H false).rightStateOn (H true) ι ι (execution.finish i))
      ((H false).rightStateOn (H true) ι ι (execution.start ⟨i.val + 1, hi⟩)) :=
  fun _ _ => .single right_loop

noncomputable def projected : (H true).PrelimExecution (σ.reindex (rightVar ι ι)) :=
  execution.rightOfSteps right_blocks

example : projected.count = execution.count := rfl
example : projected.boundary = execution.boundary := rfl
example : projected.duration = execution.duration := rfl
example : projected.curve = fun i t x => execution.curve i t (rightVar ι ι x) := rfl

theorem projected_reaches :
    (H true).PrelimReachesState (σ.reindex (rightVar ι ι)) Set.univ := by
  exact execution.rightOfSteps_reaches right_blocks (Set.mem_univ _)
    execution.visits_finalState

/-- A first flow supplies only a component prefix, not a full trajectory. -/
theorem left_prefix : (H false).IsPrelimPrefix (σ.reindex (leftVar ι ι)) :=
  (H false).parallelOn_prefix_left (H true) ι ι σ ⟨execution⟩

noncomputable def leftPrefix : (H false).PrelimExecution (σ.reindex (leftVar ι ι)) :=
  execution.firstFlowLeft

example : execution.count = 2 ∧ leftPrefix.count = 1 := ⟨rfl, rfl⟩
example : σ.horizon = 3 ∧ (σ.reindex (leftVar ι ι)).horizon = 3 := ⟨rfl, rfl⟩
example : execution.boundary ⟨2, by decide⟩ = 2 ∧
    leftPrefix.boundary ⟨1, by decide⟩ = 1 := by
  change ((2 : ℕ) : ℝ) = 2 ∧ ((1 : ℕ) : ℝ) = 1
  norm_num

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``product_step, ``left_no_step, ``left_no_nonempty, ``execution,
      ``projected_left_block_is_reflexive, ``projected_left_block_is_not_nonempty,
      ``right_loop, ``right_blocks, ``projected, ``projected_reaches, ``left_prefix,
      ``leftPrefix] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end SharedParallelExecutionChecks
