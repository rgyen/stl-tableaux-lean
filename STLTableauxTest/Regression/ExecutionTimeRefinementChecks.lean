import STLTableaux.Automata.Execution.ExecutionTimeRefinement

namespace ExecutionTimeRefinementChecks
open STLTableau STLTableau.HybridAutomaton

def clock (M : Type*) [Finite M] (edges : Bool) : HybridAutomaton M Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := if edges then Set.univ else ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun s t v => ∀ x, v x = s.2 x + t
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by
      intro q v a b r s first total x
      dsimp only [Prod.snd] at *
      rw [total x, first x]
      push_cast
      ring)
    (by
      intro q v a b r s first second x
      dsimp only [Prod.snd] at *
      rw [second x, first x]
      push_cast
      ring)
  jump := fun _ s s' => s'.2 = s.2

def state {M : Type*} [Finite M] (edges : Bool) (q : M) (t : ℝ) : (clock M edges).State :=
  ⟨(q, fun _ => t), Set.mem_univ _⟩

noncomputable def signal : FiniteSignal Unit := ⟨3, by norm_num, fun t _ => t.val⟩

def threeBoundaries (i : Fin 3) : ℝ :=
  if i.val = 0 then 0 else if i.val = 1 then 1 else 3

theorem three_increasing : StrictMono threeBoundaries := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [threeBoundaries]

noncomputable def one : (clock Unit false).PrelimExecution signal where
  count := 1
  nonempty := by decide
  initialState := state false () 0
  initial_mem := Set.mem_univ _
  start := fun _ => state false () 0
  finish := fun _ => state false () 3
  boundary := fun i => if i.val = 0 then 0 else 3
  first_zero := rfl
  increasing := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 3
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ t _ => t.val
  continuousStep := fun _ => ⟨rfl, rfl, rfl,
    fun _ => ⟨fun _ => (zero_add _).symm, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i impossible; have := i.isLt; omega
  signal_eq := by
    intro i t ht
    fin_cases i
    funext x
    change t.val = t.val - 0
    ring

theorem one_full : one.ReachesHorizon := by
  unfold PrelimExecution.ReachesHorizon
  dsimp only [one]
  norm_num [signal]

theorem jump (a b : Bool) : (clock Bool true).DiscreteStep (state true a 1) (state true b 1) :=
  ⟨⟨(a, (), b), Set.mem_univ _⟩, rfl, rfl, rfl⟩

noncomputable def two : (clock Bool true).PrelimExecution signal where
  count := 2
  nonempty := by decide
  initialState := state true false 0
  initial_mem := Set.mem_univ _
  start := fun i => state true false (if i.val = 0 then 0 else 1)
  finish := fun i => state true false (if i.val = 0 then 1 else 3)
  boundary := threeBoundaries
  first_zero := rfl
  increasing := three_increasing
  last_le_horizon := by norm_num [threeBoundaries, signal]
  duration := fun i => if i.val = 0 then 1 else 2
  duration_eq := by intro i; fin_cases i <;> norm_num [threeBoundaries]
  curve := fun i t _ => (if i.val = 0 then 0 else 1) + t.val
  continuousStep := by
    intro i
    refine ⟨rfl, ?_, ?_, fun _ => ⟨fun _ => rfl, Set.mem_univ _⟩⟩
    · funext x
      exact add_zero _
    · fin_cases i <;> funext x <;> norm_num [state]
  initialSteps := .refl
  discreteSteps := by
    intro i hi
    have zero : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    exact (Relation.TransGen.single (jump false true)).tail (jump true false)
  signal_eq := by
    intro i t ht
    fin_cases i <;> funext x <;> dsimp [threeBoundaries, signal] <;> ring

theorem two_full : two.ReachesHorizon := by
  unfold PrelimExecution.ReachesHorizon
  dsimp only [two]
  norm_num [signal, threeBoundaries]

theorem common_time_exists :
    ∃ (k : ℕ) (b : Fin (k + 1) → ℝ) (hb : StrictMono b)
      (r₁ : RefinesBoundaries one.boundary b) (r₂ : RefinesBoundaries two.boundary b),
      0 < k ∧ b 0 = 0 ∧ b (Fin.last k) = signal.horizon ∧
      ∀ j, (one.refinedFlow r₁ hb j).beginTime = (two.refinedFlow r₂ hb j).beginTime ∧
        (one.refinedFlow r₁ hb j).endTime = (two.refinedFlow r₂ hb j).endTime :=
  one.exists_common_refined_flows two one_full two_full rfl

theorem refines_one : RefinesBoundaries one.boundary threeBoundaries := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

theorem refines_two : RefinesBoundaries two.boundary threeBoundaries :=
  ⟨rfl, rfl, fun i => ⟨i, rfl⟩⟩

theorem one_owner (j : Fin 2) :
    refines_one.cell three_increasing j = ⟨0, by norm_num [one]⟩ := by
  apply Fin.ext
  change (refines_one.cell three_increasing j).val = 0
  have bound := (refines_one.cell three_increasing j).isLt
  change (refines_one.cell three_increasing j).val < 1 at bound
  omega

theorem actual_rebased_value :
    (one.refinedFlow refines_one three_increasing 1).start.val.2 () = 1 := by
  change threeBoundaries (1 : Fin 2).castSucc -
    one.boundary (refines_one.cell three_increasing 1).castSucc = 1
  simp only [one_owner]
  change (1 : ℝ) - 0 = 1
  norm_num

theorem artificial_boundary_is_idle :
    (one.refinedFlow refines_one three_increasing 0).finish =
      (one.refinedFlow refines_one three_increasing 1).start := by
  have same : refines_one.cell three_increasing 1 = refines_one.cell three_increasing 0 :=
    (one_owner 1).trans (one_owner 0).symm
  exact (one.observedFlow (refines_one.cell three_increasing 0)).sliceAt_join_of_eq
    (one.observedFlow (refines_one.cell three_increasing 1))
    (congrArg one.observedFlow same) (threeBoundaries 0) (threeBoundaries 1)
    (threeBoundaries 2)
    ⟨refines_one.cell_left three_increasing 0, by norm_num [threeBoundaries],
      refines_one.cell_right three_increasing 0⟩
    ⟨refines_one.cell_left three_increasing 1, by norm_num [threeBoundaries],
      refines_one.cell_right three_increasing 1⟩

theorem right_endpoint_retained :
    ∃ j, (one.refinedFlow refines_one three_increasing j).VisitsState one.finalState := by
  apply one.refinedFlow_covers refines_one three_increasing
  exact (one.observedFlow one.lastIndex).visits_finish

theorem old_jump_block_retained :
    ∃ (j : Fin 2) (hj : j.val + 1 < 2),
      (two.refinedFlow refines_two three_increasing j).finish = state true false 1 ∧
      (two.refinedFlow refines_two three_increasing ⟨j.val + 1, hj⟩).start = state true false 1 :=
  two.refinedFlow_old_boundary refines_two three_increasing ⟨0, by norm_num [two]⟩
    (by norm_num [two])

theorem middle_jump_goal_preserved :
    ∃ (j : Fin 2) (hj : j.val + 1 < 2),
      Relation.ReflTransGen (clock Bool true).DiscreteStep
        (two.refinedFlow refines_two three_increasing j).finish (state true true 1) ∧
      Relation.ReflTransGen (clock Bool true).DiscreteStep (state true true 1)
        (two.refinedFlow refines_two three_increasing ⟨j.val + 1, hj⟩).start := by
  obtain ⟨j, hj, finish, start⟩ := old_jump_block_retained
  exact ⟨j, hj, finish.symm ▸ .single (jump false true), start.symm ▸ .single (jump true false)⟩

run_elab do
  for name in #[``common_time_exists, ``actual_rebased_value, ``artificial_boundary_is_idle,
      ``right_endpoint_retained, ``old_jump_block_retained, ``middle_jump_goal_preserved] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end ExecutionTimeRefinementChecks
