import STLTableaux.Automata.Composition.SharedParallelPasting

namespace SharedParallelPastingChecks
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

def ι : Unit ↪ Unit := Function.Embedding.refl _

local notation "P" => parallelOn (constant Unit false) (constant Bool true) ι ι

def state (q : Bool) : (P).State :=
  ⟨(((), q), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

/-- Constructed only from a right-component jump and a left-component idle. -/
theorem componentStep (a b : Bool) :
    ComponentStep (constant Unit false) (constant Bool true) ι ι (state a) (state b) := by
  refine ⟨none, some (), ?_, rfl, Set.mem_univ _, rfl, ?_⟩
  · decide
  · exact ⟨⟨(a, (), b), Set.mem_univ _⟩, rfl, rfl⟩

noncomputable def signal : FiniteSignal (JoinedVar ι ι) :=
  ⟨3, by norm_num, fun _ _ => 0⟩

/-- Flow segments and paired jumps of the components for constructing a
product execution. -/
noncomputable def data : ParallelComponentData
    (constant Unit false) (constant Bool true) ι ι signal where
  count := 2
  nonempty := by decide
  initialState := state false
  initial_left := Set.mem_univ _
  initial_right := Set.mem_univ _
  start := fun _ => state false
  finish := fun _ => state false
  boundary := fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else 3
  first_zero := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := by norm_num [signal]
  duration := fun i => if i.val = 0 then 1 else 2
  duration_eq := by intro i; fin_cases i <;> norm_num
  curve := fun _ _ _ => 0
  flow_left := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  flow_right := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := fun _ _ =>
    (Relation.ReflTransGen.single (componentStep false true)).tail (componentStep true false)
  observe_left := fun _ _ _ _ => rfl
  observe_right := fun _ _ _ _ => rfl

theorem data_full : data.boundary ⟨data.count, by omega⟩ = signal.horizon := by
  dsimp only [data]
  norm_num [signal]

/-- A goal in a skipped discrete state at time 1, not at the final state. -/
theorem intermediate_goal : data.VisitsState (state true) := by
  refine Or.inr (Or.inr ⟨⟨0, by norm_num [data]⟩, by norm_num [data], ?_, ?_⟩)
  · exact .single (componentStep false true)
  · exact .single (componentStep true false)

theorem paste_full_early_goal :
    ∃ out : (P).PrelimExecution signal, out.ReachesHorizon ∧
      out.finalState = state false ∧ out.VisitsState (state true) := by
  obtain ⟨out, full, final, visits⟩ := data.full_execution data_full
  exact ⟨out, full, final, visits _ intermediate_goal⟩

theorem paste_component_goal :
    ∃ out : (P).PrelimExecution signal, out.ReachesHorizon ∧
      ∃ s, ((constant Unit false).rightStateOn (constant Bool true) ι ι s).val.1 = true ∧
        out.VisitsState s :=
  data.full_right_goal data_full {s | s.val.1 = true}
    ⟨state true, rfl, intermediate_goal⟩

noncomputable def initialData := { data with initialSteps :=
  (Relation.ReflTransGen.single (componentStep false true)).tail (componentStep true false) }

theorem paste_initial_goal :
    ∃ out : (P).PrelimExecution signal, out.ReachesHorizon ∧
      out.VisitsState (state true) := by
  have initial : initialData.VisitsState (state true) :=
    Or.inr (Or.inl ⟨.single (componentStep false true), .single (componentStep true false)⟩)
  obtain ⟨out, full, _, visits⟩ := initialData.full_execution data_full
  exact ⟨out, full, visits _ initial⟩

/-- Compatibility includes the shared value at every state, not just on the
half-open observed signal. Conflicting closed endpoints cannot be pasted. -/
theorem no_conflicting_shared_state :
    ¬ ∃ s : (P).State,
      ((constant Unit false).leftStateOn (constant Bool true) ι ι s).val.2 () = 0 ∧
      ((constant Unit false).rightStateOn (constant Bool true) ι ι s).val.2 () = 1 := by
  rintro ⟨s, l, r⟩
  have equal := (constant Unit false).parallelOn_shared_value (constant Bool true) ι ι s
    (x := ()) (y := ()) rfl
  linarith

local notation "I" => parallelOn (constant Unit false) (constant Unit false) ι ι

def idleState : (I).State :=
  ⟨(((), ()), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

theorem no_component_step (a b : (I).State) :
    ¬ ComponentStep (constant Unit false) (constant Unit false) ι ι a b := by
  rintro ⟨l₁, l₂, live, edge₁, edge₂, _⟩
  cases l₁ with
  | some l => exact edge₁
  | none =>
    cases l₂ with
    | some l => exact edge₂
    | none => exact live rfl

noncomputable def idleData : ParallelComponentData
    (constant Unit false) (constant Unit false) ι ι signal where
  count := 2
  nonempty := by decide
  initialState := idleState
  initial_left := Set.mem_univ _
  initial_right := Set.mem_univ _
  start := fun _ => idleState
  finish := fun _ => idleState
  boundary := data.boundary
  first_zero := data.first_zero
  increasing := data.increasing
  last_le_horizon := data.last_le_horizon
  duration := data.duration
  duration_eq := data.duration_eq
  curve := fun _ _ _ => 0
  flow_left := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  flow_right := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := fun _ _ => .refl
  observe_left := fun _ _ _ _ => rfl
  observe_right := fun _ _ _ _ => rfl

/-- Empty paired connectors need no invented jump. The two cells concatenate
to one full positive flow with exactly the original horizon. -/
theorem idle_boundary_contracts :
    ∃ out : (I).PrelimExecution signal, out.ReachesHorizon ∧ out.count = 1 := by
  obtain ⟨out, full, _, _⟩ := idleData.full_execution data_full
  refine ⟨out, full, ?_⟩
  by_contra hn
  have hi : 1 < out.count := by have := out.nonempty; omega
  have noStep : ∀ a b, ¬ (I).DiscreteStep a b := by
    intro a b step
    exact no_component_step a b
      (((constant Unit false).parallelOn_discrete_iff (constant Unit false) ι ι a b).mp step)
  have noPath : ∀ a b, ¬ Relation.TransGen (I).DiscreteStep a b := by
    intro a b steps
    induction steps with
    | single step => exact noStep _ _ step
    | tail _ step _ => exact noStep _ _ step
  exact noPath _ _ (out.discreteSteps ⟨0, by omega⟩ hi)

run_elab do
  for n in #[``paste_full_early_goal, ``paste_component_goal, ``paste_initial_goal,
      ``no_conflicting_shared_state, ``no_component_step, ``idle_boundary_contracts] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end SharedParallelPastingChecks
