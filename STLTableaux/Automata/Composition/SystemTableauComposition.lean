import STLTableaux.Automata.Composition.SharedParallelGoalProjection
import STLTableaux.Automata.Recognition.TypedOrdinaryTrace
import STLTableaux.Automata.Composition.SharedParallelConstruction

/-! The system and translated automaton share the real-valued variables.
The clocks and two boundary coordinates of the translated automaton use
distinct names. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

abbrev CompositionName := Sum Var (Sum (Sum T.clocks Unit) Bool)

def systemVarName : Var ↪ T.CompositionName := ⟨Sum.inl, Sum.inl_injective⟩

def tableauVarName : T.TypedVar ↪ T.CompositionName where
  toFun
    | .inl (.inl x) => .inl x.val
    | .inl (.inr c) => .inr (.inl c)
    | .inr b => .inr (.inr b)
  inj' := by
    intro a b equal
    cases a with
    | inl a =>
      cases a with
      | inl x =>
        cases b with
        | inl b =>
          cases b with
          | inl y =>
            exact congrArg (fun x => Sum.inl (Sum.inl x))
              (Subtype.ext (Sum.inl.inj equal))
          | inr c => cases equal
        | inr b => cases equal
      | inr c =>
        cases b with
        | inl b =>
          cases b with
          | inl x => cases equal
          | inr d =>
            exact congrArg (fun c => Sum.inl (Sum.inr c))
              (Sum.inl.inj (Sum.inr.inj equal))
        | inr b => cases equal
    | inr a =>
      cases b with
      | inl b => cases b <;> cases equal
      | inr b => exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj equal))

abbrev CompositionVar := HybridAutomaton.JoinedVar T.systemVarName T.tableauVarName

def systemCoordinate (x : Var) : T.CompositionVar :=
  HybridAutomaton.leftVar T.systemVarName T.tableauVarName x

def tableauCoordinate (x : T.TypedVar) : T.CompositionVar :=
  HybridAutomaton.rightVar T.systemVarName T.tableauVarName x

theorem shared_real_coordinate (x : T.realVariables) :
    T.systemCoordinate x.val = T.tableauCoordinate (.inl (.inl x)) :=
  HybridAutomaton.shared_variable_eq _ _ rfl

theorem monitor_clock_fresh (x : Var) (c : Sum T.clocks Unit) :
    T.systemCoordinate x ≠ T.tableauCoordinate (.inl (.inr c)) := by
  intro equal
  have name := congrArg Subtype.val equal
  cases name

theorem monitor_bit_fresh (x : Var) (b : Bool) :
    T.systemCoordinate x ≠ T.tableauCoordinate (.inr b) := by
  intro equal
  have name := congrArg Subtype.val equal
  cases name

def systemSignal (σ : FiniteSignal T.CompositionVar) : FiniteSignal Var :=
  σ.reindex T.systemCoordinate

def tableauSignal (σ : FiniteSignal T.CompositionVar) : FiniteSignal T.TypedVar :=
  σ.reindex T.tableauCoordinate

theorem tableauSignal_projectsTo (σ : FiniteSignal T.CompositionVar) :
    T.TypedProjectsTo (T.tableauSignal σ) (T.systemSignal σ) := by
  refine ⟨rfl, ?_⟩
  intro t u equal x
  have time : t = u := Subtype.ext equal
  subst u
  exact congrArg (σ.value t) (T.shared_real_coordinate x).symm

variable (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady) (τ : ℝ)

def systemTableauAutomaton :=
  H.parallelOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName

def systemTableauGoal : Set (T.systemTableauAutomaton H h τ).State :=
  {s | H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s ∈
    T.prelimGoal h τ}

/-- A goal-reaching execution of the composed automaton supplies a system
execution prefix and a goal visit of the translated automaton on the two
projections of the same signal. The latter projection preserves the ending
time and every goal visit. -/
theorem systemTableau_goal_projections (σ : FiniteSignal T.CompositionVar)
    (reached : (T.systemTableauAutomaton H h τ).PrelimReachesState σ
      (T.systemTableauGoal H h τ)) :
    H.IsPrelimPrefix (T.systemSignal σ) ∧
      (T.prelimAutomaton h τ).PrelimReachesState (T.tableauSignal σ) (T.prelimGoal h τ) ∧
      T.TypedProjectsTo (T.tableauSignal σ) (T.systemSignal σ) := by
  refine ⟨?_, ?_, T.tableauSignal_projectsTo σ⟩
  · obtain ⟨e, _⟩ := reached
    exact H.parallelOn_prefix_left (T.prelimAutomaton h τ)
      T.systemVarName T.tableauVarName σ ⟨e⟩
  · exact T.parallel_prelim_goal_projection h τ H T.systemVarName T.tableauVarName σ reached

/-- Project a full trajectory with an arbitrary earlier goal visit. The same execution of the
translated automaton witnesses both full membership and the preserved goal visit;
no prefix continuation or terminal jump is assumed. -/
theorem systemTableau_full_goal_projections (σ : FiniteSignal T.CompositionVar)
    (e : (T.systemTableauAutomaton H h τ).PrelimExecution σ) (full : e.ReachesHorizon)
    {s : (T.systemTableauAutomaton H h τ).State} (goal : s ∈ T.systemTableauGoal H h τ)
    (visit : e.VisitsState s) :
    H.IsPrelimTrajectory (T.systemSignal σ) ∧
      (T.prelimAutomaton h τ).IsPrelimTrajectory (T.tableauSignal σ) ∧
      (T.prelimAutomaton h τ).PrelimReachesState (T.tableauSignal σ) (T.prelimGoal h τ) ∧
      T.TypedProjectsTo (T.tableauSignal σ) (T.systemSignal σ) := by
  have system := H.parallelOn_trajectory_left (T.prelimAutomaton h τ)
    T.systemVarName T.tableauVarName ⟨e, full⟩
  obtain ⟨out, outFull, _, preserve⟩ := e.rightFullProjection full
  exact ⟨system, ⟨out, outFull⟩,
    ⟨out, H.rightStateOn (T.prelimAutomaton h τ) T.systemVarName T.tableauVarName s,
      goal, preserve s visit⟩, T.tableauSignal_projectsTo σ⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``tableauVarName, ``shared_real_coordinate, ``monitor_clock_fresh,
      ``monitor_bit_fresh, ``tableauSignal_projectsTo, ``systemTableau_goal_projections,
      ``systemTableau_full_goal_projections] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
