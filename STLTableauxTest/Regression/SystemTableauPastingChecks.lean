import STLTableaux.Automata.Composition.SystemTableauPasting

namespace SystemTableauPastingChecks
open STLTableau STLTableau.Section3 STLTableau.Section4
open STLTableau.HybridAutomaton

def guard : Guard Nat := ⟨7, .ge, 1⟩
noncomputable def action : EdgeLabel Nat :=
  ⟨{guard}, Set.finite_singleton _, ClockResetSet.singleton 7 0⟩
def initialAction : EdgeLabel Nat := ⟨∅, Set.finite_empty, ClockResetSet.empty⟩

noncomputable def T : Tableau Nat (Fin 2) Bool where
  realVariables := {0}
  clocks := {7}
  states := Set.univ
  edges := {(false, action, true)}
  initial := {(initialAction, false)}
  final := {true}
  label := fun _ => ∅
  label_atomic := fun _ _ impossible => impossible.elim

theorem ready : T.TranslationReady where
  states_finite := Set.finite_univ
  variables_finite := Set.finite_singleton _
  clocks_finite := Set.finite_singleton _
  edge_states := fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
  initial_states := fun _ _ => Set.mem_univ _
  final_states := Set.subset_univ _
  edge_guards := by
    intro e he g hg
    change e = (false, action, true) at he
    subst e
    change g = guard at hg
    subst g
    rfl
  initial_guards := by
    intro e he g hg
    change e = (initialAction, false) at he
    subst e
    exact hg.elim
  edge_resets := by
    intro e he
    change e = (false, action, true) at he
    subst e
    exact (ClockResetSet.clocks_singleton 7 0).subset
  initial_resets := by
    intro e he c hc
    change e = (initialAction, false) at he
    subst e
    rcases hc with ⟨a, impossible⟩
    change (none : Option NNReal) = some a at impossible
    cases impossible
  atom_variables := by intro q hq a impossible; exact impossible.elim

def H : HybridAutomaton Unit Unit (Fin 2) where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := Set.univ
  initial := {s | s.2 0 = 1 ∧ s.2 1 = 10}
  invariant := Set.univ
  flow := fun _ _ _ => True
  trajectory_closed := HybridFlow.Closed.unconstrained _
  jump := fun _ s s' => s'.2 0 = s.2 0 ∧ s'.2 1 = s.2 1 + 10

def sv (r p : ℝ) : Fin 2 → ℝ := fun x => if x = 0 then r else p
def system (r p : ℝ) : H.State := ⟨((), sv r p), Set.mem_univ _⟩

def mv (r g c d : ℝ) : T.TypedVar → ℝ
  | .inl (.inl _) => r
  | .inl (.inr (.inl _)) => c
  | .inl (.inr (.inr _)) => g
  | .inr b => if b then 1 else d

def monitor (q : Bool) (r g c d : ℝ) (bound : g ≤ 2) :
    (T.prelimAutomaton ready 2).State :=
  ⟨(⟨q, Set.mem_univ _⟩, mv r g c d), Or.inr rfl, fun _ => bound,
    (by intro a impossible; exact impossible.elim),
    (by intro m impossible; exact impossible.elim)⟩

noncomputable def ρ : FiniteSignal (Fin 2) :=
  ⟨2, by norm_num, fun t => sv (t.val + 1) (if t.val < 1 then 10 else 20)⟩
noncomputable def aug : FiniteSignal T.TypedVar :=
  ⟨2, by norm_num, fun t => mv (t.val + 1) t.val
    (if t.val < 1 then t.val else t.val - 1) (if t.val < 1 then t.val else t.val - 1)⟩

theorem projects : T.TypedProjectsTo aug ρ := by
  refine ⟨rfl, ?_⟩
  intro t u time x
  have real : x.val = 0 := x.property
  change t.val + 1 = if x.val = 0 then u.val + 1 else _
  rw [real, time]
  simp

theorem original_system_signal : T.systemSignal (T.joinSignal ρ aug projects) = ρ :=
  T.joinSignal_system ρ aug projects
theorem original_monitor_signal : T.tableauSignal (T.joinSignal ρ aug projects) = aug :=
  T.joinSignal_tableau ρ aug projects

theorem private_coordinate (t : (T.joinSignal ρ aug projects).Time) (before : t.val < 1) :
    (T.joinSignal ρ aug projects).value t (T.systemCoordinate 1) = 10 := by
  change (if (1 : Fin 2) = 0 then t.val + 1 else if t.val < 1 then 10 else 20) = 10
  simp [before]

def first : ObservedFlow H ρ where
  start := system 1 10
  finish := system 2 10
  beginTime := 0
  endTime := 1
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t => sv (t.val + 1) 10
  step := by
    refine ⟨rfl, ?_, ?_, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    · funext x
      norm_num [sv, system]
    · funext x
      norm_num [sv, system]
  observe := by
    intro t ht
    change sv (t.val + 1) (if t.val < 1 then 10 else 20) = sv ((t.val - 0) + 1) 10
    simp [ht.2]

def second : ObservedFlow (T.prelimAutomaton ready 2) aug where
  start := monitor false 1 0 0 0 (by norm_num)
  finish := monitor false 2 1 1 1 (by norm_num)
  beginTime := 0
  endTime := 1
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t => mv (t.val + 1) t.val t.val t.val
  step := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · funext x
      rcases x with (x | c) | b
      · norm_num [mv, monitor]
      · rcases c with c | u <;> norm_num [mv, monitor]
      · cases b <;> norm_num [mv, monitor]
    · funext x
      rcases x with (x | c) | b
      · norm_num [mv, monitor]
      · rcases c with c | u <;> norm_num [mv, monitor]
      · cases b <;> norm_num [mv, monitor]
    · intro t
      refine ⟨⟨fun _ => (zero_add _).symm, (zero_add _).symm, (zero_add _).symm, rfl⟩, ?_⟩
      have bound : t.val ≤ (1 : ℝ) := t.property.2
      exact (monitor false _ _ _ _ (by linarith)).property
  observe := by
    intro t ht
    change mv (t.val + 1) t.val (if t.val < 1 then t.val else t.val - 1)
      (if t.val < 1 then t.val else t.val - 1) =
      mv ((t.val - 0) + 1) (t.val - 0) (t.val - 0) (t.val - 0)
    simp [ht.2]

theorem closed_agreement : ∀ t x, first.curve t x.val =
    HybridFlow.castCurve second.curve (T.flow_duration_eq H ready 2 first second rfl rfl)
      t (.inl (.inl x)) := by
  intro t x
  have real : x.val = 0 := x.property
  change (if x.val = 0 then t.val + 1 else 10) = t.val + 1
  rw [real]
  simp

noncomputable def jointFlow :=
  T.pasteObservedFlow H ready 2 projects first second rfl rfl closed_agreement

theorem actual_joint_step :
    (T.systemTableauAutomaton H ready 2).ContinuousStep
      jointFlow.start jointFlow.finish jointFlow.duration jointFlow.curve := jointFlow.step

theorem observation_preserved (t : (T.joinSignal ρ aug projects).Time)
    (inside : 0 ≤ t.val ∧ t.val < 1) :
    (T.joinSignal ρ aug projects).value t = jointFlow.curve ⟨t.val, by
      constructor
      · exact inside.1
      · change t.val ≤ (1 : ℝ); exact inside.2.le⟩ := by
  have observed := jointFlow.observe t inside
  convert observed using 1
  apply congrArg jointFlow.curve
  exact Subtype.ext (by dsimp [jointFlow, Tableau.pasteObservedFlow, first]; ring)

def target := monitor true 2 1 0 0 (by norm_num)

theorem monitor_jump : (T.prelimAutomaton ready 2).DiscreteStep second.finish target := by
  let edge : {e // e ∈ (T.prelimAutomaton ready 2).edge} :=
    ⟨(⟨false, Set.mem_univ _⟩, action, ⟨true, Set.mem_univ _⟩), rfl⟩
  refine ⟨edge, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro g hg
    change g = guard at hg
    subst g
    exact ⟨rfl, le_rfl⟩
  · intro c
    have real : c.val = 7 := c.property
    change (0 : ℝ) = T.reset action.resets (T.old second.finish.val.2) (.inr (.inl c))
    simp [Tableau.reset, action, ClockResetSet.singleton, real]
  · intro impossible
    exact impossible.elim
  · intro impossible
    norm_num [second, monitor, mv, Tableau.dwell] at impossible
  · intro impossible
    norm_num [target, monitor, mv, Tableau.bit] at impossible

theorem system_jump : H.DiscreteStep first.finish (system 2 20) :=
  ⟨⟨((), (), ()), Set.mem_univ _⟩, rfl, rfl, rfl, by norm_num [first, system, sv]⟩

theorem final_agreement (x : T.realVariables) :
    (system 2 20).val.2 x.val = target.val.2 (.inl (.inl x)) := by
  have real : x.val = 0 := x.property
  change (if x.val = 0 then 2 else 20) = 2
  rw [real]
  simp

theorem source_agreement : ∀ x : T.realVariables,
    first.finish.val.2 x.val = second.finish.val.2 (.inl (.inl x)) :=
  T.curve_final_agreement H ready 2 first.step
    (second.step.castDuration (T.flow_duration_eq H ready 2 first second rfl rfl)) closed_agreement

noncomputable def joinedTarget := T.joinState H ready 2 (system 2 20) target final_agreement

theorem actual_simultaneous_jump :
    (T.systemTableauAutomaton H ready 2).DiscreteStep jointFlow.finish joinedTarget :=
  T.paste_simultaneous H ready 2 source_agreement final_agreement system_jump monitor_jump

theorem after_system_agreement (x : T.realVariables) :
    (system 2 20).val.2 x.val = second.finish.val.2 (.inl (.inl x)) := by
  have real : x.val = 0 := x.property
  change (if x.val = 0 then 2 else 20) = 2
  rw [real]
  simp

theorem actual_one_sided_jumps :
    Relation.ReflTransGen (T.systemTableauAutomaton H ready 2).DiscreteStep
      jointFlow.finish joinedTarget :=
  (Relation.ReflTransGen.single (T.paste_system_step H ready 2 second.finish
    source_agreement after_system_agreement system_jump)).tail
      (T.paste_monitor_step H ready 2 (system 2 20)
        after_system_agreement final_agreement monitor_jump)

theorem actual_goal : joinedTarget ∈ T.systemTableauGoal H ready 2 := by
  change H.rightStateOn (T.prelimAutomaton ready 2) T.systemVarName T.tableauVarName
    (T.joinState H ready 2 (system 2 20) target final_agreement) ∈ T.prelimGoal ready 2
  rw [T.joinState_tableau]
  exact Or.inl rfl

theorem bad_guard_rejected :
    ¬ (T.prelimAutomaton ready 2).DiscreteStep (monitor false 2 1 0 1 (by norm_num)) target := by
  rintro ⟨e, _, _, _, _, guards, _⟩
  have shape : (e.val.1.val, e.val.2.1, e.val.2.2.val) = (false, action, true) := e.property
  have label : e.val.2.1 = action := congrArg (fun e => e.2.1) shape
  rw [label] at guards
  obtain ⟨_, bound⟩ := guards guard rfl
  norm_num [Tableau.realComparison, Tableau.old, mv, monitor, guard] at bound

theorem bad_reset_rejected :
    ¬ (T.prelimAutomaton ready 2).DiscreteStep second.finish
      (monitor true 2 1 1 0 (by norm_num)) := by
  rintro ⟨e, _, _, _, _, _, reset, _⟩
  have shape : (e.val.1.val, e.val.2.1, e.val.2.2.val) = (false, action, true) := e.property
  have label : e.val.2.1 = action := congrArg (fun e => e.2.1) shape
  rw [label] at reset
  have value := reset ⟨7, rfl⟩
  norm_num [Tableau.reset, Tableau.old, mv, monitor, action, ClockResetSet.singleton] at value

def afterFirst : ObservedFlow H ρ where
  start := system 2 20
  finish := system 3 20
  beginTime := 1
  endTime := 2
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t => sv (t.val + 2) 20
  step := by
    refine ⟨rfl, ?_, ?_, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
    · funext x
      norm_num [sv, system]
    · funext x
      norm_num [sv, system]
  observe := by
    intro t ht
    change sv (t.val + 1) (if t.val < 1 then 10 else 20) = sv ((t.val - 1) + 2) 20
    rw [if_neg (not_lt_of_ge ht.1)]
    congr 1
    ring

def afterSecond : ObservedFlow (T.prelimAutomaton ready 2) aug where
  start := target
  finish := monitor true 3 2 1 1 (by norm_num)
  beginTime := 1
  endTime := 2
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t => mv (t.val + 2) (t.val + 1) t.val t.val
  step := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · funext x
      rcases x with (x | c) | b
      · norm_num [mv, monitor, target]
      · rcases c with c | u <;> norm_num [mv, monitor, target]
      · cases b <;> norm_num [mv, monitor, target]
    · funext x
      rcases x with (x | c) | b
      · norm_num [mv, monitor]
      · rcases c with c | u <;> norm_num [mv, monitor]
      · cases b <;> norm_num [mv, monitor]
    · intro t
      refine ⟨⟨fun _ => (zero_add _).symm, ?_, (zero_add _).symm, rfl⟩, ?_⟩
      · change t.val + 1 = 1 + t.val
        ring
      · have bound : t.val ≤ (1 : ℝ) := t.property.2
        exact (monitor true _ _ _ _ (by linarith)).property
  observe := by
    intro t ht
    change mv (t.val + 1) t.val (if t.val < 1 then t.val else t.val - 1)
      (if t.val < 1 then t.val else t.val - 1) =
      mv ((t.val - 1) + 2) ((t.val - 1) + 1) (t.val - 1) (t.val - 1)
    rw [if_neg (not_lt_of_ge ht.1)]
    congr 1 <;> ring

theorem after_agreement : ∀ t x, afterFirst.curve t x.val =
    HybridFlow.castCurve afterSecond.curve
      (T.flow_duration_eq H ready 2 afterFirst afterSecond rfl rfl) t (.inl (.inl x)) := by
  intro t x
  have real : x.val = 0 := x.property
  change (if x.val = 0 then t.val + 2 else 20) = t.val + 2
  rw [real]
  simp

noncomputable def afterJointFlow :=
  T.pasteObservedFlow H ready 2 projects afterFirst afterSecond rfl rfl after_agreement

theorem monitor_initial : second.start.val ∈ (T.prelimAutomaton ready 2).initial := by
  refine ⟨initialAction, rfl, T.old second.start.val.2, ?_, ?_, rfl, rfl⟩
  · intro g impossible
    exact impossible.elim
  · funext x
    rcases x with x | c
    · rfl
    · rcases c with c | u
      · rfl
      · rfl

theorem joint_initial : jointFlow.start.val ∈ (T.systemTableauAutomaton H ready 2).initial :=
  T.joinState_initial H ready 2 first.start second.start
    (T.curve_initial_agreement H ready 2 first.step
      (second.step.castDuration (T.flow_duration_eq H ready 2 first second rfl rfl))
      closed_agreement)
    ⟨rfl, rfl⟩ monitor_initial

/-- No product execution is supplied: it is built from the actual component
flows and one-sided jumps. The goal at time 1 survives continuation to time 2. -/
theorem actual_full_execution_with_early_goal :
    ∃ out : (T.systemTableauAutomaton H ready 2).PrelimExecution (T.joinSignal ρ aug projects),
      out.ReachesHorizon ∧ out.VisitsState joinedTarget := by
  have entry : afterJointFlow.start = joinedTarget := rfl
  let word : ObservedFlowChain (T.systemTableauAutomaton H ready 2) (T.joinSignal ρ aug projects)
      (Relation.ReflTransGen (T.systemTableauAutomaton H ready 2).DiscreteStep)
      jointFlow.start 0 afterJointFlow.finish 2 :=
    .snoc (.single jointFlow) afterJointFlow rfl (entry.symm ▸ actual_one_sided_jumps)
  have goal : word.VisitsState joinedTarget :=
    Or.inr (Or.inr (entry ▸ afterJointFlow.visits_start))
  obtain ⟨normal, preserve⟩ := word.normalize
  obtain ⟨out, _, _, _, stop, visits⟩ :=
    normal.toExecution jointFlow.start joint_initial rfl
    .refl (by change (2 : ℝ) ≤ 2; rfl)
  exact ⟨out, stop, visits _ (preserve _ goal)⟩

run_elab do
  for name in #[``original_system_signal, ``original_monitor_signal, ``private_coordinate,
      ``actual_joint_step, ``observation_preserved, ``monitor_jump, ``system_jump,
      ``actual_simultaneous_jump, ``actual_one_sided_jumps, ``actual_goal,
      ``bad_guard_rejected, ``bad_reset_rejected,
      ``actual_full_execution_with_early_goal] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end SystemTableauPastingChecks
