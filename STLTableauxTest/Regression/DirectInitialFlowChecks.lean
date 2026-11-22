import STLTableaux.Automata.Translation.PrelimStateGoalCorrectness
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

/-! The system starts directly from x=0 with x(t)=t and has no jumps.
The atomic predicate x≤0 holds only on the initial singleton. The property
automaton can leave that singleton without resetting shared real values. -/
namespace DirectInitialFlowChecks
open STLTableau STLTableau.HybridAutomaton
open STLTableau.Section4 STLTableau.Section4.Finiteness

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 0}
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
  jump := fun _ _ _ => False

def zero : H.State := ⟨((), fun _ => 0), Set.mem_univ _⟩
def one : H.State := ⟨((), fun _ => 1), Set.mem_univ _⟩
noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => t.val⟩

noncomputable def direct : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := zero
  initial_mem := rfl
  start := fun _ => zero
  finish := fun _ => one
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ t _ => t.val
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ =>
    ⟨fun _ => by simp [zero]; rfl, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := by
    intro i t ht
    fin_cases i
    funext x
    simp [σ]

theorem full : direct.ReachesHorizon := by
  unfold PrelimExecution.ReachesHorizon
  dsimp only [direct]
  norm_num [σ]

theorem starts_with_flow : direct.initialState = direct.start ⟨0, direct.nonempty⟩ := rfl

theorem initial_equals_first_curve :
    σ.value ⟨0, le_rfl, σ.horizon_pos⟩ =
      direct.curve ⟨0, direct.nonempty⟩ ⟨0, by simp⟩ :=
  direct.signal_at_zero_curve

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => -v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : (inputTableau (Clock := Nat) Set.univ root).TranslationReady :=
  finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp)

theorem functions_continuous : ∀ a,
    Formula.IsSubformula (.atom a) root.val → Continuous a.function := by
  intro a sub
  cases sub
  exact (continuous_apply (0 : Fin 1)).neg

theorem wellBehaved_system : direct.WellBehaved root.val :=
  direct.wellBehaved_of_continuousFlows root.val continuous_flows functions_continuous

theorem signal_regularity_is_derived : SignalAtomRightContinuous σ root.val :=
  wellBehaved_system.signalAtomRightContinuous full

theorem p_iff_zero (t : σ.Time) : σ.Satisfies root.val t ↔ t.val = 0 := by
  change -t.val ≥ 0 ↔ t.val = 0
  constructor
  · intro h; linarith [t.property.1]
  · intro h; simp [h]

def bs : Fin 3 → ℝ := ![0, 0, 1]
def ms : Fin 3 → Marker := ![●, ○, ●]
def P : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; change i.val ≤ j.val at hij
        fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i <;> norm_num [ms, bs] at *) rfl rfl

theorem stable : σ.StablePartition root.val P := by
  intro i χ sub u v hu hv
  cases sub
  rw [p_iff_zero u, p_iff_zero v]
  change Fin 2 at i
  change u.val ∈ (IntervalPartition.markedBoundaryPiece bs ms i).carrier at hu
  change v.val ∈ (IntervalPartition.markedBoundaryPiece bs ms i).carrier at hv
  fin_cases i <;>
    simp [IntervalPartition.markedBoundaryPiece, MarkedInterval.carrier_eq, bs, ms] at hu hv <;>
    grind

theorem recognized : T.recognizes JudgementTableau.labels_finite σ P := by
  apply (emptyContinuation_recognizes_iff (Clock := Nat) Set.univ root σ P).2
  apply (inputTableau_recognizes_iff Set.univ root σ P stable).2
  exact (p_iff_zero _).2 rfl

/-- The full finite-tableau forward theorem is applied without supplying
an independent whole-signal right-continuity premise. -/
theorem actual_forward :
    ∃ aug, T.TypedProjectsTo aug σ ∧
      (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).PrelimReachesState aug
        (T.prelimGoal (withEmptyContinuation_ready _ _ ready) 1) := by
  apply prelim_stateGoal_forward_of_continuousInitialFlow (Clock := Nat)
    Set.univ root Set.finite_univ (by simp) _ σ direct full starts_with_flow
    continuous_flows functions_continuous P recognized
  intro a sub
  cases sub
  rfl

/-- In the actual finite graph, each valid closed early final singleton
can exit to the empty continuation with all shared real coordinates fixed.
This does not assert that arbitrary automaton jumps preserve real values. -/
theorem singleton_jump_preserves_real
    (a : (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).State)
    (hf : a.val.1.val ∈ (inputTableau (Clock := Nat) Set.univ root).final)
    (hne : a.val.1.val ≠ emptyMode)
    (ht : a.val.2 (.inl T.globalClock) < 1) (closed : a.val.2 T.bit = 1) :
    ∃ b, (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).DiscreteStep a b ∧
      b.val.1.val = emptyMode ∧
      ∀ x : T.realVariables, b.val.2 (.inl (.inl x)) = a.val.2 (.inl (.inl x)) := by
  let v : T.TypedVar → ℝ := fun x => match x with
    | .inl y => a.val.2 (.inl y)
    | .inr _ => 0
  let q : T.states := ⟨emptyMode, Or.inl rfl⟩
  have hem : T.label q.val = ∅ := empty_label Set.univ root
  have inv : (q, v) ∈ (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).invariant := by
    refine ⟨Or.inl rfl, fun _ => ht.le, ?_, ?_⟩
    · intro p hp; rw [hem] at hp; exact hp.elim
    · intro m hm; rw [hem] at hm; exact hm.elim
  let b := (⟨(q, v), inv⟩ : (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).State)
  refine ⟨b, ?_, rfl, fun _ => rfl⟩
  let edge := (a.val.1, emptyIncoming (Clock := Nat), q)
  have he : edge ∈ (T.prelimAutomaton (withEmptyContinuation_ready _ _ ready) 1).edge :=
    final_empty_edge Set.univ root _ hf hne
  refine ⟨⟨edge, he⟩, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl,
    ?_, fun _ => ⟨closed, rfl⟩, ?_⟩
  · intro g hg; exact hg.elim
  · intro c; rfl
  · change Section3.Local.terminal ∈ T.label q.val → _
    rw [hem]
    simp
  · intro _ p hp; exact a.property.2.2.1 p hp

run_elab do
  for name in #[``full, ``initial_equals_first_curve, ``continuous_flows,
      ``wellBehaved_system, ``signal_regularity_is_derived, ``recognized,
      ``actual_forward, ``singleton_jump_preserves_real] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end DirectInitialFlowChecks
