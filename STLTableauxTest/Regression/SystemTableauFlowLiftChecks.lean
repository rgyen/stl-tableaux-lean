import STLTableaux.Automata.Composition.SystemTableauFlowLift
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition
import STLTableaux.Automata.Translation.InitialAtomRetention

/-! A recognizing run of the finite tableau supplies the atomic label for a
product flow. The one-flow product execution covers the whole signal,
and its final state uses the closed endpoint of the system flow. -/
namespace SystemTableauFlowLiftChecks
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
    (by intro q v a b r s first total x
        dsimp only [Prod.snd] at *
        rw [total x, first x]; push_cast; ring)
    (by intro q v a b r s first second x
        dsimp only [Prod.snd] at *
        rw [second x, first x]; push_cast; ring)
  jump := fun _ _ _ => False

def zero : H.State := ⟨((), fun _ => 0), Set.mem_univ _⟩
def one : H.State := ⟨((), fun _ => 1), Set.mem_univ _⟩
noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => t.val⟩
noncomputable def f : ObservedFlow H σ where
  start := zero
  finish := one
  beginTime := 0
  endTime := 1
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t _ => t.val
  step := ⟨rfl, rfl, rfl, fun _ =>
    ⟨fun _ => by simp [zero]; rfl, Set.mem_univ _⟩⟩
  observe := by intro t ht; funext x; simp [σ]

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : T.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp))
def q : T.states := ⟨emptyMode, Or.inl rfl⟩
theorem empty_labels : T.label q.val = ∅ := empty_label Set.univ root

def bs : Fin 2 → ℝ := ![0, 1]
def ms : Fin 2 → Marker := ![●, ●]
def P : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i; norm_num [bs] at hi) rfl rfl

theorem labels : ∀ l ∈ T.label q.val,
    l.holds σ P (fun _ => 0) ⟨0, by decide⟩ := by
  intro l hl
  rw [empty_labels] at hl
  exact hl.elim

noncomputable def v : T.TypedVar → ℝ :=
  T.entryValue f.beginTime (fun _ => 0) (f.curve ⟨0, by simp⟩)
    (P.interval ⟨0, by decide⟩).leftBoundary

theorem actual_monitor_cell :
    ∃ a b : (T.prelimAutomaton ready σ.horizon).State,
      a.val = (q, v) ∧
      b.val = (q, T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩) ∧
      (T.prelimAutomaton ready σ.horizon).ContinuousStep a b f.duration
        (T.clockLiftCurve v f.curve) := by
  apply T.monitor_flow_over_system_cell H ready f continuous_flows P ⟨0, by decide⟩
    rfl rfl q (fun _ => 0) (fun _ => 0) labels
  · intro a ha; rw [empty_labels] at ha; exact ha.elim
  · intro a ha; rw [empty_labels] at ha; exact ha.elim

def x : T.realVariables := ⟨(), Set.mem_univ _⟩

theorem actual_endpoint_real :
    T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩ (.inl (.inl x)) = 1 := rfl

theorem actual_entry_real : v (.inl (.inl x)) = 0 := rfl

theorem actual_endpoint_not_entry :
    T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩ (.inl (.inl x)) ≠
      v (.inl (.inl x)) := by
  rw [actual_endpoint_real, actual_entry_real]
  norm_num

theorem actual_endpoint_clock :
    T.clockLiftCurve v f.curve ⟨f.duration, by simp⟩ (.inl T.globalClock) = 1 := by
  norm_num [Tableau.clockLiftCurve, Tableau.forwardCurveValue, v, Tableau.entryValue,
    Tableau.globalClock, f]

theorem stable : σ.StablePartition root.val P := by
  intro i χ sub u w hu hw
  cases sub
  change (u.val ≥ 0) ↔ (w.val ≥ 0)
  exact iff_of_true u.property.1 w.property.1

theorem recognized : T.recognizes JudgementTableau.labels_finite σ P := by
  apply (emptyContinuation_recognizes_iff (Clock := Nat) Set.univ root σ P).2
  apply (inputTableau_recognizes_iff Set.univ root σ P stable).2
  change (0 : ℝ) ≥ 0
  rfl

/-- Extract a genuinely atom-labelled first state from an actual recognized
run. This is stronger than the empty-mode baseline above. -/
theorem recognized_atomic_source :
    ∃ (q : T.states) (β : ClockValuation Nat),
      Section3.Local.predicate (.plain (.atom p)) ∈ T.label q.val ∧
      ∀ l ∈ T.label q.val, l.holds σ P β ⟨0, by decide⟩ := by
  obtain ⟨path, run, _, allα⟩ := recognized
  let q : T.states := ⟨path.firstState, ready.initial_states _ run.2⟩
  refine ⟨q, path.firstIncoming.resets.apply (fun _ => 0), ?_, ?_⟩
  · exact InitialAtomRetention.empty_atom_initial Set.univ p root rfl
      path.firstIncoming path.firstState run.2
  · have h := allα (fun _ => 0)
    cases path with
    | last e s => exact h.2
    | step e s tail => exact h.1.2

theorem recognized_atomic_initial_source :
    ∃ (q : T.states) (l : EdgeLabel Nat),
      (l, q.val) ∈ T.initial ∧
      (∀ g ∈ l.guards, g.holds (fun _ => 0)) ∧
      Section3.Local.predicate (.plain (.atom p)) ∈ T.label q.val ∧
      ∀ loc ∈ T.label q.val,
        loc.holds σ P (l.resets.apply (fun _ => 0)) ⟨0, by decide⟩ := by
  obtain ⟨path, run, _, allα⟩ := recognized
  let q : T.states := ⟨path.firstState, ready.initial_states _ run.2⟩
  refine ⟨q, path.firstIncoming, run.2, ?_, ?_, ?_⟩
  · have h := allα (fun _ => 0)
    cases path with
    | last e s => exact h.1
    | step e s tail => exact h.1.1
  · exact InitialAtomRetention.empty_atom_initial Set.univ p root rfl
      path.firstIncoming path.firstState run.2
  · have h := allα (fun _ => 0)
    cases path with
    | last e s => exact h.2
    | step e s tail => exact h.1.2

theorem actual_atomic_monitor_cell :
    ∃ (q : T.states) (β : ClockValuation Nat)
      (a b : (T.prelimAutomaton ready σ.horizon).State),
      Section3.Local.predicate (.plain (.atom p)) ∈ T.label q.val ∧
      a.val.1 = q ∧ b.val.1 = q ∧
      b.val.2 (.inl (.inl x)) = 1 ∧
      b.val.2 (.inl T.globalClock) = 1 ∧
      (T.prelimAutomaton ready σ.horizon).ContinuousStep a b f.duration
        (T.clockLiftCurve
          (T.entryValue f.beginTime β (f.curve ⟨0, by simp⟩)
            (P.interval ⟨0, by decide⟩).leftBoundary) f.curve) := by
  obtain ⟨q, β, atom, labels⟩ := recognized_atomic_source
  have atom_eq (a : AtomicProposition Unit)
      (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label q.val) : a = p := by
    have sub := emptyContinuation_atom_subformula Set.univ root q a ha
    cases sub
    rfl
  obtain ⟨a, b, entry, finish, step⟩ :=
    T.monitor_flow_over_system_cell H ready f continuous_flows P ⟨0, by decide⟩
      rfl rfl q β β labels
      (by intro a ha; rw [atom_eq a ha]; rfl)
      (by intro a ha; rw [atom_eq a ha]; exact continuous_apply (0 : Fin 1))
  refine ⟨q, β, a, b, atom, ?_, ?_, ?_, ?_, step⟩
  · exact congrArg Prod.fst entry
  · exact congrArg Prod.fst finish
  · rw [show b.val.2 = _ from congrArg Prod.snd finish]; rfl
  · rw [show b.val.2 = _ from congrArg Prod.snd finish]
    norm_num [Tableau.clockLiftCurve, Tableau.forwardCurveValue, Tableau.entryValue,
      Tableau.globalClock, f]

theorem actual_atomic_product_cell :
    ∃ (q : T.states) (β : ClockValuation Nat)
      (a b : (T.systemTableauAutomaton H ready σ.horizon).State),
      Section3.Local.predicate (.plain (.atom p)) ∈ T.label q.val ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName a = zero ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b = one ∧
      (T.systemTableauAutomaton H ready σ.horizon).ContinuousStep a b f.duration
        (fun u => T.joinValuation (f.curve u)
          (T.clockLiftCurve
            (T.entryValue f.beginTime β (f.curve ⟨0, by simp⟩)
              (P.interval ⟨0, by decide⟩).leftBoundary) f.curve u)) := by
  obtain ⟨q, β, atom, labels⟩ := recognized_atomic_source
  have atom_eq (a : AtomicProposition Unit)
      (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label q.val) : a = p := by
    have sub := emptyContinuation_atom_subformula Set.univ root q a ha
    cases sub
    rfl
  obtain ⟨a, b, initial, final, _, _, step⟩ :=
    T.systemTableau_flow_over_cell H ready f continuous_flows P ⟨0, by decide⟩
      rfl rfl q β β labels
      (by intro a ha; rw [atom_eq a ha]; rfl)
      (by intro a ha; rw [atom_eq a ha]; exact continuous_apply (0 : Fin 1))
  exact ⟨q, β, a, b, atom, initial, final, step⟩

theorem actual_atomic_initial_product_cell :
    ∃ (q : T.states) (l : EdgeLabel Nat)
      (a b : (T.systemTableauAutomaton H ready σ.horizon).State),
      (l, q.val) ∈ T.initial ∧
      Section3.Local.predicate (.plain (.atom p)) ∈ T.label q.val ∧
      a.val ∈ (T.systemTableauAutomaton H ready σ.horizon).initial ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName a = zero ∧
      H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b = one ∧
      (T.systemTableauAutomaton H ready σ.horizon).ContinuousStep a b f.duration
        (fun u => T.joinValuation (f.curve u)
          (T.clockLiftCurve
            (T.entryValue f.beginTime (l.resets.apply (fun _ => 0))
              (f.curve ⟨0, by simp⟩) (P.interval ⟨0, by decide⟩).leftBoundary)
            f.curve u)) := by
  obtain ⟨q, l, initial, guards, atom, labels⟩ := recognized_atomic_initial_source
  have atom_eq (a : AtomicProposition Unit)
      (ha : Section3.Local.predicate (.plain (.atom a)) ∈ T.label q.val) : a = p := by
    have sub := emptyContinuation_atom_subformula Set.univ root q a ha
    cases sub
    rfl
  obtain ⟨a, b, init, left, right, step⟩ :=
    T.systemTableau_initial_flow_over_first_cell H ready f continuous_flows P
      (by decide) rfl rfl (show f.start.val ∈ H.initial from rfl)
      q l initial (fun _ => 0) guards labels
      (by intro a ha; rw [atom_eq a ha]; rfl)
      (by intro a ha; rw [atom_eq a ha]; exact continuous_apply (0 : Fin 1))
  exact ⟨q, l, a, b, initial, atom, init, left, right, step⟩

/-- A concrete single-flow product trajectory (no goal claim). Its signal
is defined from the actual joint curve on [0,1), not from sigma at 1. -/
theorem actual_one_flow_product :
    ∃ aug : FiniteSignal T.CompositionVar,
      (T.systemTableauAutomaton H ready σ.horizon).IsPrelimTrajectory aug ∧
      ∀ (t : aug.Time) (x : Unit), aug.value t (T.systemCoordinate x) = t.val := by
  obtain ⟨q, l, a, b, _, _, init, _, _, step⟩ := actual_atomic_initial_product_cell
  let v := T.entryValue f.beginTime (l.resets.apply (fun _ => 0))
    (f.curve ⟨0, by simp⟩) (P.interval ⟨0, by decide⟩).leftBoundary
  let γ := fun u => T.joinValuation (f.curve u) (T.clockLiftCurve v f.curve u)
  let aug : FiniteSignal T.CompositionVar :=
    ⟨1, by norm_num, fun t => γ ⟨t.val, t.property.1, t.property.2.le⟩⟩
  let e : (T.systemTableauAutomaton H ready σ.horizon).PrelimExecution aug := {
    count := 1
    nonempty := by decide
    initialState := a
    initial_mem := init
    start := fun _ => a
    finish := fun _ => b
    boundary := fun i => i.val
    first_zero := by norm_num
    increasing := by
      intro i j hij
      change (i.val : ℝ) < (j.val : ℝ)
      exact_mod_cast (show i.val < j.val from hij)
    last_le_horizon := by norm_num [aug]
    duration := fun _ => 1
    duration_eq := by intro i; fin_cases i; norm_num
    curve := fun _ => γ
    continuousStep := fun _ => step
    initialSteps := .refl
    discreteSteps := by intro i hi; have := i.isLt; omega
    signal_eq := by
      intro i t ht
      fin_cases i
      change γ _ = γ _
      congr 1
      apply Subtype.ext
      simp }
  refine ⟨aug, ⟨e, ?_⟩, ?_⟩
  · unfold PrelimExecution.ReachesHorizon
    dsimp only [e]
    norm_num [aug]
  · intro t x
    rfl

run_elab do
  for name in #[``actual_monitor_cell, ``recognized_atomic_source,
      ``recognized_atomic_initial_source, ``actual_atomic_monitor_cell,
      ``actual_atomic_product_cell, ``actual_atomic_initial_product_cell,
      ``actual_one_flow_product,
      ``actual_endpoint_real, ``actual_endpoint_not_entry, ``actual_endpoint_clock] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end SystemTableauFlowLiftChecks
