import STLTableaux.Automata.Composition.SystemTableauComposition
import STLTableaux.Automata.Translation.InitialAtomRetention
import STLTableaux.Automata.Execution.WellBehaved
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

/-! Regression for the initial post-atom guard on an actual finite tableau.
With the manuscript convention, the initial reset is followed by a flow observing
`x=1` from time zero. The signal cannot satisfy the atom `x ≤ 0` in the
initial tableau label, so the absence of a product execution is expected. -/
namespace InitialPostAudit
open STLTableau STLTableau.HybridAutomaton
open STLTableau.Section4 STLTableau.Section4.Finiteness

theorem zero_chain_atoms {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.prelimAutomaton h τ).State} (zero : a.val.2 T.dwell = 0)
    (steps : Relation.ReflTransGen (T.prelimAutomaton h τ).DiscreteStep a b) :
    T.atomsAt a.val.1 b.val.2 := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp steps with same | chain
  · subst b
    exact a.property.2.2.1
  · obtain ⟨mid, first, rest⟩ := Relation.TransGen.head'_iff.mp chain
    obtain ⟨edge, _, _, _, _, _, _, _, dwell, _, polarity, post⟩ := first
    have opened := (polarity zero).2
    have stuck : ∀ s, ¬ (T.prelimAutomaton h τ).DiscreteStep mid s := by
      intro s step
      obtain ⟨_, _, _, _, _, _, _, _, _, _, next, _⟩ := step
      have closed := (next dwell).1
      linarith
    have same : b = mid := (Relation.reflTransGen_iff_eq stuck).mp rest
    subst b
    exact post opened

def H : HybridAutomaton Bool Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(false, (), true)}
  initial := {s | s.1 = false ∧ s.2 () = 0}
  invariant := Set.univ
  flow := fun s _ v => s.1 = true ∧ v = s.2 ∧ v () = 1
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total; exact ⟨first.1, total.2.1.trans first.2.1.symm, total.2.2⟩)
    (by intro q v a b r s first second; exact ⟨first.1, second.2.1.trans first.2.1, second.2.2⟩)
  jump := fun _ _ s' => s'.2 () = 1

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => -v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : T.TranslationReady :=
  withEmptyContinuation_ready Set.univ root
    (finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp))

theorem no_product_execution (τ : ℝ) (aug : FiniteSignal T.CompositionVar) :
    ¬ Nonempty ((T.systemTableauAutomaton H ready τ).PrelimExecution aug) := by
  rintro ⟨e⟩
  let A := T.prelimAutomaton ready τ
  let i : Fin e.count := ⟨0, e.nonempty⟩
  let a := H.rightStateOn A T.systemVarName T.tableauVarName e.initialState
  let b := H.rightStateOn A T.systemVarName T.tableauVarName (e.start i)
  have initial : a.val ∈ A.initial := e.initial_mem.2
  obtain ⟨l, initialLabel, v, guards, reset, dwell, bit⟩ := initial
  have atomLabel := InitialAtomRetention.empty_atom_initial (Clock := Nat)
    Set.univ p root rfl l a.val.1.val initialLabel
  have steps := H.parallelOn_jumpClosure_right A T.systemVarName T.tableauVarName e.initialSteps
  have atomAt := zero_chain_atoms T ready τ dwell steps p atomLabel
  obtain ⟨support, inequality⟩ := atomAt
  let x : T.realVariables := ⟨(), support ⟨0, by decide⟩⟩
  have system := H.parallelOn_continuous_left A T.systemVarName T.tableauVarName
    (e.continuousStep i)
  have atZero := ((system.2.2.2 ⟨0, by simp⟩).1).2.2
  rw [system.2.1] at atZero
  have shared := H.parallelOn_shared_value A T.systemVarName T.tableauVarName (e.start i)
    (x := ()) (y := .inl (.inl x)) rfl
  have value : b.val.2 (.inl (.inl x)) = 1 := shared.symm.trans atZero
  change -b.val.2 (.inl (.inl x)) ≥ (0 : ℝ) at inequality
  rw [value] at inequality
  norm_num at inequality

def before : H.State := ⟨(false, fun _ => 0), Set.mem_univ _⟩
def after : H.State := ⟨(true, fun _ => 1), Set.mem_univ _⟩
theorem jump : H.DiscreteStep before after := ⟨⟨(false, (), true), rfl⟩, rfl, rfl, rfl⟩
noncomputable def σ : FiniteSignal Unit :=
  ⟨1, by norm_num, fun _ _ => 1⟩

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
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨⟨rfl, rfl, rfl⟩, Set.mem_univ _⟩⟩
  initialSteps := .single jump
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := fun _ _ _ => rfl

theorem full_system_trajectory : H.IsPrelimTrajectory σ := by
  refine ⟨execution, ?_⟩
  unfold PrelimExecution.ReachesHorizon
  dsimp only [execution]
  norm_num [σ]

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  have same : γ = fun _ => γ ⟨0, by simp⟩ := by
    funext u
    exact (evolves u).1.2.1
  rw [same]
  exact continuous_const

theorem system_wellBehaved : execution.WellBehaved root.val := by
  apply execution.wellBehaved_of_continuousFlows root.val continuous_flows
  intro a sub
  cases sub
  exact (continuous_apply (0 : Fin 1)).neg

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
  rfl

theorem root_not_recognized : ¬ T.recognizes JudgementTableau.labels_finite σ P := by
  intro rec
  have sat := (inputTableau_recognizes_iff Set.univ root σ P stable).1
    ((emptyContinuation_recognizes_iff (Clock := Nat) Set.univ root σ P).1 rec)
  change -(1 : ℝ) ≥ 0 at sat
  norm_num at sat

theorem initial_boundary_agreement :
    H.IsPrelimTrajectory σ ∧ execution.WellBehaved root.val ∧
      ¬ T.recognizes JudgementTableau.labels_finite σ P ∧
      ∀ aug, ¬ Nonempty ((T.systemTableauAutomaton H ready 1).PrelimExecution aug) :=
  ⟨full_system_trajectory, system_wellBehaved, root_not_recognized, no_product_execution 1⟩

run_elab do
  for name in #[``zero_chain_atoms, ``no_product_execution, ``full_system_trajectory,
      ``continuous_flows, ``system_wellBehaved, ``root_not_recognized, ``initial_boundary_agreement] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end InitialPostAudit
