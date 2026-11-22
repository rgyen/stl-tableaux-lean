import STLTableaux.Automata.Execution.WellBehaved

/-! A direct-start observed prefix need not realize its signal's suffix.
This tests only the distinction between prefix and full SYSTEM witnesses;
it asserts no finite-tableau no-goal result or model-checking counterexample. -/
namespace UnobservedSuffixChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 0}
  invariant := {s | s.2 () = 0}
  flow := fun _ _ v => ∀ x, v x = 0
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total; exact total)
    (by intro q v a b r s first second; exact second)
  jump := fun _ _ _ => False

def zeroState : H.State := ⟨((), fun _ => 0), rfl⟩
noncomputable def σ : FiniteSignal Unit :=
  ⟨2, by norm_num, fun t _ => if t.val < 1 then 0 else 1⟩

noncomputable def e : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := zeroState
  initial_mem := rfl
  start := fun _ => zeroState
  finish := fun _ => zeroState
  boundary := fun i => (i.val : ℝ) / 2
  first_zero := by norm_num
  increasing := by
    intro i j hij
    have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
    dsimp only
    linarith
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1 / 2
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨fun _ => rfl, rfl⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := by
    intro i t ht
    fin_cases i
    have upper : t.val < 1 := by
      have h := ht.2
      norm_num at h
      linarith
    funext x
    simp [σ, upper]

theorem direct_start : e.initialState = e.start ⟨0, e.nonempty⟩ := rfl
theorem observed_prefix : H.IsPrelimPrefix σ := ⟨e⟩

theorem prefix_stop : e.boundary ⟨e.count, by omega⟩ = (1 : ℝ) / 2 := by
  unfold e
  norm_num

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  have same : γ = fun _ _ => 0 := by
    funext t x
    exact (evolves t).1 x
  rw [same]
  exact continuous_const

theorem no_full_system_witness : ¬ H.IsPrelimTrajectory σ := by
  intro trajectory
  let t : σ.Time := ⟨1, by norm_num, by norm_num [σ]⟩
  obtain ⟨q, inv⟩ := trajectory.invariant_at t
  change (if (1 : ℝ) < 1 then 0 else 1) = 0 at inv
  norm_num at inv

theorem prefix_does_not_imply_full :
    H.IsPrelimPrefix σ ∧ ¬ H.IsPrelimTrajectory σ :=
  ⟨observed_prefix, no_full_system_witness⟩

run_elab do
  for name in #[``direct_start, ``observed_prefix, ``prefix_stop,
      ``continuous_flows, ``no_full_system_witness, ``prefix_does_not_imply_full] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end UnobservedSuffixChecks
