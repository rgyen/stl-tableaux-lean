import STLTableaux.Automata.Execution.BoundedZeroTimeExtension

namespace BoundedZeroTimeExtensionChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton (Fin 3) Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(0, (), 1), (1, (), 2)}
  initial := {s | s.1 = 0}
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ _ => True

def s (q : Fin 3) : H.State := ⟨(q, fun _ => 0), Set.mem_univ _⟩

theorem step01 : H.DiscreteStep (s 0) (s 1) := by
  exact ⟨⟨(0, (), 1), by simp [H]⟩, rfl, rfl, trivial⟩

theorem step12 : H.DiscreteStep (s 1) (s 2) := by
  exact ⟨⟨(1, (), 2), by simp [H]⟩, rfl, rfl, trivial⟩

theorem no_original02 : ¬ H.DiscreteStep (s 0) (s 2) := by
  rintro ⟨e, hs, ht, _⟩
  have he := e.property
  change e.val = (0, (), 1) ∨ e.val = (1, (), 2) at he
  rcases he with he | he <;> simp_all [s]

theorem path02 : H.BoundedZeroTime 2 (s 0) (s 2) := by
  refine ⟨2, ![s 0, s 1, s 2], by decide, le_rfl, rfl, rfl, ?_⟩
  intro i
  fin_cases i
  · exact step01
  · exact step12

theorem shortcut02 : (H.boundedZeroTimeExtension 2).DiscreteStep (s 0) (s 2) :=
  (H.extension_step_iff 2).mpr (Or.inr path02)

theorem no_shortcut02_at_one :
    ¬ (H.boundedZeroTimeExtension 1).DiscreteStep (s 0) (s 2) := by
  intro step
  rcases (H.extension_step_iff 1).mp step with old | ⟨k, v, hk, hn, first, last, steps⟩
  · exact no_original02 old
  · have he : k = 1 := by omega
    subst k
    have direct := steps 0
    change H.DiscreteStep (v 0) (v (Fin.last 1)) at direct
    exact no_original02 (first ▸ last ▸ direct)

def σ : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩

def shortcutExecution : (H.boundedZeroTimeExtension 2).PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := s 0
  initial_mem := rfl
  start := fun _ => s 2
  finish := fun _ => s 2
  boundary := fun i => if i.val = 0 then 0 else 1
  first_zero := rfl
  increasing := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := le_rfl
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩
  initialSteps := .single shortcut02
  discreteSteps := by intro i hi; exact False.elim (by omega)
  signal_eq := fun _ _ _ => rfl

def originalExecution : H.PrelimExecution σ :=
  shortcutExecution.unfoldZeroTimeExtension H 2

example : originalExecution.count = shortcutExecution.count := rfl
example : originalExecution.start = shortcutExecution.start := rfl
example : originalExecution.finish = shortcutExecution.finish := rfl
example : originalExecution.boundary = shortcutExecution.boundary := rfl
example : originalExecution.curve = shortcutExecution.curve := rfl

theorem same_signal : H.IsPrelimTrajectory σ :=
  (H.boundedZeroTimeExtension_trajectory_iff 2 σ).mp ⟨shortcutExecution, rfl⟩

theorem goal_preserved : H.PrelimReachesState σ {s 2} := by
  apply (H.boundedZeroTimeExtension_reachesState_iff 2 σ {s 2}).mp
  exact ⟨shortcutExecution, s 2, rfl, shortcutExecution.visits_finalState⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``no_original02, ``path02, ``shortcut02, ``no_shortcut02_at_one,
      ``same_signal, ``goal_preserved] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end BoundedZeroTimeExtensionChecks
