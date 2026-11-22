import STLTableaux.Automata.Execution.WellBehaved

/-! The flow-local condition includes its own start and permits zero-length
closed evolutions. No signal observation or jump condition is a premise. -/
namespace FlowWellBehavedChecks
open STLTableau

def atom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0 - 1, .ge⟩
def γ (r : NNReal) : HybridFlow.Curve Unit r := fun _ _ => 1

theorem wellBehaved_constant (r : NNReal) : WellBehaved (γ r) (.atom atom) := by
  apply wellBehaved_of_continuous _ _ continuous_const
  intro a sub
  cases sub
  exact (continuous_apply (0 : Fin 1)).sub continuous_const

theorem wellBehaved_zero_duration : WellBehaved (γ 0) (.atom atom) :=
  wellBehaved_constant 0

theorem atom_at_flow_start : atom.Holds (γ 1 ⟨0, by simp⟩) := by
  apply (wellBehaved_constant 1).atom_at_zero atom rfl (.refl _) (by norm_num)
  intro u _
  change (1 : ℝ) - 1 ≥ 0
  norm_num

run_elab do
  for n in #[``wellBehaved_constant, ``wellBehaved_zero_duration, ``atom_at_flow_start] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end FlowWellBehavedChecks
