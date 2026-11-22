import STLTableaux.Automata.Execution.FlowConcatenation
import STLTableaux.Automata.Composition.SharedParallelConstruction

/-! Trajectory checks for hybrid automata. The relation that adds `t²` to the
entry value fails closure under restriction of continuous transitions. -/
namespace HybridTrajectoryChecks
open STLTableau STLTableau.HybridAutomaton

def constant : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ _ => False

def state : constant.State := ⟨((), fun _ => 0), Set.mem_univ _⟩

theorem step (r : NNReal) : constant.ContinuousStep state state r (fun _ _ => 0) :=
  ⟨rfl, rfl, rfl, fun _ => ⟨rfl, Set.mem_univ _⟩⟩

/-- No separate FlowAdd premise is supplied. -/
example : constant.ContinuousStep state state (1 + 2 : NNReal)
    (ContinuousStep.concatCurve 1 2 (fun _ _ => 0) (fun _ _ => 0)) :=
  (step 1).concat (step 2)

example : constant.ContinuousStep
    ((step 2).stateAt ⟨1, by norm_num⟩) state (2 - 1 : NNReal)
    (HybridFlow.suffixCurve (fun _ _ => 0) 1 (by norm_num : (1 : NNReal) ≤ 2)) :=
  (step 2).suffixStep 1 (by norm_num)

def badFlow (s : Unit × (Unit → ℝ)) (t : NNReal) (v : Unit → ℝ) : Prop :=
  v () = s.2 () + (t : ℝ) ^ 2

theorem bad_not_trajectory_closed : ¬ HybridFlow.Closed badFlow Set.univ := by
  intro closed
  let γ : HybridFlow.Curve Unit 2 := fun t _ => t.val ^ 2
  have full : HybridFlow.Evolves badFlow Set.univ () γ := by
    intro t
    refine ⟨?_, Set.mem_univ _⟩
    change t.val ^ 2 = (0 : ℝ) ^ 2 + t.val ^ 2
    ring
  have restarted := closed.suffix full 1 (by norm_num)
  have half := (restarted ⟨1 / 2, by norm_num⟩).1
  change ((1 : ℝ) + 1 / 2) ^ 2 = (1 + 0) ^ 2 + (1 / 2) ^ 2 at half
  norm_num at half

run_elab do
  for n in #[``step, ``bad_not_trajectory_closed] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end HybridTrajectoryChecks
