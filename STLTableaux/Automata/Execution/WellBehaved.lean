import STLTableaux.Automata.Execution.PrelimExecution
import Mathlib.Topology.Instances.Real.Lemmas

/-! Well-behavedness is local to each closed continuous evolution. It does
not compare valuations across a discrete jump. -/
namespace STLTableau
variable {Var : Type*} {r : NNReal}

/-- Each atomic function is right-continuous on this evolution's own
domain `[0,r]`. The value at zero is `γ(0)`, not a separate observation. -/
def WellBehaved (γ : HybridFlow.Curve Var r) (φ : Formula Var) : Prop :=
  ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
    ∀ t, ContinuousWithinAt
      (fun u => a.function (fun i => γ u (a.arguments i))) (Set.Ici t) t

/-- Continuous flows and continuous atomic functions imply flow-local
well-behavedness. No signal/curve equality or jump premise is needed. -/
theorem wellBehaved_of_continuous (γ : HybridFlow.Curve Var r) (φ : Formula Var)
    (hγ : Continuous γ)
    (hf : ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
      Continuous a.function) : WellBehaved γ φ := by
  intro a sub t
  exact ((hf a sub).comp
    (continuous_pi (fun i => (continuous_apply (a.arguments i)).comp hγ))).continuousWithinAt

/-- Non-strict atomic truth immediately after the start extends to the
start of the SAME flow. Nothing is concluded about an earlier singleton. -/
theorem WellBehaved.atom_at_zero {γ : HybridFlow.Curve Var r} {φ : Formula Var}
    (hw : WellBehaved γ φ) (a : AtomicProposition Var) (ha : a.relation = .ge)
    (sub : Formula.IsSubformula (.atom a) φ) (hr : 0 < (r : ℝ))
    (body : ∀ u, 0 < u.val → a.Holds (γ u)) :
    a.Holds (γ ⟨0, by simp⟩) := by
  suffices nonneg : 0 ≤ a.function (fun i => γ ⟨0, by simp⟩ (a.arguments i)) by
    simpa [AtomicProposition.Holds, ha, RealRelation.Holds] using nonneg
  by_contra! negative
  obtain ⟨δ, hδ, close⟩ := Metric.continuousWithinAt_iff.mp (hw a sub ⟨0, by simp⟩)
    (-(a.function (fun i => γ ⟨0, by simp⟩ (a.arguments i)))) (by linarith)
  obtain ⟨u, positive, upper⟩ := exists_between (lt_min hδ hr)
  let v : Set.Icc (0 : ℝ) r := ⟨u, positive.le, (lt_min_iff.mp upper).2.le⟩
  have nonneg : 0 ≤ a.function (fun i => γ v (a.arguments i)) := by
    simpa [AtomicProposition.Holds, ha, RealRelation.Holds] using body v positive
  have distance : dist v (⟨0, by simp⟩ : Set.Icc (0 : ℝ) r) < δ := by
    change |u - 0| < δ
    simpa [abs_of_nonneg positive.le] using (lt_min_iff.mp upper).1
  have near := close (show v ∈ Set.Ici ⟨0, by simp⟩ from positive.le) distance
  rw [Real.dist_eq, abs_lt] at near
  linarith [near.2]

namespace HybridAutomaton
variable {Mode Label : Type*} (H : HybridAutomaton Mode Label Var)

/-- Continuity of the individual evolutions permitted by the flow
condition. This places no continuity requirement on discrete transitions. -/
def ContinuousFlows : Prop :=
  ∀ {q r} (γ : HybridFlow.Curve Var r),
    HybridFlow.Evolves H.flow H.invariant q γ → Continuous γ

namespace PrelimExecution
variable {H} {σ : FiniteSignal Var}

/-- Every continuous evolution in this particular execution is well-behaved.
This applies to prefixes too and does not constrain unobserved signal times. -/
def WellBehaved (e : H.PrelimExecution σ) (φ : Formula Var) : Prop :=
  ∀ i, STLTableau.WellBehaved (e.curve i) φ

theorem wellBehaved_of_continuous (e : H.PrelimExecution σ) (φ : Formula Var)
    (curves : ∀ i, Continuous (e.curve i))
    (functions : ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
      Continuous a.function) : e.WellBehaved φ := by
  intro i
  exact STLTableau.wellBehaved_of_continuous (e.curve i) φ (curves i) functions

/-- The sufficient-condition lemma, with its intended flow-by-flow scope. -/
theorem wellBehaved_of_continuousFlows (e : H.PrelimExecution σ) (φ : Formula Var)
    (flows : H.ContinuousFlows)
    (functions : ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
      Continuous a.function) : e.WellBehaved φ := by
  apply e.wellBehaved_of_continuous φ _ functions
  intro i
  exact flows _ (e.continuousStep i).evolves

end PrelimExecution

/-- Every full trajectory has a flow-wise well-behaved witnessing execution.
Initial jumps may change values before the first observation. -/
theorem IsPrelimTrajectory.exists_wellBehaved_execution {σ : FiniteSignal Var}
    (trajectory : H.IsPrelimTrajectory σ) (φ : Formula Var) (flows : H.ContinuousFlows)
    (functions : ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
      Continuous a.function) :
    ∃ e : H.PrelimExecution σ, e.ReachesHorizon ∧ e.WellBehaved φ := by
  obtain ⟨e, full⟩ := trajectory
  exact ⟨e, full, e.wellBehaved_of_continuousFlows φ flows functions⟩

end HybridAutomaton

run_elab do
  for n in #[``wellBehaved_of_continuous, ``WellBehaved.atom_at_zero,
      ``HybridAutomaton.PrelimExecution.wellBehaved_of_continuous,
      ``HybridAutomaton.PrelimExecution.wellBehaved_of_continuousFlows,
      ``HybridAutomaton.IsPrelimTrajectory.exists_wellBehaved_execution] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau
