import STLTableaux.Automata.Recognition.PrelimPartitionConnection
import STLTableaux.Automata.Execution.BoundedZeroTimeExtension

/-! Compress only actually bounded SYSTEM boundary blocks. Artificial cuts
are idles; the bound is a certificate on the supplied execution, not inferred
from arbitrary reflexive-transitive reachability. -/
namespace STLTableau.HybridAutomaton.PrelimExecution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var} (e : H.PrelimExecution σ)
variable (full : e.ReachesHorizon) (R : IntervalPartition σ.domain)
variable (fine : R.FinerThan (e.fullFlowPartition full))

theorem cell_action_zeroTimeExtension (n : ℕ)
    (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (i j : Fin R.size) (adj : i.val + 1 = j.val) :
    e.cellExitState full R fine i = e.cellEntryState full R fine j ∨
      (H.boundedZeroTimeExtension n).DiscreteStep
        (e.cellExitState full R fine i) (e.cellEntryState full R fine j) := by
  rcases e.cell_connector_cases full R fine i j adj with idle | ⟨k, live, leave, enter⟩
  · exact Or.inl idle
  · right
    rw [leave, enter]
    exact (H.extension_step_iff n).mpr (Or.inr (bound k live))

/-- The extension changes no physical entry state or choice of flow owner. -/
theorem cellEntry_inZeroTimeExtension (n : ℕ) (i : Fin R.size) :
    (e.inZeroTimeExtension H n).cellEntryState full R fine i =
      e.cellEntryState full R fine i := rfl

theorem cellExit_inZeroTimeExtension (n : ℕ) (i : Fin R.size) :
    (e.inZeroTimeExtension H n).cellExitState full R fine i =
      e.cellExitState full R fine i := rfl

/-- The positive provider retains the same curve and physical endpoints. -/
theorem refinedObservedFlow_inZeroTimeExtension (n : ℕ) (i : Fin R.size)
    (positive : 0 < (STLTableau.Judgement.duration R i : ℝ)) :
    ((e.inZeroTimeExtension H n).refinedObservedFlow full R fine i positive).start =
        (e.refinedObservedFlow full R fine i positive).start ∧
      ((e.inZeroTimeExtension H n).refinedObservedFlow full R fine i positive).finish =
        (e.refinedObservedFlow full R fine i positive).finish ∧
      ((e.inZeroTimeExtension H n).refinedObservedFlow full R fine i positive).curve =
        (e.refinedObservedFlow full R fine i positive).curve := ⟨rfl, rfl, rfl⟩

/-- The action API directly on the extended witness uses the same cells. -/
theorem extended_cell_action (n : ℕ)
    (bound : ∀ (k : Fin e.count) (live : k.val + 1 < e.count),
      H.BoundedZeroTime n (e.finish k) (e.start ⟨k.val + 1, live⟩))
    (i j : Fin R.size) (adj : i.val + 1 = j.val) :
    (e.inZeroTimeExtension H n).cellExitState full R fine i =
        (e.inZeroTimeExtension H n).cellEntryState full R fine j ∨
      (H.boundedZeroTimeExtension n).DiscreteStep
        ((e.inZeroTimeExtension H n).cellExitState full R fine i)
        ((e.inZeroTimeExtension H n).cellEntryState full R fine j) :=
  e.cell_action_zeroTimeExtension full R fine n bound i j adj

run_elab do
  for name in #[``cell_action_zeroTimeExtension, ``cellEntry_inZeroTimeExtension,
      ``cellExit_inZeroTimeExtension, ``refinedObservedFlow_inZeroTimeExtension,
      ``extended_cell_action] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.HybridAutomaton.PrelimExecution
