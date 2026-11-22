import STLTableaux.Semantics.Stability.StabilityRefinement

open STLTableau
open scoped STL

-- The universal property fixes the direction: coarsest common refinement.
example {D : Set ℝ} (P Q : IntervalPartition D) :
    ∃ R : IntervalPartition D, R ⊑ P ∧ R ⊑ Q ∧
      ∀ S : IntervalPartition D, S ⊑ P → S ⊑ Q → S ⊑ R :=
  P.exists_common_refinement Q

-- Boundary markers must preserve a singleton intersection at a shared endpoint.
example : (MarkedInterval.inter ⟨0, 1, .closed, .closed⟩
    ⟨1, 2, .closed, .open⟩).carrier = {1} := by
  rw [MarkedInterval.carrier_inter]
  ext x
  simp only [Set.mem_inter_iff, MarkedInterval.mem_carrier,
    MarkedInterval.mem_iff, Marker.Includes, Set.mem_singleton_iff]
  constructor <;> intro h <;> grind

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``MarkedInterval.carrier_inter,
    ``IntervalPartition.exists_common_refinement,
    ``FiniteSignal.FullyStable.and,
    ``FiniteSignal.exists_common_stable_refinement,
    ``FiniteSignal.HasFiniteVariability.and]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
