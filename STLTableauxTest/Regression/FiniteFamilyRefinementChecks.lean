import STLTableaux.Semantics.Stability.FiniteFamilyRefinement

open STLTableau
open scoped STL

example {D : Set ℝ} (P : IntervalPartition D) :
    ∃ R : IntervalPartition D, R ⊑ P ∧
      (∀ Q ∈ (∅ : Finset (IntervalPartition D)), R ⊑ Q) ∧
      ∀ S : IntervalPartition D, S ⊑ P →
        (∀ Q ∈ (∅ : Finset (IntervalPartition D)), S ⊑ Q) → S ⊑ R :=
  P.exists_common_refinement_finset ∅

example {Var : Type*} (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (φ : Fin 3 → Formula Var) (hφ : ∀ i, σ.HasFiniteVariability (φ i)) :
    ∃ R : IntervalPartition σ.domain, R ⊑ P ∧
      ∀ i, σ.StablePartition (φ i) R :=
  σ.exists_common_stable_refinement_finite P φ hφ

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``IntervalPartition.exists_common_refinement_finset,
      ``FiniteSignal.exists_common_stable_refinement_finite] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
