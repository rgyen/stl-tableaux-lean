/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Stability.Stability
import STLTableaux.Semantics.Partitions.PartitionRefinement

/-! Combining existing stable partitions, without assuming that arbitrary
signals or arbitrary semantic rewrites preserve finite variability. -/
namespace STLTableau.FiniteSignal
open scoped STL
variable {Var : Type*}

theorem FullyStable.and {σ : FiniteSignal Var} {J : MarkedInterval}
    {φ ψ : Formula Var} (hφ : FullyStable σ J φ) (hψ : FullyStable σ J ψ) :
    FullyStable σ J (φ ∧ₛ ψ) := by
  intro χ hχ
  cases hχ with
  | refl =>
    intro u v hu hv
    exact and_congr (hφ.stable u v hu hv) (hψ.stable u v hu hv)
  | and_left h => exact hφ _ h
  | and_right h => exact hψ _ h

/-- Two supplied fully stable partitions admit a shared stable refinement. -/
theorem exists_common_stable_refinement {σ : FiniteSignal Var}
    {φ ψ : Formula Var} {P Q : IntervalPartition σ.domain}
    (hP : σ.StablePartition φ P) (hQ : σ.StablePartition ψ Q) :
    ∃ R : IntervalPartition σ.domain,
      R ⊑ P ∧ R ⊑ Q ∧ σ.StablePartition φ R ∧ σ.StablePartition ψ R := by
  obtain ⟨R, hRP, hRQ, _⟩ := P.exists_common_refinement Q
  exact ⟨R, hRP, hRQ, hP.of_finer hRP, hQ.of_finer hRQ⟩

theorem HasFiniteVariability.and {σ : FiniteSignal Var} {φ ψ : Formula Var}
    (hφ : σ.HasFiniteVariability φ) (hψ : σ.HasFiniteVariability ψ) :
    σ.HasFiniteVariability (φ ∧ₛ ψ) := by
  obtain ⟨P, hP⟩ := hφ
  obtain ⟨Q, hQ⟩ := hψ
  obtain ⟨R, _, _, hRφ, hRψ⟩ := exists_common_stable_refinement hP hQ
  exact ⟨R, fun i => (hRφ i).and (hRψ i)⟩

end STLTableau.FiniteSignal
