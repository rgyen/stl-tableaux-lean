/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Stability.StabilityRefinement

/-! Common refinements for finite families. A supplied base partition handles
the empty family and preserves any existing subdivision. No finite variability
is inferred merely from semantic equivalence or from arbitrary signal values.
-/
namespace STLTableau
open scoped STL

namespace IntervalPartition

/-- Coarsest common refinement of a base partition and a finite family. -/
theorem exists_common_refinement_finset {D : Set ℝ} (P₀ : IntervalPartition D)
    (Ps : Finset (IntervalPartition D)) :
    ∃ R : IntervalPartition D, R ⊑ P₀ ∧ (∀ P ∈ Ps, R ⊑ P) ∧
      ∀ S : IntervalPartition D, S ⊑ P₀ → (∀ P ∈ Ps, S ⊑ P) → S ⊑ R := by
  classical
  induction Ps using Finset.induction_on with
  | empty =>
    exact ⟨P₀, finerThan_refl P₀, by simp, fun _ h _ => h⟩
  | @insert P Ps _ ih =>
    obtain ⟨R, hR₀, hRs, hleast⟩ := ih
    obtain ⟨T, hTR, hTP, hTleast⟩ := R.exists_common_refinement P
    refine ⟨T, finerThan_trans hTR hR₀, ?_, ?_⟩
    · intro Q hQ
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact hTP
      · exact finerThan_trans hTR (hRs Q hQ)
    · intro S hS₀ hSs
      apply hTleast S
      · exact hleast S hS₀ (fun Q hQ => hSs Q (Finset.mem_insert_of_mem hQ))
      · exact hSs P (Finset.mem_insert_self _ _)

end IntervalPartition

namespace FiniteSignal

/-- Finitely many individually finite-variable formulas admit a common fully
stable partition that also refines a supplied base partition. -/
theorem exists_common_stable_refinement_finite {Var ι : Type*} [Finite ι]
    (σ : FiniteSignal Var) (P₀ : IntervalPartition σ.domain)
    (φ : ι → Formula Var) (hφ : ∀ i, σ.HasFiniteVariability (φ i)) :
    ∃ R : IntervalPartition σ.domain, R ⊑ P₀ ∧
      ∀ i, σ.StablePartition (φ i) R := by
  classical
  letI := Fintype.ofFinite ι
  choose P hP using hφ
  obtain ⟨R, hR₀, hRs, _⟩ := P₀.exists_common_refinement_finset (Finset.univ.image P)
  refine ⟨R, hR₀, fun i => ?_⟩
  exact (hP i).of_finer (hRs (P i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))

end FiniteSignal
end STLTableau
