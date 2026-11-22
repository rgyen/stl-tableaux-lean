/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Signals

/-!
# Stability and finite variability

Stable truth on an interval, fully stable partitions, and finite variability
(Section 2).
-/

namespace STLTableau

namespace Formula

variable {Var : Type*}

/-- Reflexive subformula relation. -/
inductive IsSubformula : Formula Var → Formula Var → Prop where
  | refl (φ) : IsSubformula φ φ
  | neg {χ φ} : IsSubformula χ φ → IsSubformula χ (.neg φ)
  | and_left {χ φ ψ} : IsSubformula χ φ → IsSubformula χ (.and φ ψ)
  | and_right {χ φ ψ} : IsSubformula χ ψ → IsSubformula χ (.and φ ψ)
  | until_left {χ φ ψ I} : IsSubformula χ φ → IsSubformula χ (.until I φ ψ)
  | until_right {χ φ ψ I} : IsSubformula χ ψ → IsSubformula χ (.until I φ ψ)

/-- Reflexive subformula notation. -/
scoped[STL] infix:50 " ≼ " => STLTableau.Formula.IsSubformula

open scoped STL

theorem IsSubformula.trans {χ φ ψ : Formula Var}
    (hχφ : χ ≼ φ) (hφψ : φ ≼ ψ) : χ ≼ ψ := by
  induction hφψ with
  | refl => exact hχφ
  | neg _ ih => exact .neg ih
  | and_left _ ih => exact .and_left ih
  | and_right _ ih => exact .and_right ih
  | until_left _ ih => exact .until_left ih
  | until_right _ ih => exact .until_right ih

end Formula

namespace FiniteSignal

variable {Var : Type*}

open scoped STL

/-- The half-open real-time domain `[0, τ)` of a signal. -/
def domain (σ : FiniteSignal Var) : Set ℝ := Set.Ico 0 σ.horizon

@[simp] theorem mem_domain {σ : FiniteSignal Var} {t : ℝ} :
    t ∈ σ.domain ↔ 0 ≤ t ∧ t < σ.horizon := Iff.rfl

/-- Truth of `φ` is constant throughout `J`. -/
def Stable (σ : FiniteSignal Var) (J : MarkedInterval) (φ : Formula Var) : Prop :=
  ∀ (u v : σ.Time), u.1 ∈ J → v.1 ∈ J →
    (((σ, u) ⊨ φ) ↔ ((σ, v) ⊨ φ))

theorem Stable.mono {σ : FiniteSignal Var}
    {J K : MarkedInterval} {φ : Formula Var} (hstable : Stable σ J φ)
    (hsub : K.carrier ⊆ J.carrier) : Stable σ K φ := by
  intro u v hu hv
  exact hstable u v (hsub hu) (hsub hv)

/-- `J` is stable for every subformula of `φ`. -/
def FullyStable (σ : FiniteSignal Var) (J : MarkedInterval) (φ : Formula Var) : Prop :=
  ∀ ψ, ψ ≼ φ → Stable σ J ψ

theorem FullyStable.stable {σ : FiniteSignal Var}
    {J : MarkedInterval} {φ : Formula Var} (h : FullyStable σ J φ) : Stable σ J φ :=
  h φ (.refl φ)

theorem FullyStable.mono {σ : FiniteSignal Var}
    {J K : MarkedInterval} {φ : Formula Var} (hstable : FullyStable σ J φ)
    (hsub : K.carrier ⊆ J.carrier) : FullyStable σ K φ := by
  intro ψ hψ
  exact (hstable ψ hψ).mono hsub

/-- A partition is fully stable when each one of its intervals is. -/
def StablePartition (σ : FiniteSignal Var)
    (φ : Formula Var) (P : IntervalPartition σ.domain) : Prop :=
  ∀ i, FullyStable σ (P.interval i) φ

/-- Stable partitions remain stable under refinement. -/
theorem StablePartition.of_finer {σ : FiniteSignal Var}
    {φ : Formula Var} {P Q : IntervalPartition σ.domain}
    (hP : StablePartition σ φ P) (hQP : Q ⊑ P) : StablePartition σ φ Q := by
  intro j
  obtain ⟨i, hsub⟩ := hQP j
  exact (hP i).mono hsub

/-- A signal has finite variability for `φ` if its domain admits a finite
fully stable interval partition for `φ`. -/
def HasFiniteVariability (σ : FiniteSignal Var) (φ : Formula Var) : Prop :=
  ∃ P : IntervalPartition σ.domain, StablePartition σ φ P

end FiniteSignal

end STLTableau
