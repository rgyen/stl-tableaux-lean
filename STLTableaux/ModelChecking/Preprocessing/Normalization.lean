/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.ModelChecking.Preprocessing.Preprocessing

/-! Recursive elimination of timed until over finite signals.
The target allows Boolean negation; conversion to negation normal form is a
separate step. In particular, this module does not claim `MixedReady` output.
-/

namespace STLTableau
namespace Formula
variable {Var : Type*}

/-- Timed until remains only in the encoding of eventually/always.
Unlike `MixedReady`, arbitrary Boolean negation is still permitted. -/
inductive TimedUntilFree : Formula Var → Prop
  | truth : TimedUntilFree .truth
  | atom (a : AtomicProposition Var) : TimedUntilFree (.atom a)
  | neg {φ} : TimedUntilFree φ → TimedUntilFree (.neg φ)
  | and {φ ψ} : TimedUntilFree φ → TimedUntilFree ψ → TimedUntilFree (.and φ ψ)
  | until {φ ψ} : TimedUntilFree φ → TimedUntilFree ψ →
      TimedUntilFree (untimedUntil φ ψ)
  | eventually (I : TimeInterval) {φ} : TimedUntilFree φ → TimedUntilFree (eventually I φ)
  | always (I : TimeInterval) {φ} : TimedUntilFree φ → TimedUntilFree (always I φ)

/-- Eliminate one timed-until node whose operands have already been processed.
The unbounded positive-lower case explicitly retains the finite-horizon guard. -/
noncomputable def eliminateUntil (I : TimeInterval) (φ ψ : Formula Var) : Formula Var := by
  classical
  exact match I with
  | .bounded I =>
      .and (eventually (.bounded I) ψ)
        (if ha : 0 < I.lower then
          always (.bounded ⟨0, I.lower, le_rfl, ha⟩) (untimedUntil φ ψ)
        else untimedUntil φ ψ)
  | .unbounded a =>
      if ha : 0 < (a : ℝ) then
        .and (eventually (.unbounded a) .truth)
          (always (.bounded ⟨0, a, le_rfl, ha⟩) (untimedUntil φ ψ))
      else untimedUntil φ ψ

/-- Structural recursion on the original formula, not on generated syntax.
Existing eventualities are retained rather than expanded into redundant until
and prefix conditions; their operands are still normalized recursively. -/
noncomputable def eliminateTimedUntil : Formula Var → Formula Var
  | .truth => .truth
  | .atom a => .atom a
  | .neg φ => .neg (eliminateTimedUntil φ)
  | .and φ ψ => .and (eliminateTimedUntil φ) (eliminateTimedUntil ψ)
  | .until I .truth ψ => eventually I (eliminateTimedUntil ψ)
  | .until I φ ψ => eliminateUntil I (eliminateTimedUntil φ) (eliminateTimedUntil ψ)

/-- Already-admitted eventuality syntax is preserved exactly. -/
theorem eliminateTimedUntil_eventually (I : TimeInterval) (φ : Formula Var) :
    (eventually I φ).eliminateTimedUntil = eventually I φ.eliminateTimedUntil := rfl

theorem timedUntilFree_eliminateUntil (I : TimeInterval) {φ ψ : Formula Var}
    (hφ : TimedUntilFree φ) (hψ : TimedUntilFree ψ) :
    TimedUntilFree (eliminateUntil I φ ψ) := by
  classical
  cases I with
  | bounded I =>
    simp only [eliminateUntil]
    split
    · exact .and (.eventually _ hψ) (.always _ (.until hφ hψ))
    · exact .and (.eventually _ hψ) (.until hφ hψ)
  | unbounded a =>
    simp only [eliminateUntil]
    split
    · exact .and (.eventually _ .truth) (.always _ (.until hφ hψ))
    · exact .until hφ hψ

theorem timedUntilFree_eliminateTimedUntil (φ : Formula Var) :
    TimedUntilFree (eliminateTimedUntil φ) := by
  induction φ with
  | truth => exact .truth
  | atom a => exact .atom a
  | neg φ ih => exact .neg ih
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | «until» I φ ψ ihφ ihψ =>
    cases φ <;> first
      | exact .eventually I ihψ
      | exact timedUntilFree_eliminateUntil I ihφ ihψ

end Formula

namespace FiniteSignal
open scoped STL
variable {Var : Type*}

theorem satisfies_eliminateUntil (σ : FiniteSignal Var) (I : TimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨Formula.eliminateUntil I φ ψ) ↔ ((σ,t)⊨(φ U[I] ψ)) := by
  classical
  cases I with
  | bounded I =>
    by_cases ha : 0 < I.lower
    · simpa only [Formula.eliminateUntil, dif_pos ha] using
        (σ.satisfies_bounded_until_iff_eventually_and_always_untimedUntil I ha φ ψ t).symm
    · have hz : I.lower = 0 := le_antisymm (le_of_not_gt ha) I.lower_nonnegative
      simpa only [Formula.eliminateUntil, dif_neg ha] using
        (σ.satisfies_bounded_until_zero_iff_eventually_and_untimedUntil I hz φ ψ t).symm
  | unbounded a =>
    by_cases ha : 0 < (a : ℝ)
    · simpa only [Formula.eliminateUntil, dif_pos ha] using
        (σ.satisfies_unbounded_until_iff_eventually_truth_and_always_untimedUntil a ha φ ψ t).symm
    · have hz : a = 0 := Subtype.ext (le_antisymm (le_of_not_gt ha) a.coe_nonneg)
      subst a
      simp only [Formula.eliminateUntil, dif_neg ha, Formula.untimedUntil]

/-- Recursive timed-until elimination preserves Boolean satisfaction at every
signal time, without a lower- or upper-endpoint horizon assumption. -/
theorem satisfies_eliminateTimedUntil (σ : FiniteSignal Var) (φ : Formula Var)
    (t : σ.Time) : ((σ,t)⊨Formula.eliminateTimedUntil φ) ↔ ((σ,t)⊨φ) := by
  induction φ generalizing t with
  | truth => rfl
  | atom a => rfl
  | neg φ ih => exact not_congr (ih t)
  | and φ ψ ihφ ihψ => exact and_congr (ihφ t) (ihψ t)
  | «until» I φ ψ ihφ ihψ =>
    have hcongr : ((σ,t)⊨(φ.eliminateTimedUntil U[I] ψ.eliminateTimedUntil)) ↔
        ((σ,t)⊨(φ U[I] ψ)) := by
      constructor
      · rintro ⟨u, hu, hψ, hφ⟩
        exact ⟨u, hu, (ihψ u).mp hψ, fun s hts hsu => (ihφ s).mp (hφ s hts hsu)⟩
      · rintro ⟨u, hu, hψ, hφ⟩
        exact ⟨u, hu, (ihψ u).mpr hψ, fun s hts hsu => (ihφ s).mpr (hφ s hts hsu)⟩
    cases φ <;> first
      | exact hcongr
      | exact (σ.satisfies_eliminateUntil I _ _ t).trans hcongr

end FiniteSignal
end STLTableau
