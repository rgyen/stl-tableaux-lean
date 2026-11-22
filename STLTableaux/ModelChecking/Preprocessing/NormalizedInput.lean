/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.ModelChecking.Preprocessing.Normalization
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Total semantic preprocessing into the mixed temporal grammar.
Negation normalization preserves eventually/always encodings at all intervals,
including positive-lower unbounded intervals used for finite-horizon guards.
-/

namespace STLTableau
namespace Formula
variable {Var : Type*}

/-- Push negation inward, preserving timed eventuality as an opening-rule form. -/
def normalizeMixedNegation (negative : Bool) : Formula Var → Formula Var
  | .truth => if negative then falsity else .truth
  | .atom a => if negative then a.complementFormula else .atom a
  | .neg φ => normalizeMixedNegation (!negative) φ
  | .and φ ψ => if negative then
      Formula.or (normalizeMixedNegation true φ) (normalizeMixedNegation true ψ)
    else .and (normalizeMixedNegation false φ) (normalizeMixedNegation false ψ)
  | .until I φ ψ => if negative then
      match φ with
      | .truth => Formula.always I (normalizeMixedNegation true ψ)
      | _ => Formula.release I (normalizeMixedNegation true φ) (normalizeMixedNegation true ψ)
    else .until I (normalizeMixedNegation false φ) (normalizeMixedNegation false ψ)

theorem satisfies_normalizeMixedNegation (φ : Formula Var) (negative : Bool)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies (φ.normalizeMixedNegation negative) t ↔
      if negative then ¬ σ.Satisfies φ t else σ.Satisfies φ t := by
  induction φ generalizing negative t with
  | truth => cases negative <;> simp [normalizeMixedNegation, falsity, FiniteSignal.Satisfies]
  | atom a => cases negative <;>
      simp [normalizeMixedNegation, AtomicProposition.satisfies_complementFormula,
        FiniteSignal.Satisfies]
  | neg φ ih => cases negative <;> simp [normalizeMixedNegation, FiniteSignal.Satisfies, ih]
  | and φ ψ ihφ ihψ =>
      cases negative
      · simp [normalizeMixedNegation, FiniteSignal.Satisfies, ihφ, ihψ]
      · simp [normalizeMixedNegation, FiniteSignal.satisfies_or, FiniteSignal.Satisfies,
          ihφ, ihψ]
        tauto
  | «until» I φ ψ ihφ ihψ =>
      cases negative
      · simp [normalizeMixedNegation, FiniteSignal.Satisfies, ihφ, ihψ]
      · have hrelease :
            σ.Satisfies (Formula.release I (normalizeMixedNegation true φ)
              (normalizeMixedNegation true ψ)) t ↔ ¬ σ.Satisfies (.until I φ ψ) t := by
          simp [Formula.release, FiniteSignal.Satisfies, ihφ, ihψ]
        cases φ <;> first
          | exact hrelease
          | simp only [normalizeMixedNegation, ↓reduceIte]
            simp [Formula.always, Formula.eventually, FiniteSignal.Satisfies, ihψ]

theorem TimedUntilFree.mixedReady_normalizeMixedNegation {φ : Formula Var}
    (h : φ.TimedUntilFree) (negative : Bool) :
    (φ.normalizeMixedNegation negative).MixedReady := by
  induction h generalizing negative with
  | truth => cases negative <;> first | exact .truth | exact .falsity
  | atom a =>
      cases negative
      · exact .atom a
      · cases hr : a.relation <;>
          simp only [normalizeMixedNegation, ↓reduceIte,
            AtomicProposition.complementFormula, hr] <;>
          first | exact .atom _ | exact .or (.atom _) (.atom _)
  | neg h ih => exact ih (!negative)
  | and hφ hψ ihφ ihψ =>
      cases negative
      · exact .and (ihφ false) (ihψ false)
      · exact .or (ihφ true) (ihψ true)
  | @«until» φ ψ hφ hψ ihφ ihψ =>
      cases negative
      · exact .until (ihφ false) (ihψ false)
      · cases φ <;> first
          | exact .always _ (ihψ true)
          | exact .release (ihφ true) (ihψ true)
  | eventually I h ih =>
      cases negative
      · exact .eventually I (ih false)
      · exact .always I (ih true)
  | always I h ih =>
      cases negative
      · exact .always I (ih false)
      · exact .eventually I (ih true)

/-- Total normalization into the normalized input grammar. Real-endpoint
comparisons make this a noncomputable specification, not an executable parser. -/
noncomputable def normalizeForTableau (φ : Formula Var) : Formula Var :=
  (eliminateTimedUntil φ).normalizeMixedNegation false

theorem mixedReady_normalizeForTableau (φ : Formula Var) :
    φ.normalizeForTableau.MixedReady :=
  (timedUntilFree_eliminateTimedUntil φ).mixedReady_normalizeMixedNegation false

theorem satisfies_normalizeForTableau (φ : Formula Var)
    (σ : FiniteSignal Var) (t : σ.Time) :
    σ.Satisfies φ.normalizeForTableau t ↔ σ.Satisfies φ t := by
  unfold normalizeForTableau
  exact (satisfies_normalizeMixedNegation _ false σ t).trans
    (σ.satisfies_eliminateTimedUntil φ t)

end Formula
end STLTableau
