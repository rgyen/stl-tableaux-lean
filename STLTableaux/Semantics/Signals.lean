/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Partitions.Partition

/-!
# Signal Temporal Logic

STL syntax and satisfaction on finite signals (Section 2). Timing intervals
are bounded closed intervals or right-unbounded intervals `[a, ∞)`.
-/

namespace STLTableau

/-- A bounded, closed, non-singular STL timing interval `[lower, upper]`. -/
structure BoundedTimeInterval where
  lower : ℝ
  upper : ℝ
  lower_nonnegative : 0 ≤ lower
  nonSingular : lower < upper

namespace BoundedTimeInterval

/-- The Mathlib set denoted by a bounded timing interval. -/
def carrier (I : BoundedTimeInterval) : Set ℝ := Set.Icc I.lower I.upper

instance : Membership ℝ BoundedTimeInterval := ⟨fun I d => d ∈ I.carrier⟩

@[simp] theorem mem_carrier {I : BoundedTimeInterval} {d : ℝ} :
    d ∈ I.carrier ↔ I.lower ≤ d ∧ d ≤ I.upper := Iff.rfl

end BoundedTimeInterval

/-- An STL timing interval: either `[a,b]` or `[a,∞)`, with nonnegative `a`. -/
inductive TimeInterval where
  | bounded (interval : BoundedTimeInterval)
  | unbounded (lower : NNReal)

namespace TimeInterval

/-- The Mathlib set denoted by a timing interval. -/
def carrier : TimeInterval → Set ℝ
  | .bounded I => I.carrier
  | .unbounded a => Set.Ici a

instance : Membership ℝ TimeInterval := ⟨fun I d => d ∈ I.carrier⟩

instance : Coe BoundedTimeInterval TimeInterval := ⟨.bounded⟩

/-- Membership in `[a, ∞)`. -/
@[simp] theorem mem_unbounded {a : NNReal} {d : ℝ} :
    d ∈ unbounded a ↔ (a : ℝ) ≤ d := by
  rfl

@[simp] theorem mem_bounded {I : BoundedTimeInterval} {d : ℝ} :
    d ∈ TimeInterval.bounded I ↔ I.lower ≤ d ∧ d ≤ I.upper := Iff.rfl

/-- Every delay in a timing interval is nonnegative. -/
theorem nonnegative {I : TimeInterval} {d : ℝ} (hd : d ∈ I) : 0 ≤ d := by
  cases I with
  | bounded I => exact I.lower_nonnegative.trans hd.1
  | unbounded a => exact a.coe_nonneg.trans hd

/-- Absolute times obtained by shifting a relative timing interval. -/
def translate (t : ℝ) (I : TimeInterval) : Set ℝ := {t' | t' - t ∈ I}

@[simp] theorem mem_translate {t t' : ℝ} {I : TimeInterval} :
    t' ∈ I.translate t ↔ t' - t ∈ I := Iff.rfl

theorem le_of_mem_translate {t t' : ℝ} {I : TimeInterval} (h : t' ∈ I.translate t) :
    t ≤ t' := by
  have := nonnegative h
  linarith

end TimeInterval

/-- Comparisons admitted in an atomic STL proposition. -/
inductive RealRelation where
  | ge | gt | eq | lt | le
  deriving DecidableEq, Repr

namespace RealRelation

def Holds : RealRelation → ℝ → ℝ → Prop
  | .ge => (· ≥ ·)
  | .gt => (· > ·)
  | .eq => (· = ·)
  | .lt => (· < ·)
  | .le => (· ≤ ·)

end RealRelation

/-- The atomic proposition `f(x₁, …, xₙ) ⋈ 0`. -/
structure AtomicProposition (Var : Type*) where
  arity : ℕ
  arguments : Fin arity → Var
  function : (Fin arity → ℝ) → ℝ
  relation : RealRelation

namespace AtomicProposition

variable {Var : Type*}

/-- Evaluate an atomic proposition on a real-valued assignment. -/
def Holds (a : AtomicProposition Var) (v : Var → ℝ) : Prop :=
  a.relation.Holds (a.function fun i => v (a.arguments i)) 0

end AtomicProposition

/-- Core STL syntax over real-valued signal variables. -/
inductive Formula (Var : Type*) where
  | truth
  | atom (a : AtomicProposition Var)
  | neg (φ : Formula Var)
  | and (φ ψ : Formula Var)
  | until (I : TimeInterval) (φ ψ : Formula Var)

namespace Formula

variable {Var : Type*}

def falsity : Formula Var := .neg .truth
def or (φ ψ : Formula Var) : Formula Var := .neg (.and (.neg φ) (.neg ψ))
def eventually (I : TimeInterval) (φ : Formula Var) : Formula Var := .until I .truth φ
def always (I : TimeInterval) (φ : Formula Var) : Formula Var := .neg (eventually I (.neg φ))
def release (I : TimeInterval) (φ ψ : Formula Var) : Formula Var :=
  .neg (.until I (.neg φ) (.neg ψ))

def untimedUntil (φ ψ : Formula Var) : Formula Var := .until (.unbounded 0) φ ψ
def untimedEventually (φ : Formula Var) : Formula Var := eventually (.unbounded 0) φ
def untimedAlways (φ : Formula Var) : Formula Var := always (.unbounded 0) φ

/-- Readable STL syntax. Enable with `open scoped STL`. -/
scoped[STL] prefix:max "¬ₛ " => STLTableau.Formula.neg
scoped[STL] infixr:60 " ∧ₛ " => STLTableau.Formula.and
scoped[STL] notation:55 φ " U[" I "] " ψ => STLTableau.Formula.until I φ ψ
scoped[STL] notation:max "◇[" I "] " φ => STLTableau.Formula.eventually I φ
scoped[STL] notation:max "□[" I "] " φ => STLTableau.Formula.always I φ
scoped[STL] notation:55 φ " R[" I "] " ψ => STLTableau.Formula.release I φ ψ

end Formula

/-- A signal over the half-open time domain `[0, horizon)`. -/
structure FiniteSignal (Var : Type*) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  value : {t : ℝ // 0 ≤ t ∧ t < horizon} → Var → ℝ

namespace FiniteSignal

variable {Var : Type*}

/-- Times at which a finite signal is defined. -/
abbrev Time (σ : FiniteSignal Var) := {t : ℝ // 0 ≤ t ∧ t < σ.horizon}

/-- Boolean STL satisfaction, including the inclusive `[t,t']`
requirement for the left operand of until. -/
def Satisfies (σ : FiniteSignal Var) : Formula Var → σ.Time → Prop
  | .truth, _ => True
  | .atom a, t => a.Holds (σ.value t)
  | .neg φ, t => ¬Satisfies σ φ t
  | .and φ ψ, t => Satisfies σ φ t ∧ Satisfies σ ψ t
  | .until I φ ψ, t =>
      ∃ t' : σ.Time,
        t'.1 ∈ I.translate t.1 ∧
        Satisfies σ ψ t' ∧
        ∀ t'' : σ.Time, t.1 ≤ t''.1 → t''.1 ≤ t'.1 → Satisfies σ φ t''

/-- Satisfaction notation mirroring the manuscript's `σ, t ⊨ φ`. Parentheses avoid
ambiguity with Lean's tuple and function-argument commas. -/
notation:45 "(" σ "," t ")" "⊨" φ => STLTableau.FiniteSignal.Satisfies σ φ t

open scoped STL

@[simp] theorem satisfies_truth (σ : FiniteSignal Var) (t : σ.Time) : (σ, t) ⊨ .truth := trivial

@[simp] theorem satisfies_atom (σ : FiniteSignal Var) (a : AtomicProposition Var)
    (t : σ.Time) : ((σ, t) ⊨ (.atom a)) ↔ a.Holds (σ.value t) := Iff.rfl

@[simp] theorem satisfies_neg (σ : FiniteSignal Var) (φ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ (¬ₛ φ)) ↔ ¬((σ, t) ⊨ φ) := Iff.rfl

@[simp] theorem satisfies_and (σ : FiniteSignal Var) (φ ψ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ (φ ∧ₛ ψ)) ↔ ((σ, t) ⊨ φ) ∧ ((σ, t) ⊨ ψ) := Iff.rfl

theorem satisfies_until_iff (σ : FiniteSignal Var)
    (I : TimeInterval) (φ ψ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ (φ U[I] ψ)) ↔
      ∃ t' : σ.Time,
        t'.1 ∈ I.translate t.1 ∧ ((σ, t') ⊨ ψ) ∧
        ∀ t'' : σ.Time, t.1 ≤ t''.1 → t''.1 ≤ t'.1 → (σ, t'') ⊨ φ := Iff.rfl

@[simp] theorem not_satisfies_falsity (σ : FiniteSignal Var)
    (t : σ.Time) : ¬((σ, t) ⊨ Formula.falsity) := by
  simp [Formula.falsity, Satisfies]

@[simp] theorem satisfies_or (σ : FiniteSignal Var)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ Formula.or φ ψ) ↔ ((σ, t) ⊨ φ) ∨ ((σ, t) ⊨ ψ) := by
  classical
  change (¬(¬((σ, t) ⊨ φ) ∧ ¬((σ, t) ⊨ ψ))) ↔ _
  tauto

/-- Inclusive until requires its left operand already at the current time. -/
theorem satisfies_left_of_until (σ : FiniteSignal Var) (I : TimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) (h : (σ,t)⊨(φ U[I] ψ)) :
    (σ,t)⊨φ := by
  obtain ⟨u, hu, _, hprefix⟩ := h
  exact hprefix t le_rfl (TimeInterval.le_of_mem_translate hu)

/-- Both operands true now suffice for untimed until: choose the present
time itself as witness. -/
theorem satisfies_untimedUntil_of_and (σ : FiniteSignal Var)
    (φ ψ : Formula Var) (t : σ.Time) (hφ : (σ,t)⊨φ) (hψ : (σ,t)⊨ψ) :
    (σ,t)⊨(Formula.untimedUntil φ ψ) := by
  refine ⟨t, ?_, hψ, ?_⟩
  · change (0 : ℝ) ≤ t.1 - t.1
    simp
  · intro u htu hut
    have hu : u = t := Subtype.ext (le_antisymm hut htu)
    simpa only [hu] using hφ

/-- With the inclusive-until dual, the left release operand true
now suffices to satisfy release. -/
theorem satisfies_release_of_left (σ : FiniteSignal Var) (I : TimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) (hφ : (σ,t)⊨φ) :
    (σ,t)⊨(φ R[I] ψ) := by
  intro h
  exact satisfies_left_of_until σ I (.neg φ) (.neg ψ) t h hφ

theorem satisfies_eventually_iff (σ : FiniteSignal Var)
    (I : TimeInterval) (φ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ (◇[I] φ)) ↔
      ∃ t' : σ.Time, t'.1 ∈ I.translate t.1 ∧ (σ, t') ⊨ φ := by
  simp [Formula.eventually, Satisfies]

theorem satisfies_always_iff (σ : FiniteSignal Var)
    (I : TimeInterval) (φ : Formula Var) (t : σ.Time) :
    ((σ, t) ⊨ (□[I] φ)) ↔
      ∀ t' : σ.Time, t'.1 ∈ I.translate t.1 → (σ, t') ⊨ φ := by
  change ¬((σ, t) ⊨ (◇[I] (¬ₛ φ))) ↔ _
  rw [satisfies_eventually_iff]
  constructor
  · intro h t' ht'
    by_contra hφ
    exact h ⟨t', ht', hφ⟩
  · rintro h ⟨t', ht', hnotφ⟩
    exact hnotφ (h t' ht')

end FiniteSignal

end STLTableau
