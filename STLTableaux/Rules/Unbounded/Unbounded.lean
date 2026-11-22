import STLTableaux.ModelChecking.Preprocessing.Admissibility
import STLTableaux.Semantics.IntervalSemantics

/-!
# Exact bounded compilation at a fixed finite horizon

The input grammar admits arbitrary `[a,∞)` bounds on eventually and always,
while retaining untimed until/release. Compilation changes the initial formula,
not the semantics of clocked predicates with possibly negative scope endpoints.
The resulting formula is admitted by the existing concrete rule catalogue.
The horizon is a parameter: this does not construct one horizon-independent
finite tableau for all signals.
-/
namespace STLTableau
open scoped STL
variable {Clock Var : Type*}

/-- Replace an infinite upper bound by a bound strictly beyond every delay
between two signal times in `[0,H)`. Existing bounded intervals are untouched. -/
def capTiming (H : ℝ) (hH : 0 < H) : TimeInterval → BoundedTimeInterval
  | .bounded I => I
  | .unbounded a => ⟨a, (a : ℝ) + H + 1, a.coe_nonneg, by linarith⟩

/-- Exactness uses both endpoints being actual signal times. It is deliberately
not asserted for arbitrary real scope points of a clocked predicate. -/
theorem capTiming_translate (σ : FiniteSignal Var) (I : TimeInterval)
    (t u : σ.Time) :
    u.1 ∈ ((capTiming σ.horizon σ.horizon_pos I : BoundedTimeInterval) :
      TimeInterval).translate t.1 ↔
      u.1 ∈ I.translate t.1 := by
  cases I with
  | bounded I => rfl
  | unbounded a =>
      change ((a : ℝ) ≤ u.1 - t.1 ∧ u.1 - t.1 ≤ (a : ℝ) + σ.horizon + 1) ↔
        (a : ℝ) ≤ u.1 - t.1
      constructor
      · exact And.left
      · intro h
        exact ⟨h, by linarith [t.2.1, u.2.2, a.coe_nonneg]⟩

/-- Capping a timing interval preserves inclusive-until semantics. -/
theorem until_capTiming (σ : FiniteSignal Var) (I : TimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(.until (capTiming σ.horizon σ.horizon_pos I) φ ψ)) ↔
      (σ,t)⊨(.until I φ ψ) := by
  simp only [FiniteSignal.Satisfies, capTiming_translate]

theorem eventually_capTiming (σ : FiniteSignal Var) (I : TimeInterval)
    (φ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(Formula.eventually (capTiming σ.horizon σ.horizon_pos I) φ)) ↔
      (σ,t)⊨(Formula.eventually I φ) :=
  until_capTiming σ I .truth φ t

theorem always_capTiming (σ : FiniteSignal Var) (I : TimeInterval)
    (φ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(Formula.always (capTiming σ.horizon σ.horizon_pos I) φ)) ↔
      (σ,t)⊨(Formula.always I φ) := by
  exact not_congr (eventually_capTiming σ I (.neg φ) t)

/-- The normalized input grammar, including unbounded F/G intervals.
This representation retains constructor choices instead of guessing whether
an encoded `until` is an F, U, or a component of a dual connective. -/
inductive HorizonInput (Var : Type*) where
  | truth
  | falsity
  | atom (a : AtomicProposition Var)
  | and (φ ψ : HorizonInput Var)
  | or (φ ψ : HorizonInput Var)
  | until (φ ψ : HorizonInput Var)
  | release (φ ψ : HorizonInput Var)
  | eventually (I : TimeInterval) (φ : HorizonInput Var)
  | always (I : TimeInterval) (φ : HorizonInput Var)

namespace UnboundedStability

private theorem fully_neg (σ : FiniteSignal Var) (J : MarkedInterval) (φ : Formula Var) :
    σ.FullyStable J (.neg φ) ↔ σ.FullyStable J φ := by
  constructor
  · intro h ψ hp; exact h ψ (.neg hp)
  · intro h ψ hp
    cases hp with
    | refl =>
        intro u v hu hv
        exact not_congr (h.stable u v hu hv)
    | neg hp => exact h ψ hp

private theorem fully_and (σ : FiniteSignal Var) (J : MarkedInterval) (φ ψ : Formula Var) :
    σ.FullyStable J (.and φ ψ) ↔ σ.FullyStable J φ ∧ σ.FullyStable J ψ := by
  constructor
  · intro h; exact ⟨fun χ hc => h χ (.and_left hc), fun χ hc => h χ (.and_right hc)⟩
  · rintro ⟨hφ,hψ⟩ χ hc
    cases hc with
    | refl =>
        intro u v hu hv
        exact and_congr (hφ.stable u v hu hv) (hψ.stable u v hu hv)
    | and_left hc => exact hφ χ hc
    | and_right hc => exact hψ χ hc

private theorem fully_until (σ : FiniteSignal Var) (J : MarkedInterval)
    (I : TimeInterval) (φ ψ : Formula Var) :
    σ.FullyStable J (.until I φ ψ) ↔
      σ.Stable J (.until I φ ψ) ∧ σ.FullyStable J φ ∧ σ.FullyStable J ψ := by
  constructor
  · intro h
    exact ⟨h.stable, fun χ hc => h χ (.until_left hc), fun χ hc => h χ (.until_right hc)⟩
  · rintro ⟨h,hφ,hψ⟩ χ hc
    cases hc with
    | refl => exact h
    | until_left hc => exact hφ χ hc
    | until_right hc => exact hψ χ hc

private theorem stable_neg (σ : FiniteSignal Var) (J : MarkedInterval) (φ : Formula Var) :
    σ.Stable J (.neg φ) ↔ σ.Stable J φ := by
  classical
  constructor
  · intro h u v hu hv
    have hh := h u v hu hv
    change (¬ _) ↔ (¬ _) at hh
    tauto
  · intro h u v hu hv
    exact not_congr (h u v hu hv)

end UnboundedStability

namespace HorizonInput

def formula : HorizonInput Var → Formula Var
  | .truth => .truth
  | .falsity => Formula.falsity
  | .atom a => .atom a
  | .and φ ψ => .and φ.formula ψ.formula
  | .or φ ψ => Formula.or φ.formula ψ.formula
  | .until φ ψ => Formula.untimedUntil φ.formula ψ.formula
  | .release φ ψ => Formula.release (.unbounded 0) φ.formula ψ.formula
  | .eventually I φ => Formula.eventually I φ.formula
  | .always I φ => Formula.always I φ.formula

/-- Compile a formula with a fixed horizon to the tableau formula grammar. -/
def compile (H : ℝ) (hH : 0 < H) : HorizonInput Var → Formula Var
  | .truth => .truth
  | .falsity => Formula.falsity
  | .atom a => .atom a
  | .and φ ψ => .and (φ.compile H hH) (ψ.compile H hH)
  | .or φ ψ => Formula.or (φ.compile H hH) (ψ.compile H hH)
  | .until φ ψ => Formula.untimedUntil (φ.compile H hH) (ψ.compile H hH)
  | .release φ ψ => Formula.release (.unbounded 0) (φ.compile H hH) (ψ.compile H hH)
  | .eventually I φ => Formula.eventually (capTiming H hH I) (φ.compile H hH)
  | .always I φ => Formula.always (capTiming H hH I) (φ.compile H hH)

theorem compile_ready (H : ℝ) (hH : 0 < H) (φ : HorizonInput Var) :
    (φ.compile H hH).TableauReady := by
  induction φ with
  | truth => exact .truth
  | falsity => exact .falsity
  | atom a => exact .atom a
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | or φ ψ ihφ ihψ => exact .or ihφ ihψ
  | «until» φ ψ ihφ ihψ => exact .until ihφ ihψ
  | release φ ψ ihφ ihψ => exact .release ihφ ihψ
  | eventually I φ ih => exact .eventually _ ih
  | always I φ ih => exact .always _ ih

/-- Pointwise equivalence is proved recursively for arbitrary nesting,
including nested unbounded temporal operators and inclusive until/release. -/
theorem compile_correct (σ : FiniteSignal Var) (φ : HorizonInput Var) (t : σ.Time) :
    ((σ,t)⊨(φ.compile σ.horizon σ.horizon_pos)) ↔ (σ,t)⊨φ.formula := by
  induction φ generalizing t with
  | truth => rfl
  | falsity => rfl
  | atom a => rfl
  | and φ ψ ihφ ihψ =>
      exact and_congr (ihφ t) (ihψ t)
  | or φ ψ ihφ ihψ =>
      change (¬ (¬ _ ∧ ¬ _)) ↔ (¬ (¬ _ ∧ ¬ _))
      exact not_congr (and_congr (not_congr (ihφ t)) (not_congr (ihψ t)))
  | «until» φ ψ ihφ ihψ =>
      simp only [compile, formula, Formula.untimedUntil, FiniteSignal.Satisfies,
        ihφ, ihψ]
  | release φ ψ ihφ ihψ =>
      simp only [compile, formula, Formula.release, FiniteSignal.Satisfies, ihφ, ihψ]
  | eventually I φ ih =>
      rw [show (HorizonInput.eventually I φ).compile σ.horizon σ.horizon_pos =
        Formula.eventually (capTiming σ.horizon σ.horizon_pos I)
          (φ.compile σ.horizon σ.horizon_pos) from rfl]
      rw [eventually_capTiming]
      simp only [formula, Formula.eventually, FiniteSignal.Satisfies, ih]
  | always I φ ih =>
      rw [show (HorizonInput.always I φ).compile σ.horizon σ.horizon_pos =
        Formula.always (capTiming σ.horizon σ.horizon_pos I)
          (φ.compile σ.horizon σ.horizon_pos) from rfl]
      rw [always_capTiming]
      simp only [formula, Formula.always, Formula.eventually, FiniteSignal.Satisfies, ih]

/-- Stable truth of the initial formula is preserved on every interval. -/
theorem compile_plain_correct (σ : FiniteSignal Var) (φ : HorizonInput Var)
    (J : MarkedInterval) (α : ClockValuation Clock) :
    predicateSatisfies σ J α (.plain (φ.compile σ.horizon σ.horizon_pos)) ↔
      predicateSatisfies σ J α (.plain φ.formula) := by
  simp only [predicateSatisfies, compile_correct]

/-- Pointwise correctness also preserves truth stability. -/
theorem compile_stable (σ : FiniteSignal Var) (φ : HorizonInput Var) (J : MarkedInterval) :
    σ.Stable J (φ.compile σ.horizon σ.horizon_pos) ↔ σ.Stable J φ.formula := by
  simp only [FiniteSignal.Stable, compile_correct]

/-- The very same partition is fully stable before and after compilation;
no unproved existence or partition-refinement premise is introduced. -/
theorem compile_fullyStable (σ : FiniteSignal Var) (φ : HorizonInput Var) (J : MarkedInterval) :
    σ.FullyStable J (φ.compile σ.horizon σ.horizon_pos) ↔ σ.FullyStable J φ.formula := by
  induction φ with
  | truth => rfl
  | falsity => rfl
  | atom a => rfl
  | and φ ψ ihφ ihψ =>
      simp only [compile, formula, UnboundedStability.fully_and, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp only [compile, formula, Formula.or, UnboundedStability.fully_neg,
        UnboundedStability.fully_and, ihφ, ihψ]
  | «until» φ ψ ihφ ihψ =>
      have hs := compile_stable σ (.until φ ψ) J
      simpa only [compile, formula, Formula.untimedUntil,
        UnboundedStability.fully_until, ihφ, ihψ] using
        (and_congr hs (and_congr ihφ ihψ))
  | release φ ψ ihφ ihψ =>
      have hs := compile_stable σ (.release φ ψ) J
      simp only [compile, formula, Formula.release, UnboundedStability.stable_neg] at hs
      simpa only [compile, formula, Formula.release, UnboundedStability.fully_neg,
        UnboundedStability.fully_until, ihφ, ihψ] using
        (and_congr hs (and_congr ihφ ihψ))
  | eventually I φ ih =>
      have hs := compile_stable σ (.eventually I φ) J
      simpa only [compile, formula, Formula.eventually,
        UnboundedStability.fully_until, ih] using (and_congr hs (Iff.rfl.and ih))
  | always I φ ih =>
      have hs := compile_stable σ (.always I φ) J
      simp only [compile, formula, Formula.always, UnboundedStability.stable_neg] at hs
      simpa only [compile, formula, Formula.always, Formula.eventually,
        UnboundedStability.fully_neg, UnboundedStability.fully_until, ih] using
        (and_congr hs (Iff.rfl.and ih))

theorem compile_stablePartition (σ : FiniteSignal Var) (φ : HorizonInput Var)
    (P : IntervalPartition σ.domain) :
    σ.StablePartition (φ.compile σ.horizon σ.horizon_pos) P ↔
      σ.StablePartition φ.formula P := by
  simp only [FiniteSignal.StablePartition, compile_fullyStable]

end HorizonInput
end STLTableau
