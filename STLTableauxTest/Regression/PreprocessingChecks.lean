import STLTableaux.ModelChecking.Preprocessing.NormalizedInput

open STLTableau
open scoped STL

variable {Var : Type*}

-- The complete pipeline accepts every raw formula, with no readiness premise.
example (φ : Formula Var) : φ.normalizeForTableau.MixedReady :=
  Formula.mixedReady_normalizeForTableau φ

example (σ : FiniteSignal Var) (φ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨φ.normalizeForTableau) ↔ ((σ,t)⊨φ) :=
  Formula.satisfies_normalizeForTableau φ σ t

-- Arbitrary nesting and negation are covered, not just a single until node.
example (φ : Formula Var) : φ.eliminateTimedUntil.TimedUntilFree :=
  Formula.timedUntilFree_eliminateTimedUntil φ

example (σ : FiniteSignal Var) (φ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨φ.eliminateTimedUntil) ↔ ((σ,t)⊨φ) :=
  σ.satisfies_eliminateTimedUntil φ t

-- No premise requires t + I.upper (or t + I.lower) to precede the horizon.
example (σ : FiniteSignal Var) (I : BoundedTimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ
        (φ U[TimeInterval.unbounded ⟨I.lower, I.lower_nonnegative⟩] ψ))) :=
  σ.satisfies_bounded_until_iff_eventually_and_unbounded I φ ψ t

-- The zero-lower case does not manufacture a forbidden singleton interval.
example (σ : FiniteSignal Var) (I : BoundedTimeInterval) (ha : I.lower = 0)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ Formula.untimedUntil φ ψ)) :=
  σ.satisfies_bounded_until_zero_iff_eventually_and_untimedUntil I ha φ ψ t

-- A positive lower endpoint admits the literal always-prefix syntax.
example (σ : FiniteSignal Var) (I : BoundedTimeInterval) (ha : 0 < I.lower)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ
        (□[TimeInterval.bounded ⟨0, I.lower, le_rfl, ha⟩]
          (Formula.untimedUntil φ ψ)))) :=
  σ.satisfies_bounded_until_iff_eventually_and_always_untimedUntil I ha φ ψ t

-- Guarded unbounded normalization has no extra horizon premise.
example (σ : FiniteSignal Var) (a : NNReal) (ha : 0 < (a : ℝ))
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.unbounded a] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.unbounded a] Formula.truth) ∧ₛ
        (□[TimeInterval.bounded ⟨0, a, le_rfl, ha⟩]
          (Formula.untimedUntil φ ψ)))) :=
  σ.satisfies_unbounded_until_iff_eventually_truth_and_always_untimedUntil a ha φ ψ t

-- At or beyond the horizon, the standalone identity fails even for true operands.
-- This covers equality with the horizon, not just a strictly later lower endpoint.
theorem unbounded_until_prefix_horizon_counterexample
    (σ : FiniteSignal Var) (a : NNReal) (ha : 0 < (a : ℝ)) (t : σ.Time)
    (horizon : σ.horizon ≤ t.val + a) :
    ¬ ((σ,t)⊨(Formula.truth U[TimeInterval.unbounded a] Formula.truth)) ∧
      ((σ,t)⊨(□[TimeInterval.bounded ⟨0, a, le_rfl, ha⟩]
        (Formula.untimedUntil Formula.truth Formula.truth))) := by
  constructor
  · rintro ⟨u, hu, _, _⟩
    have hlow : (a : ℝ) ≤ u.val - t.val := hu
    linarith [u.property.2]
  · rw [FiniteSignal.satisfies_always_iff]
    intro u _
    exact σ.satisfies_untimedUntil_of_and .truth .truth u trivial trivial

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``Formula.eliminateTimedUntil_eventually,
    ``Formula.satisfies_normalizeMixedNegation,
    ``Formula.TimedUntilFree.mixedReady_normalizeMixedNegation,
    ``Formula.mixedReady_normalizeForTableau,
    ``Formula.satisfies_normalizeForTableau,
    ``Formula.timedUntilFree_eliminateUntil,
    ``Formula.timedUntilFree_eliminateTimedUntil,
    ``FiniteSignal.satisfies_eliminateUntil,
    ``FiniteSignal.satisfies_eliminateTimedUntil,
    ``FiniteSignal.satisfies_bounded_until_iff_eventually_and_unbounded,
    ``FiniteSignal.satisfies_unbounded_until_iff_prefix_untimedUntil,
    ``FiniteSignal.satisfies_bounded_until_iff_eventually_and_prefix_untimedUntil,
    ``FiniteSignal.satisfies_bounded_until_iff_eventually_and_always_untimedUntil,
    ``FiniteSignal.satisfies_unbounded_until_iff_always_of_bounded_eventually,
    ``FiniteSignal.satisfies_bounded_until_zero_iff_eventually_and_untimedUntil,
    ``FiniteSignal.satisfies_unbounded_eventually_truth_iff,
    ``FiniteSignal.satisfies_unbounded_until_iff_eventually_truth_and_prefix_untimedUntil,
    ``FiniteSignal.satisfies_unbounded_until_iff_eventually_truth_and_always_untimedUntil,
    ``unbounded_until_prefix_horizon_counterexample]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
