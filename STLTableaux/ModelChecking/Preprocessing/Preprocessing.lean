/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Signals

/-! Semantic preprocessing for the finite-signal, inclusive until.
The combined bounded normalization is valid without extra horizon assumptions.
Lower-bounded normalization is stated either with an explicit horizon premise
or with an eventuality-of-truth guard. A zero lower endpoint is handled without
introducing a singular timing interval.
-/

namespace STLTableau.FiniteSignal
open scoped STL
variable {Var : Type*}

/-- Bounded-until equivalence from Section 2. The reverse direction uses the
earlier of the two right-operand witnesses in the signal domain. -/
theorem satisfies_bounded_until_iff_eventually_and_unbounded
    (σ : FiniteSignal Var) (I : BoundedTimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ
        (φ U[TimeInterval.unbounded ⟨I.lower, I.lower_nonnegative⟩] ψ))) := by
  rw [satisfies_and, satisfies_eventually_iff]
  constructor
  · rintro ⟨u, hu, hψ, hφ⟩
    have hbounds : I.lower ≤ u.val - t.val ∧ u.val - t.val ≤ I.upper := hu
    exact ⟨⟨u, hu, hψ⟩, u, hbounds.1, hψ, hφ⟩
  · rintro ⟨⟨e, he, hψe⟩, u, hu, hψu, hφ⟩
    have heBounds : I.lower ≤ e.val - t.val ∧ e.val - t.val ≤ I.upper := he
    have huLower : I.lower ≤ u.val - t.val := hu
    by_cases hue : u.val ≤ e.val
    · refine ⟨u, ?_, hψu, hφ⟩
      change I.lower ≤ u.val - t.val ∧ u.val - t.val ≤ I.upper
      exact ⟨huLower, (sub_le_sub_right hue t.val).trans heBounds.2⟩
    · refine ⟨e, he, hψe, ?_⟩
      intro s hts hse
      exact hφ s hts (hse.trans (le_of_not_ge hue))

/-- The lower-bounded-until identity, provided its shifted lower endpoint is
still a signal time. The quantified form also covers the singular prefix `[0,0]`. -/
theorem satisfies_unbounded_until_iff_prefix_untimedUntil
    (σ : FiniteSignal Var) (a : NNReal) (φ ψ : Formula Var) (t : σ.Time)
    (ha : t.val + a < σ.horizon) :
    ((σ,t)⊨(φ U[TimeInterval.unbounded a] ψ)) ↔
      ∀ s : σ.Time, t.val ≤ s.val → s.val ≤ t.val + a →
        (σ,s)⊨(Formula.untimedUntil φ ψ) := by
  constructor
  · rintro ⟨u, hu, hψ, hφ⟩ s hts hsa
    have hau : (a : ℝ) ≤ u.val - t.val := hu
    refine ⟨u, ?_, hψ, fun v hsv hvu => hφ v (hts.trans hsv) hvu⟩
    change (0 : ℝ) ≤ u.val - s.val
    linarith
  · intro h
    let s : σ.Time := ⟨t.val + a, add_nonneg t.property.1 a.coe_nonneg, ha⟩
    obtain ⟨u, hu, hψ, hφ⟩ := h s (by dsimp [s]; linarith [a.coe_nonneg]) le_rfl
    have hsu : s.val ≤ u.val := TimeInterval.le_of_mem_translate hu
    refine ⟨u, ?_, hψ, ?_⟩
    · change (a : ℝ) ≤ u.val - t.val
      dsimp [s] at hsu
      linarith
    · intro v htv hvu
      by_cases hvs : v.val ≤ s.val
      · exact σ.satisfies_left_of_until (.unbounded 0) φ ψ v (h v htv hvs)
      · exact hφ v (le_of_not_ge hvs) hvu

/-- Combined bounded normalization needs no extra horizon assumption: its
eventuality supplies a witness beyond the lower endpoint. -/
theorem satisfies_bounded_until_iff_eventually_and_prefix_untimedUntil
    (σ : FiniteSignal Var) (I : BoundedTimeInterval)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨(◇[TimeInterval.bounded I] ψ)) ∧
        ∀ s : σ.Time, t.val ≤ s.val → s.val ≤ t.val + I.lower →
          (σ,s)⊨(Formula.untimedUntil φ ψ) := by
  rw [satisfies_bounded_until_iff_eventually_and_unbounded, satisfies_and]
  constructor
  · rintro ⟨he, hu⟩
    obtain ⟨u, humem, _⟩ := (σ.satisfies_eventually_iff _ _ _).mp he
    have hlow : I.lower ≤ u.val - t.val := humem.1
    have ha : t.val + I.lower < σ.horizon := by linarith [u.property.2]
    exact ⟨he, (σ.satisfies_unbounded_until_iff_prefix_untimedUntil
      ⟨I.lower, I.lower_nonnegative⟩ φ ψ t ha).mp hu⟩
  · rintro ⟨he, hprefix⟩
    obtain ⟨u, humem, _⟩ := (σ.satisfies_eventually_iff _ _ _).mp he
    have hlow : I.lower ≤ u.val - t.val := humem.1
    have ha : t.val + I.lower < σ.horizon := by linarith [u.property.2]
    exact ⟨he, (σ.satisfies_unbounded_until_iff_prefix_untimedUntil
      ⟨I.lower, I.lower_nonnegative⟩ φ ψ t ha).mpr hprefix⟩

/-- Syntactic version of the bounded timed-until elimination.
The positivity assumption makes `[0,I.lower]` an admitted nonsingular interval. -/
theorem satisfies_bounded_until_iff_eventually_and_always_untimedUntil
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (ha : 0 < I.lower)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ
        (□[TimeInterval.bounded ⟨0, I.lower, le_rfl, ha⟩]
          (Formula.untimedUntil φ ψ)))) := by
  rw [satisfies_bounded_until_iff_eventually_and_prefix_untimedUntil,
    satisfies_and, satisfies_always_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h s hs
    have hs' : 0 ≤ s.val - t.val ∧ s.val - t.val ≤ I.lower := hs
    exact h s (by linarith) (by linarith)
  · intro h s hts hsa
    apply h s
    change 0 ≤ s.val - t.val ∧ s.val - t.val ≤ I.lower
    constructor <;> linarith

/-- The equivalence for the unbounded until assumes satisfaction of
`◇[I] ψ` with bounded `I`. -/
theorem satisfies_unbounded_until_iff_always_of_bounded_eventually
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (ha : 0 < I.lower)
    (φ ψ : Formula Var) (t : σ.Time)
    (he : (σ,t)⊨(◇[TimeInterval.bounded I] ψ)) :
    ((σ,t)⊨(φ U[TimeInterval.unbounded ⟨I.lower, I.lower_nonnegative⟩] ψ)) ↔
      ((σ,t)⊨(□[TimeInterval.bounded ⟨0, I.lower, le_rfl, ha⟩]
        (Formula.untimedUntil φ ψ))) := by
  have h := (σ.satisfies_bounded_until_iff_eventually_and_unbounded I φ ψ t).symm.trans
    (σ.satisfies_bounded_until_iff_eventually_and_always_untimedUntil I ha φ ψ t)
  simpa only [satisfies_and, he, true_and] using h

/-- At lower endpoint zero the prefix condition is simply untimed until at
the present time, so no singular timing interval is introduced. -/
theorem satisfies_bounded_until_zero_iff_eventually_and_untimedUntil
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (ha : I.lower = 0)
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.bounded I] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.bounded I] ψ) ∧ₛ
        (Formula.untimedUntil φ ψ))) := by
  rw [satisfies_bounded_until_iff_eventually_and_unbounded]
  have hzero : (⟨I.lower, I.lower_nonnegative⟩ : NNReal) = 0 :=
    Subtype.ext ha
  rw [hzero]
  rfl

/-- An eventuality of truth over `[a, ∞)` holds exactly when the earliest
possible witness lies in the finite signal domain. -/
theorem satisfies_unbounded_eventually_truth_iff
    (σ : FiniteSignal Var) (a : NNReal) (t : σ.Time) :
    ((σ,t)⊨(◇[TimeInterval.unbounded a] Formula.truth)) ↔
      t.val + a < σ.horizon := by
  rw [satisfies_eventually_iff]
  constructor
  · rintro ⟨u, hu, _⟩
    have hlow : (a : ℝ) ≤ u.val - t.val := hu
    linarith [u.property.2]
  · intro ha
    refine ⟨⟨t.val + a, add_nonneg t.property.1 a.coe_nonneg, ha⟩, ?_, trivial⟩
    change (a : ℝ) ≤ t.val + a - t.val
    linarith

/-- Guarded lower-bounded normalization valid even when the requested lower
endpoint lies outside the finite signal. -/
theorem satisfies_unbounded_until_iff_eventually_truth_and_prefix_untimedUntil
    (σ : FiniteSignal Var) (a : NNReal) (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.unbounded a] ψ)) ↔
      ((σ,t)⊨(◇[TimeInterval.unbounded a] Formula.truth)) ∧
        ∀ s : σ.Time, t.val ≤ s.val → s.val ≤ t.val + a →
          (σ,s)⊨(Formula.untimedUntil φ ψ) := by
  rw [satisfies_unbounded_eventually_truth_iff]
  constructor
  · intro h
    have hex := h
    obtain ⟨u, hu, _, _⟩ := hex
    have hlow : (a : ℝ) ≤ u.val - t.val := hu
    have ha : t.val + a < σ.horizon := by linarith [u.property.2]
    exact ⟨ha, (σ.satisfies_unbounded_until_iff_prefix_untimedUntil a φ ψ t ha).mp h⟩
  · rintro ⟨ha, h⟩
    exact (σ.satisfies_unbounded_until_iff_prefix_untimedUntil a φ ψ t ha).mpr h

/-- Syntactic guarded normalization for a positive unbounded lower endpoint. -/
theorem satisfies_unbounded_until_iff_eventually_truth_and_always_untimedUntil
    (σ : FiniteSignal Var) (a : NNReal) (ha : 0 < (a : ℝ))
    (φ ψ : Formula Var) (t : σ.Time) :
    ((σ,t)⊨(φ U[TimeInterval.unbounded a] ψ)) ↔
      ((σ,t)⊨((◇[TimeInterval.unbounded a] Formula.truth) ∧ₛ
        (□[TimeInterval.bounded ⟨0, a, le_rfl, ha⟩]
          (Formula.untimedUntil φ ψ)))) := by
  rw [satisfies_unbounded_until_iff_eventually_truth_and_prefix_untimedUntil,
    satisfies_and, satisfies_always_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h s hs
    have hs' : 0 ≤ s.val - t.val ∧ s.val - t.val ≤ a := hs
    exact h s (by linarith) (by linarith)
  · intro h s hts hsa
    apply h s
    change 0 ≤ s.val - t.val ∧ s.val - t.val ≤ a
    constructor <;> linarith

end STLTableau.FiniteSignal
