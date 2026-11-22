import STLTableaux.Finiteness.Derivation.DerivationNormalization

/-! Expose an assignment already present in an inherited reset as an inner
singleton binder. All rewrites use the actual structural reset laws. This lets
an existing frozen boundary constructor operate beneath an inherited reset,
without changing Resolve or dropping that inherited scope from either output. -/
namespace STLTableau.Section4.Finiteness.InheritedResetExposure
open Section3
variable {Clock Var : Type*}

private theorem reset_ext {R S : ClockResetSet Clock} (h : R.value = S.value) : R = S := by
  cases R
  cases S
  cases h
  rfl

variable [DecidableEq Clock]

/-- An actual recorded assignment absorbs its identical singleton on the left
of the left-biased reset union. No agreement of valuations is assumed. -/
theorem singleton_union_of_value (R : ClockResetSet Clock) (d : Clock) (v : NNReal)
    (hv : R.value d = some v) : (ClockResetSet.singleton d v).union R = R := by
  apply reset_ext
  funext c
  change (match (ClockResetSet.singleton d v).value c with
    | some a => some a | none => R.value c) = R.value c
  by_cases hc : c = d
  · subst c
    simp only [ClockResetSet.singleton,if_true,hv]
  · simp only [ClockResetSet.singleton,if_neg hc]

/-- Duplicate an inherited assignment into a literal inner reset scope. -/
theorem expose (R : ClockResetSet Clock) (d : Clock) (v : NNReal)
    (hv : R.value d = some v) (J : MixedJ Clock Var) :
    StructuralEq (.reset R J) (.reset R (.reset (ClockResetSet.singleton d v) J)) := by
  have h := ACIdem.resetNested R (ClockResetSet.singleton d v) J
  rw [singleton_union_of_value R d v hv] at h
  exact h.symm

/-- Expose the already inherited assignment only around the focused conjunct;
the other pending context remains literal and under the same inherited reset. -/
theorem expose_conjunct (R : ClockResetSet Clock) (d : Clock) (v : NNReal)
    (hv : R.value d = some v) (J Γ : MixedJ Clock Var) :
    StructuralEq (.reset R (.conj J Γ))
      (.reset R (.conj (.reset (ClockResetSet.singleton d v) J) Γ)) :=
  .trans (.resetDistrib R J Γ)
    (.trans (.conj (expose R d v hv J) (.refl _))
      (.symm (.resetDistrib R (.reset (ClockResetSet.singleton d v) J) Γ)))

/-- Actual optional-boundary assembly when the right-zero reset is already in
the inherited input map. The body is exactly the existing boundaryOptional
shape. Both full and erased outputs retain the entire original outer reset. -/
def optional_boundary_with_inherited_reset
    (R : ClockResetSet Clock) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ H A : MixedJ Clock Var)
    (hr : R.value d = some 0) (frozen : FrozenByUpper c d m ℓ kind I φ)
    (hdΓ : d ∉ Γ.freeClocks)
    (D : Resolve (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A) :
    Resolve (.reset R (.conj (.predicate (.bounded c d m (Marker.complement ℓ) kind I φ))
      (.conj (.marker ℓ) Γ))) (.reset R H) (.reset R A) :=
  .structural (expose R d 0 hr _)
    (.reset R (.boundaryOptional frozen hdΓ D))

/-- The analogous required merger retains the inherited reset too. This uses
the actual current unclocked predicate in the existing required-boundary input. -/
def required_boundary_with_inherited_reset
    (R : ClockResetSet Clock) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ H A : MixedJ Clock Var)
    (hr : R.value d = some 0) (frozen : FrozenByUpper c d m ℓ kind I φ)
    (hdΓ : d ∉ Γ.freeClocks)
    (D : Resolve (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A) :
    Resolve (.reset R (.conj (.conj
      (.predicate (.bounded c d m (Marker.complement ℓ) kind I φ))
      (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ)))
      (.reset R H) (.reset R A) :=
  .structural (expose R d 0 hr _)
    (.reset R (.boundaryRequired frozen hdΓ D))

/-- Duplicating the inner binder changes neither the established erased/full
normalization correspondence nor the retained outer reset on both outputs. -/
theorem optional_erased_normalizes
    (R : ClockResetSet Clock) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ H A : MixedJ Clock Var)
    (hr : R.value d = some 0) (frozen : FrozenByUpper c d m ℓ kind I φ)
    (hdΓ : d ∉ Γ.freeClocks)
    (D : Resolve (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A)
    {F : Section3.TransitionForm Clock Var}
    (hF : Section3.TransitionForm.normalize? (.reset R H) = some F) :
    Section3.TransitionForm.normalize? (.reset R A) = some F.atomicProjection :=
  (optional_boundary_with_inherited_reset R c d m ℓ kind I φ Γ H A hr frozen hdΓ D).normalize_erased_of_full hF

end STLTableau.Section4.Finiteness.InheritedResetExposure
