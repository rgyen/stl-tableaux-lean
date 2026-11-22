import STLTableaux.Finiteness.Derivation.Branches.RawBranchPrivacy
import STLTableaux.Finiteness.Derivation.BoundaryGuardScope

/-! Literal support and privacy of the existing boundary constructors.
Duplicate exclusion is explicit. Inherited-reset guard noncapture and historical
frozen provenance are separate obligations, not consequences of these lemmas. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

def boundaryReplacementInput [DecidableEq Clock] (required : Bool) (c d : Clock)
    (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) : MixedJ Clock Var :=
  .reset (ClockResetSet.singleton d 0)
    (.conj (if required then
      .conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))
      else .predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.conj (.marker ℓ) Γ))

def boundaryReplacementChild (c : Clock) (m ℓ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) : MixedJ Clock Var :=
  .conj (.predicate (.upper c m kind I φ))
    (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))

@[simp] theorem boundaryGuard_nextPrivate (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    NextPrivate (withBoundaryGuard c b Γ) ↔ NextPrivate Γ := by
  cases b <;> simp [withBoundaryGuard,NextPrivate]

@[simp] theorem boundaryGuard_nextSyntaxClocks (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    nextSyntaxClocks (withBoundaryGuard c b Γ) = nextSyntaxClocks Γ := by
  cases b <;> simp [withBoundaryGuard,nextSyntaxClocks]

@[simp] theorem boundaryGuard_currentPredicates (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    (withBoundaryGuard c b Γ).currentPredicates = Γ.currentPredicates := by
  cases b <;> simp [withBoundaryGuard,Section3.Judgement.currentPredicates]

@[simp] theorem boundaryReplacement_nextPrivate [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    NextPrivate (boundaryReplacementChild c m ℓ kind I φ Γ) ↔
      NextPrivate (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
  cases required <;> simp [boundaryReplacementChild,boundaryReplacementInput,NextPrivate]

@[simp] theorem boundaryReplacement_nextSyntaxClocks [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    nextSyntaxClocks (boundaryReplacementChild c m ℓ kind I φ Γ) =
      nextSyntaxClocks (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
  cases required <;> simp [boundaryReplacementChild,boundaryReplacementInput,nextSyntaxClocks]

@[simp] theorem boundaryReplacement_child_predicates (c : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) :
    (boundaryReplacementChild c m ℓ kind I φ Γ).currentPredicates =
      {.upper c m kind I φ} ∪ Γ.currentPredicates := by
  simp [boundaryReplacementChild,Section3.Judgement.currentPredicates]

theorem boundaryReplacement_syntax_subset [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    syntaxClocks (boundaryReplacementChild c m ℓ kind I φ Γ) ⊆
      syntaxClocks (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
  cases required <;> cases h : Marker.imp ℓ m <;>
    simp [boundaryReplacementChild,boundaryReplacementInput,withBoundaryGuard,h,syntaxClocks,Set.subset_def]
    <;> aesop

theorem boundaryReplacement_resetNames_subset [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    resetNames (boundaryReplacementChild c m ℓ kind I φ Γ) ⊆
      resetNames (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
  cases required <;> cases h : Marker.imp ℓ m <;>
    simp [boundaryReplacementChild,boundaryReplacementInput,withBoundaryGuard,h,resetNames]

theorem boundaryReplacement_freeClocks [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) (hcd : c ≠ d) (hd : d ∉ Γ.freeClocks) :
    (boundaryReplacementInput required c d m ℓ kind I φ Γ).freeClocks =
      (boundaryReplacementChild c m ℓ kind I φ Γ).freeClocks := by
  ext x
  cases required <;> cases h : Marker.imp ℓ m <;>
    simp only [boundaryReplacementChild,boundaryReplacementInput,Bool.false_eq_true,
      eq_self,ite_false,ite_true,withBoundaryGuard,h,Section3.Judgement.freeClocks,
      ClockResetSet.clocks_singleton,Set.mem_sdiff,Set.mem_union,Set.mem_insert_iff,
      Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false,false_or] <;> aesop

private theorem upper_support_subset_bounded (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    syntaxClocks (.predicate (.upper c m kind I φ)) ⊆
      syntaxClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) := by
  exact Set.singleton_subset_iff.2 (Or.inl rfl)

/-- Privacy does not ban equal duplicate predicates, so excluding a remaining
copy of the selected bounded occurrence is necessary here. -/
theorem boundaryReplacement_private [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var)
    (hprivate : privateRawCurrent (boundaryReplacementInput required c d m ℓ kind I φ Γ))
    (hduplicate : .bounded c d m (¬ₘ ℓ) kind I φ ∉ Γ.currentPredicates) :
    privateRawCurrent (boundaryReplacementChild c m ℓ kind I φ Γ) := by
  have hbound : .bounded c d m (¬ₘ ℓ) kind I φ ∈
      (boundaryReplacementInput required c d m ℓ kind I φ Γ).currentPredicates := by
    cases required <;> simp [boundaryReplacementInput,Section3.Judgement.currentPredicates]
  have hcontext : Γ.currentPredicates ⊆
      (boundaryReplacementInput required c d m ℓ kind I φ Γ).currentPredicates := by
    intro p hp
    cases required <;> simp [boundaryReplacementInput,Section3.Judgement.currentPredicates,hp]
  intro p hp q hq hpq
  rw [boundaryReplacement_child_predicates] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact False.elim (hpq (hp.trans hq.symm))
  · have hd := hprivate _ hbound q (hcontext hq) (fun he => hduplicate (he ▸ hq))
    exact hd.mono (hp ▸ upper_support_subset_bounded c d m ℓ kind I φ) Set.Subset.rfl
  · have hd := hprivate p (hcontext hp) _ hbound (fun he => hduplicate (he ▸ hp))
    exact hd.mono Set.Subset.rfl (hq ▸ upper_support_subset_bounded c d m ℓ kind I φ)
  · exact hprivate p (hcontext hp) q (hcontext hq) hpq


/-- Source-to-next separation is inherited by the upper replacement. -/
theorem boundaryReplacement_source_next_disjoint [DecidableEq Clock] (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var)
    (h : Disjoint (syntaxClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)))
      (nextSyntaxClocks (boundaryReplacementInput required c d m ℓ kind I φ Γ))) :
    Disjoint (syntaxClocks (.predicate (.upper c m kind I φ)))
      (nextSyntaxClocks (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  rw [boundaryReplacement_nextSyntaxClocks required c d m ℓ kind I φ Γ]
  exact h.mono_left (upper_support_subset_bounded c d m ℓ kind I φ)

/-- The two literal syntax definitions are precisely the existing required
and optional constructors, with unchanged full and erased outputs. -/
noncomputable def Resolve.boundaryReplacement [DecidableEq Clock] (required : Bool)
    {c d : Clock} {m ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {Γ H A : MixedJ Clock Var} (hf : FrozenByUpper c d m ℓ kind I φ)
    (hd : d ∉ Γ.freeClocks) (D : Resolve (boundaryReplacementChild c m ℓ kind I φ Γ) H A) :
    Resolve (boundaryReplacementInput required c d m ℓ kind I φ Γ) H A := by
  cases required with
  | false => exact .boundaryOptional hf hd D
  | true => exact .boundaryRequired hf hd D

end STLTableau.Section4.Finiteness
