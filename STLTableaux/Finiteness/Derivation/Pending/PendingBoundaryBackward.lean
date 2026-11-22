import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryExposure
import STLTableaux.Finiteness.Derivation.BoundaryReplacementSupport

/-! Backward assembly for copied-residual boundary continuations. The old
outside guards are absent here and are reattached by general outer assembly. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem fold_permute_to {X Y : List (MixedJ Clock Var)}
    (h : X.Perm Y) {K : MixedJ Clock Var} (hk : foldCurrent Y = some K) :
    ∃ T, foldCurrent X = some T ∧ StructuralEq T K := by
  cases ht : foldCurrent X with
  | none =>
    have hx := (foldCurrent_none_iff _).1 ht
    have hy : Y = [] := List.length_eq_zero_iff.mp (by simpa only [hx,List.length_nil] using h.length_eq.symm)
    rw [hy] at hk
    cases hk
  | some T => exact ⟨T,rfl,foldCurrent_perm h ht hk⟩

omit [DecidableEq Clock] in
private theorem duplicate_marker (ℓ : Marker) (rest : Option (MixedJ Clock Var)) :
    StructuralEq (prependCurrent (.marker ℓ) rest)
      (.conj (.marker ℓ) (prependCurrent (.marker ℓ) rest)) := by
  cases rest with
  | none => exact .symm (.idem _)
  | some T => exact .trans (.conj (.symm (.idem _)) (.refl T)) (.assoc _ _ _)

/-- The literal existing boundary input body before its right-zero binder. -/
def boundaryOriginalBody (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) : MixedJ Clock Var :=
  .conj (if required then
    .conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.predicate (.plain (timedFormula kind I φ)))
    else .predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.conj (.marker ℓ) Γ)

omit [DecidableEq Clock] in
/-- Copy inherited residual assignments only into the residual suffix. -/
theorem boundary_original_copy_reset
    (R : ClockResetSet Clock) (remaining : List (Local Clock Var))
    (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (hd : Disjoint (copyActiveResets R remaining).clocks
      (Section3.Judgement.freeClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)))) :
    StructuralEq (.reset R (boundaryOriginalBody required c d m ℓ kind I φ Γ))
      (.reset R (boundaryOriginalBody required c d m ℓ kind I φ
        (.reset (copyActiveResets R remaining) Γ))) := by
  let S := copyActiveResets R remaining
  let K : MixedJ Clock Var := if required then
    .conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.predicate (.plain (timedFormula kind I φ)))
    else .predicate (.bounded c d m (¬ₘ ℓ) kind I φ)
  have hK : StructuralEq (.reset S K) K := .resetUnused S K (by
    cases required <;> simpa only [K,Bool.false_eq_true,↓reduceIte,
      Section3.Judgement.freeClocks,Set.union_empty] using hd)
  have hm : StructuralEq (.reset S (.marker ℓ) : MixedJ Clock Var) (.marker ℓ) :=
    .resetUnused S _ (Set.disjoint_empty _)
  have he : StructuralEq (.reset S (boundaryOriginalBody required c d m ℓ kind I φ Γ))
      (boundaryOriginalBody required c d m ℓ kind I φ (.reset S Γ)) :=
    (ACIdem.resetDistrib S K (.conj (.marker ℓ) Γ)).trans
      (.conj hK ((ACIdem.resetDistrib S (.marker ℓ) Γ).trans (.conj hm (.refl _))))
  exact (copyActiveResets_expose R remaining _).trans (.reset R he)

/-- The continuation is the INNER copied child at the inherited valuation.
The existing boundary constructors and old reset then recover the original body. -/
noncomputable def boundary_copied_backward
    (R : ClockResetSet Clock) (remaining : List (Local Clock Var))
    (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ H E : MixedJ Clock Var)
    (hr : R.value d = some 0) (frozen : FrozenByUpper c d m ℓ kind I φ)
    (hdΓ : d ∉ Γ.freeClocks)
    (hd : Disjoint (copyActiveResets R remaining).clocks
      (Section3.Judgement.freeClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))))
    (D : Resolve (boundaryReplacementChild c m ℓ kind I φ
      (.reset (copyActiveResets R remaining) Γ)) H E) :
    Resolve (.reset R (boundaryOriginalBody required c d m ℓ kind I φ Γ))
      (.reset R H) (.reset R E) := by
  have hdCopy : d ∉ (Section3.Judgement.reset (copyActiveResets R remaining) Γ).freeClocks :=
    fun h => hdΓ h.1
  apply Resolve.structural (boundary_original_copy_reset R remaining required c d m ℓ kind I φ Γ hd)
  cases required with
  | false =>
    exact InheritedResetExposure.optional_boundary_with_inherited_reset R c d m ℓ
      kind I φ (.reset (copyActiveResets R remaining) Γ) H E hr frozen hdCopy D
  | true =>
    exact InheritedResetExposure.required_boundary_with_inherited_reset R c d m ℓ
      kind I φ (.reset (copyActiveResets R remaining) Γ) H E hr frozen hdCopy D

omit [DecidableEq Clock] in
/-- Actual selected locals expose the boundary body and d-free residual;
no syntactic or semantic equivalence is assumed among the input premises. -/
theorem owned_boundary_original_body
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest)) :
    ∃ Body Γ, foldCurrent (owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) = some Body ∧
      Γ = prependCurrent (.marker ℓ)
        (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) ∧
      StructuralEq Body (boundaryOriginalBody required c d m ℓ kind I φ Γ) ∧ d ∉ Γ.freeClocks := by
  let Γ := prependCurrent (.marker ℓ)
    (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))
  have ht : foldCurrent ((if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest).map
      Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) =
      some (if required then .conj (.predicate (.plain (timedFormula kind I φ))) Γ else Γ) := by
    cases required <;> simp only [Bool.false_eq_true,↓reduceIte,List.map_cons,List.cons_append,
      Local.toJudgement,foldCurrent_cons,prependCurrent]
    all_goals rfl
  obtain ⟨Old,ho,he⟩ := fold_permute_to
    ((hselection.map Local.toJudgement).append_right (owned.nextInputs.map Section3.Judgement.next)) ht
  have hs := (remaining_body_support owned _ left right hsplit Old ho).2
  have hdOld : d ∉ Old.freeClocks := by
    intro hd
    exact Set.disjoint_left.1 hs (by simp [syntaxClocks]) (free_subset_syntax Old hd)
  have hdTarget : d ∉ (if required then
      Section3.Judgement.conj (.predicate (.plain (timedFormula kind I φ))) Γ else Γ).freeClocks := by
    rw [← he.freeClocks_eq]
    exact hdOld
  have hdΓ : d ∉ Γ.freeClocks := by
    cases required <;> simpa only [Bool.false_eq_true,↓reduceIte,
      Section3.Judgement.freeClocks,Set.empty_union] using hdTarget
  obtain ⟨Body,hb,hExpose⟩ := owned_selected_exposure owned _ left right hsplit
  rw [ho] at hExpose
  refine ⟨Body,Γ,hb,rfl,?_,hdΓ⟩
  cases required with
  | false =>
    exact hExpose.trans (.conj (.refl _) (he.trans (duplicate_marker ℓ _)))
  | true =>
    exact hExpose.trans ((ACIdem.conj (.refl _) he).trans
      ((ACIdem.symm (.assoc _ _ _)).trans (.conj (.refl _) (duplicate_marker ℓ _))))

/-- Recover the actual original owned body from its inner copied continuation.
The d-freeness side condition is derived from source privacy. -/
theorem owned_boundary_copied_backward
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (hr : R.value d = some 0) (frozen : FrozenByUpper c d m ℓ kind I φ)
    (Γ H E : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
    (D : Resolve (boundaryReplacementChild c m ℓ kind I φ
      (.reset (copyActiveResets R (left ++ right)) Γ)) H E) :
    ∃ Body, foldCurrent (owned.locals.map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next) = some Body ∧
      Nonempty (Resolve (.reset R Body) (.reset R H) (.reset R E)) := by
  obtain ⟨Body,Γ',hBody,hΓ',hExpose,hdΓ⟩ :=
    owned_boundary_original_body owned required c d m ℓ kind I φ left right rest hsplit hselection
  have he : Γ' = Γ := hΓ'.trans hΓ.symm
  rw [he] at hExpose hdΓ
  have hd := (copied_remaining_protected owned ∅ (Set.disjoint_empty _) _ left right hsplit).mono_right
    ((free_subset_syntax (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))).trans Set.subset_union_right)
  refine ⟨Body,hBody,⟨?_⟩⟩
  exact .structural (.reset R hExpose)
    (boundary_copied_backward R (left ++ right) required c d m ℓ kind I φ Γ H E hr frozen hdΓ hd D)

end STLTableau.Section4.Finiteness
