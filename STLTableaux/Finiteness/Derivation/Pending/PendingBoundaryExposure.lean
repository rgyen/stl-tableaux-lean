import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedExposure
import STLTableaux.Finiteness.Derivation.Pending.PendingFold
import STLTableaux.Finiteness.Derivation.ResolveFreeSupport
import STLTableaux.Finiteness.Derivation.InheritedResetExposure

/-! Expose actual selected boundary locals beneath their inherited reset.
The selected marker is duplicated by idempotence, so an absent residual never
requires a fabricated neutral judgement. Outside guards retain their scope. -/
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

private theorem lift_owned_boundary
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (d : Clock) (hr : R.value d = some 0)
    {Body Input : MixedJ Clock Var}
    (hf : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body)
    (he : StructuralEq Body Input) :
    ∃ Target, optionalConj
        (foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))))
        (some (.reset R (.reset (ClockResetSet.singleton d 0) Input))) = some Target ∧
      StructuralEq J Target := by
  have hb : StructuralEq (.reset R Body)
      (.reset R (.reset (ClockResetSet.singleton d 0) Input)) :=
    (ACIdem.reset R he).trans (InheritedResetExposure.expose R d 0 hr Input)
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    refine ⟨_,rfl,?_⟩
    have hc : owned.canonical = .reset R Body := by
      simpa only [canonicalSyntax,hg,hf,Option.map_some,optionalConj,Option.some.injEq] using owned.shape.symm
    exact owned.regroup.trans (hc ▸ hb)
  | some Guards =>
    refine ⟨_,rfl,?_⟩
    have hc : owned.canonical = .conj Guards (.reset R Body) := by
      simpa only [canonicalSyntax,hg,hf,Option.map_some,optionalConj,Option.some.injEq] using owned.shape.symm
    exact owned.regroup.trans (hc ▸ (.conj (.refl Guards) hb))

/-- Optional exposure from an actual `↑↓` source split and an actual marker
in the remaining local list. The residual may be absent. Its d-freeness follows
from source ownership, rather than a boundary-admission premise. -/
theorem owned_optional_boundary_exposure
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hmarker : (left ++ right).Perm (.marker ℓ :: rest))
    (hr : R.value d = some 0) :
    ∃ Γ Target, d ∉ Γ.freeClocks ∧
      Γ = prependCurrent (.marker ℓ)
        (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) ∧
      optionalConj (foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))))
        (some (.reset R (.reset (ClockResetSet.singleton d 0)
          (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.conj (.marker ℓ) Γ))))) = some Target ∧
      StructuralEq J Target := by
  let Γ := prependCurrent (.marker ℓ)
    (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))
  have ht : foldCurrent ((.marker ℓ :: rest).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ := by
    simpa only [List.map_cons,List.cons_append,Local.toJudgement] using
      foldCurrent_cons (.marker ℓ) (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)
  obtain ⟨Old,ho,he⟩ := fold_permute_to
    ((hmarker.map Local.toJudgement).append_right (owned.nextInputs.map Section3.Judgement.next)) ht
  have hs := (remaining_body_support owned _ left right hsplit Old ho).2
  have hdOld : d ∉ Old.freeClocks := by
    intro hd
    exact Set.disjoint_left.1 hs (by simp [syntaxClocks]) (free_subset_syntax Old hd)
  have hd : d ∉ Γ.freeClocks := by rw [← he.freeClocks_eq]; exact hdOld
  obtain ⟨Body,hb,hExpose⟩ := owned_selected_exposure owned _ left right hsplit
  rw [ho] at hExpose
  have hBody : StructuralEq Body (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.conj (.marker ℓ) Γ)) :=
    hExpose.trans (.conj (.refl _) (he.trans (duplicate_marker ℓ _)))
  obtain ⟨Target,htarget,hstruct⟩ := lift_owned_boundary owned d hr hb hBody
  exact ⟨Γ,Target,hd,rfl,htarget,hstruct⟩

/-- Required exposure additionally selects the actual unclocked companion predicate. The
selected marker remains available even when it is the only residual local. -/
theorem owned_required_boundary_exposure
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselected : (left ++ right).Perm
      (.predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest))
    (hr : R.value d = some 0) :
    ∃ Γ Target, d ∉ Γ.freeClocks ∧
      Γ = prependCurrent (.marker ℓ)
        (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) ∧
      optionalConj (foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))))
        (some (.reset R (.reset (ClockResetSet.singleton d 0)
          (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
            (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))))) = some Target ∧
      StructuralEq J Target := by
  let Γ := prependCurrent (.marker ℓ)
    (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))
  have ht : foldCurrent ((.predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) =
        some (Section3.Judgement.conj (.predicate (.plain (timedFormula kind I φ))) Γ) := by
    simp only [List.map_cons,List.cons_append,Local.toJudgement,foldCurrent_cons,prependCurrent]
    rfl
  obtain ⟨Old,ho,he⟩ := fold_permute_to
    ((hselected.map Local.toJudgement).append_right (owned.nextInputs.map Section3.Judgement.next)) ht
  have hs := (remaining_body_support owned _ left right hsplit Old ho).2
  have hdOld : d ∉ Old.freeClocks := by
    intro hd
    exact Set.disjoint_left.1 hs (by simp [syntaxClocks]) (free_subset_syntax Old hd)
  have hd : d ∉ Γ.freeClocks := by
    intro hΓ
    apply hdOld
    rw [he.freeClocks_eq]
    exact Or.inr hΓ
  obtain ⟨Body,hb,hExpose⟩ := owned_selected_exposure owned _ left right hsplit
  rw [ho] at hExpose
  have hBody : StructuralEq Body
      (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ)) :=
    hExpose.trans ((ACIdem.conj (.refl _) he).trans
      ((ACIdem.symm (.assoc _ _ _)).trans (.conj (.refl _) (duplicate_marker ℓ _))))
  obtain ⟨Target,htarget,hstruct⟩ := lift_owned_boundary owned d hr hb hBody
  exact ⟨Γ,Target,hd,rfl,htarget,hstruct⟩
end STLTableau.Section4.Finiteness
