import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryChild

/-! The boundary IH frame uses only copied residual resets at the inherited
valuation. The original outside guards and outer reset are reattached later. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- Only the selected source's left clock is read by the replacement and guard.
All copied residual assignments can therefore be exposed just around Γ. -/
theorem boundary_child_copy_reset (S : ClockResetSet Clock) (c : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var)
    (hc : c ∉ S.clocks) :
    StructuralEq (.reset S (boundaryReplacementChild c m ℓ kind I φ Γ))
      (boundaryReplacementChild c m ℓ kind I φ (.reset S Γ)) := by
  have hu : StructuralEq (.reset S (.predicate (.upper c m kind I φ)))
      (.predicate (.upper c m kind I φ)) := .resetUnused S _ (by
    change Disjoint S.clocks {c}
    exact Set.disjoint_singleton_right.2 hc)
  have hm : StructuralEq (.reset S (.marker ℓ) : MixedJ Clock Var) (.marker ℓ) :=
    .resetUnused S _ (Set.disjoint_empty _)
  exact (ACIdem.resetDistrib S _ _).trans (.conj hu
    ((ACIdem.resetDistrib S _ _).trans (.conj hm
      (BoundaryGuardScope.extract_boundary_guard S c (Marker.imp ℓ m) Γ (fun _ => hc)))))

theorem boundary_child_copy_weight (S : ClockResetSet Clock) (c : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) :
    pendingWeight (boundaryReplacementChild c m ℓ kind I φ (.reset S Γ)) =
      pendingWeight (.reset S (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  simp only [boundaryReplacementChild,pendingWeight,pendingWeight_boundaryGuard]

private theorem copy_syntax (S : ClockResetSet Clock) (c : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) :
    syntaxClocks (boundaryReplacementChild c m ℓ kind I φ (.reset S Γ)) ⊆
      syntaxClocks (.reset S (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
  cases hg : Marker.imp ℓ m <;>
    simp [boundaryReplacementChild,withBoundaryGuard,hg,syntaxClocks]

/-- Actual copied boundary ownership. The inherited outer R and its outside
old guards are deliberately absent from this IH input. -/
theorem construct_copied_boundary_child_owned
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hNext : NextPrivate J)
    (A U : Set Clock) (hprotected : protectedActive owned A) (hU : Disjoint R.clocks U)
    (required : Bool) (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) :
    ∃ child : OwnedPending
      (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ))
      (copyActiveResets R (left ++ right)) W,
      child.guards = boundaryChildGuards c (Marker.imp ℓ m) [] ∧
      child.locals = PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest) ∧
      child.nextInputs = owned.nextInputs ∧ protectedActive child A ∧
      Disjoint (copyActiveResets R (left ++ right)).clocks
        (A ∪ syntaxClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))) ∧
      Disjoint (copyActiveResets R (left ++ right)).clocks U ∧
      NextPrivate (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)) := by
  let S := copyActiveResets R (left ++ right)
  have hS : Disjoint S.clocks (A ∪ syntaxClocks (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))) :=
    copied_remaining_protected owned A hprotected _ left right hsplit
  have hc : c ∉ S.clocks := fun hx => Set.disjoint_left.1 hS hx (Or.inr (Or.inl rfl))
  have hSW : S.clocks ⊆ W := by
    intro x hx
    rw [copyActiveResets_clocks] at hx
    exact owned.covers_input (Or.inr hx.1)
  obtain ⟨inner,hG,hL,hNs,hGuards,hPrivate⟩ := construct_boundary_child_owned_core owned hNext required
    c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ S [] hSW
    (by intro g hg; cases hg) (fun _ => hc)
  have he := boundary_child_copy_reset S c m ℓ kind I φ Γ hc
  have hweight := boundary_child_copy_weight S c m ℓ kind I φ Γ
  let child : OwnedPending (boundaryReplacementChild c m ℓ kind I φ (.reset S Γ)) S W := {
    inner with
    regroup := he.symm.trans inner.regroup
    regroup_nonincrease := by
      rw [hweight]
      exact inner.regroup_nonincrease
    covers_input := by
      apply Set.union_subset
      · apply Set.union_subset
        · exact (copy_syntax S c m ℓ kind I φ Γ).trans (fun _ hx => inner.covers_input (Or.inl (Or.inl hx)))
        · exact fun _ hx => inner.covers_input (Or.inl (Or.inr hx))
      · exact fun _ hx => inner.covers_input (Or.inr hx) }
  refine ⟨child,hG,hL,hNs,?_,hS,?_,?_⟩
  · exact boundary_child_protected owned A hprotected required c d m ℓ kind I φ left right rest hsplit hselection child hL
  · exact hU.mono_left (by rw [copyActiveResets_clocks]; exact Set.inter_subset_left)
  · exact he.nextPrivate_iff.1 hPrivate


theorem copied_boundary_child_weight_compare [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (Γ : MixedJ Clock Var) (hΓ : Γ = prependCurrent (.marker ℓ)
      (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
    (child : OwnedPending (boundaryReplacementChild c m ℓ kind I φ
      (.reset (copyActiveResets R (left ++ right)) Γ)) (copyActiveResets R (left ++ right)) W) :
    pendingWeight child.canonical ≤ pendingWeight owned.canonical ∧
      (required = true → pendingWeight child.canonical < pendingWeight owned.canonical) := by
  have hecopy : pendingWeight (boundaryReplacementChild c m ℓ kind I φ
      (.reset (copyActiveResets R (left ++ right)) Γ)) =
      pendingWeight (outsidePending owned.guards R (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
    rw [outsidePending_weight,boundary_child_copy_weight]
    rfl
  have hle := child.regroup_nonincrease
  rw [hecopy] at hle
  cases required with
  | false =>
      have he := optional_boundary_child_weight owned c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ
      exact ⟨hle.trans_eq he,by intro h; cases h⟩
  | true =>
      have he := required_boundary_child_weight owned c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ
      have hlt := lt_of_le_of_lt hle he
      exact ⟨hlt.le,fun _ => hlt⟩

end STLTableau.Section4.Finiteness
