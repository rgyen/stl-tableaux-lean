import STLTableaux.Finiteness.Derivation.Pending.PendingStep
import STLTableaux.Finiteness.Derivation.Pending.PendingNextPrivacy
import STLTableaux.Finiteness.Derivation.Pending.PendingInputSemantics

/-! An actual selected ordinary positive step with a present residual context.
It constructs smaller pending ownership, full truth/invariant preservation and
retained-source protection; it is not yet a recursive completion theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Select an actual preserving rule and construct the smaller child frame.
All source/residual semantic premises are obtained from the given input by
PendingInputSemantics. No child ownership, resolver or target count is assumed. -/
theorem exists_ordinary_child_present
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A) (hNext : NextPrivate J)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (Γ : MixedJ Clock Var)
    (hΓfold : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : p.Ready) (hΓready : Γ.Ready)
    (hip : ∀ hk : k.val < P.size, p.Invariant σ P (R.apply α) k hk)
    (hstp : σ.StablePartition p.formula P)
    (hsp : Judgement.holds σ P (R.apply α) k (.predicate p))
    (hsΓ : Judgement.holds σ P (R.apply α) k Γ)
    (hiΓ : Γ.EvaluatedInvariant σ P (R.apply α) k)
    (hstΓ : Γ.UnderlyingStable σ P) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) Rc W'),
      x ∉ W ∧ RawBranch p B ∧
      FreshFor p B (.reset (copyActiveResets R (left ++ right)) Γ) ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.conj (.predicate p) Γ) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).Ready ∧
      Judgement.holds σ P (R.apply α) k (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).EvaluatedInvariant σ P (R.apply α) k ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).UnderlyingStable σ P ∧
      NextPrivate (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) := by
  let S := copyActiveResets R (left ++ right)
  obtain ⟨x,B,hx,raw,hfresh,hreset,hHistory,hBtrue,hBfull,hBstable⟩ :=
    RawBranch.exists_preserving_history p hp hn (.reset S Γ) W owned.finite_budget
      σ P (R.apply α) k hip hstp hsp
  have hxW : x ∉ W := fun h => hx (Or.inl (Or.inl h))
  have hBsupport := raw.syntaxClocks_subset_source_union_singleton x hreset
  obtain ⟨Rb,Lb,Nb,Cb,hbshape,hBC,hbweight,hlen,hflat,_,hbSafe,hbSource,hbReset⟩ :=
    raw.canonical_with_reset_support
  have hrest := remaining_body_support owned p left right hsplit Γ hΓfold
  have hSW : S.clocks ⊆ W := by
    intro c hc
    have hR : c ∈ R.clocks := by
      have hc' : c ∈ (copyActiveResets R (left ++ right)).clocks := hc
      rw [copyActiveResets_clocks] at hc'
      exact hc'.1
    exact owned.covers_input (Or.inr hR)
  have hSp : Disjoint S.clocks (syntaxClocks (.predicate p)) :=
    (copied_remaining_protected owned A hprotected p left right hsplit).mono_right Set.subset_union_right
  have hSB : Disjoint S.clocks (syntaxClocks B) := by
    apply Set.disjoint_left.2
    intro c hc hcB
    rcases hBsupport hcB with hcp | hcx
    · exact Set.disjoint_left.1 hSp hc hcp
    · have he : c = x := hcx
      subst c
      exact hxW (hSW hc)
  have hRbW : Disjoint Rb.clocks W := hHistory.mono_left (by
    intro c hc
    exact ⟨hbReset hc,fun hs => Set.disjoint_left.1 hbSource hc hs⟩)
  have hc : Rb.Consistent S := ClockResetSet.consistent_of_disjoint (hRbW.mono_right hSW)
  have hL : Disjoint S.clocks Cb.freeClocks :=
    hSB.mono_right ((free_subset_syntax Cb).trans (branch_canonical_support hbshape hBC hbReset))
  have hR : Disjoint Rb.clocks (Γ.freeClocks \ S.clocks) :=
    hRbW.mono_right (Set.sdiff_subset.trans ((free_subset_syntax Γ).trans hrest.1))
  obtain ⟨Cchild,hcshape,hcstruct,hcw⟩ := assemble_child_canonical hbshape hΓfold hc hL hR
  have hregroup : ACIdem (.conj B (.reset S Γ)) Cchild :=
    .trans (.conj hBC (.refl _)) hcstruct
  have hweight : pendingWeight Cchild ≤ pendingWeight (.conj B (.reset S Γ)) := by
    change pendingWeight Cchild ≤ pendingWeight B + pendingWeight Γ
    exact hcw.trans (Nat.add_le_add_right hbweight _)
  obtain ⟨W',child,hWW',hchildProtected,hchildReset⟩ :=
    construct_ordinary_child_owned owned A hA hprotected p left right hsplit x hxW raw
      Rb Lb Nb hbshape hBC hlen hflat hbSafe hbSource hbReset hBsupport hHistory
      (.conj B (.reset S Γ)) Cchild hcshape hregroup hweight
  have hsmall : pendingWeight child.canonical < pendingWeight (.conj (.predicate p) Γ) := by
    apply lt_of_le_of_lt child.regroup_nonincrease
    simpa only [pendingWeight] using raw.pendingWeight_lt_context Γ
  have hsReset : Judgement.holds σ P (R.apply α) k (.reset S Γ) := by
    change Judgement.holds σ P (S.apply (R.apply α)) k Γ
    rw [copyActiveResets_apply_inherited]
    exact hsΓ
  have hiReset : (Section3.Judgement.reset S Γ).EvaluatedInvariant σ P (R.apply α) k := by
    change Γ.EvaluatedInvariant σ P (S.apply (R.apply α)) k
    rw [copyActiveResets_apply_inherited]
    exact hiΓ
  have hstable : (.conj B (.reset S Γ) : MixedJ Clock Var).UnderlyingStable σ P := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact hBstable φ hφ
    · exact hstΓ φ hφ
  have hchildNext := child_nextPrivate owned hNext raw hbshape hBC hcshape
  refine ⟨x,B,_,W',child,hxW,raw,hfresh,hWW',hchildProtected,hchildReset,hsmall,
    ⟨raw.ready hp,hΓready⟩,⟨hBtrue,hsReset⟩,⟨hBfull,hiReset⟩,hstable,?_⟩
  exact hregroup.nextPrivate_iff.2 hchildNext

end STLTableau.Section4.Finiteness
