import STLTableaux.Finiteness.Derivation.Pending.PendingOrdinaryChild

/-! An actual selected ordinary positive step with ABSENT residual context.
The child is the branch B itself; no neutral judgement is inserted. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

omit [DecidableEq Clock] [Infinite Clock] in
private theorem reset_ext {T U : ClockResetSet Clock} (h : T.value = U.value) : T = U := by
  cases T
  cases U
  cases h
  rfl

omit [DecidableEq Clock] [Infinite Clock] in
private theorem copied_empty (R : ClockResetSet Clock) :
    copyActiveResets R ([] : List (Local Clock Var)) = ClockResetSet.empty := by
  apply reset_ext
  funext c
  simp [copyActiveResets,Finiteness.LocalResetSupport.restrictResets,activeSupport,ClockResetSet.empty]

omit [DecidableEq Clock] [Infinite Clock] in
private theorem union_empty_right (R : ClockResetSet Clock) : R.union ClockResetSet.empty = R := by
  apply reset_ext
  funext c
  change (match R.value c with | some a => some a | none => none) = R.value c
  cases R.value c <;> rfl

/-- The singleton-source ordinary step constructs its smaller child and every
semantic premise at the inherited valuation. Freshness protects the ACTUAL
source J during branch selection but never inserts J as a residual context. -/
theorem exists_ordinary_child_solo
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (hAbsent : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = none)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : p.Ready)
    (hip : ∀ hk : k.val < P.size, p.Invariant σ P (R.apply α) k hk)
    (hstp : σ.StablePartition p.formula P)
    (hsp : Judgement.holds σ P (R.apply α) k (.predicate p)) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending B Rc W'),
      x ∉ W ∧ RawBranch p B ∧ FreshWithoutContext p B ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.predicate p) ∧
      B.Ready ∧ Judgement.holds σ P (R.apply α) k B ∧
      B.EvaluatedInvariant σ P (R.apply α) k ∧ B.UnderlyingStable σ P ∧ NextPrivate B := by
  have hempty : left ++ right = [] ∧ owned.nextInputs = [] := by
    simpa only [foldCurrent_none_iff,List.append_eq_nil_iff,List.map_eq_nil_iff] using hAbsent
  obtain ⟨x,B,hx,raw,hfresh,hreset,hHistory,hBtrue,hBfull,hBstable⟩ :=
    RawBranch.exists_preserving_history p hp hn J W owned.finite_budget
      σ P (R.apply α) k hip hstp hsp
  have hxW : x ∉ W := fun h => hx (Or.inl (Or.inl h))
  have hSolo : FreshWithoutContext p B := hfresh.mono_right Set.subset_union_right
  have hBsupport := raw.syntaxClocks_subset_source_union_singleton x hreset
  obtain ⟨Rb,Lb,Nb,Cb,hbshape,hBC,hbweight,hlen,hflat,_,hbSafe,hbSource,hbReset⟩ :=
    raw.canonical_with_reset_support
  have hRc : Rb.union (copyActiveResets R (left ++ right)) = Rb := by
    rw [hempty.1,copied_empty,union_empty_right]
  have hCollected : ∃ Cchild, canonicalSyntax Rb [] (PendingCollection.collect Lb) Nb = some Cchild ∧
      StructuralEq B Cchild ∧ pendingWeight Cchild ≤ pendingWeight B := by
    cases hb : foldCurrent (Lb.map Local.toJudgement ++ Nb.map Section3.Judgement.next) with
    | none => simp [canonicalSyntax,hb,foldCurrent,optionalConj] at hbshape
    | some Kb =>
      have he : .reset Rb Kb = Cb := by
        simpa only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hb,Option.map_some,Option.some.injEq] using hbshape
      subst Cb
      obtain ⟨Kc,hKc,hcollect,hweight,_,_⟩ := PendingCollection.collect_locals Lb Nb Kb hb
      refine ⟨.reset Rb Kc,?_,.trans hBC (.reset Rb hcollect),?_⟩
      · simp only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hKc,Option.map_some]
      · exact hweight.trans hbweight
  obtain ⟨Cchild,hshape,hregroup,hweight⟩ := hCollected
  have hcshape : canonicalSyntax (Rb.union (copyActiveResets R (left ++ right))) []
      (PendingCollection.collect (Lb ++ (left ++ right))) (Nb ++ owned.nextInputs) = some Cchild := by
    rw [hRc]
    simpa only [hempty.1,hempty.2,List.append_nil] using hshape
  obtain ⟨W',child,hWW',hchildProtected,hchildReset⟩ :=
    construct_ordinary_child_owned owned A hA hprotected p left right hsplit x hxW raw
      Rb Lb Nb hbshape hBC hlen hflat hbSafe hbSource hbReset hBsupport hHistory
      B Cchild hcshape hregroup hweight
  have hsmall : pendingWeight child.canonical < pendingWeight (.predicate p) :=
    lt_of_le_of_lt child.regroup_nonincrease raw.pendingWeight_lt_source
  exact ⟨x,B,_,W',child,hxW,raw,hSolo,hWW',hchildProtected,hchildReset,hsmall,
    raw.ready hp,hBtrue,hBfull,hBstable,raw.next_private⟩

end STLTableau.Section4.Finiteness
