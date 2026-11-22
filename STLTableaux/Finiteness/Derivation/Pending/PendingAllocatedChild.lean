import STLTableaux.Finiteness.Derivation.Pending.PendingStep
import STLTableaux.Finiteness.Derivation.Pending.PendingNextPrivacy
import STLTableaux.Finiteness.Derivation.Pending.PendingResetAgreement

/-! Ordinary child construction with a caller-selected reset name or actual
branch. This supplies allocation control, not a finite-pool existence claim. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/- Caller-selected rule parameters need only a nontrivial clock type. -/
theorem RawBranch.select_preserving_at [Nontrivial Clock]
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (x : Clock) (hx : x ∉ syntaxClocks Γ ∪ syntaxClocks (.predicate p))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ B, RawBranch p B ∧ FreshFor p B Γ ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      Judgement.holds σ P α k B ∧ B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B,hB⟩ := RawBranch.exists_of_ready p hp hn
  cases hB with
  | @finite p₀ R rule B₀ _ =>
    obtain ⟨R',hr,hfresh⟩ := finite_fresh_rule_at rule Γ x hx
    have hi₀ : ∀ hk : k.val < P.size, STLTableau.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
    obtain ⟨C,hm,hC,hI⟩ := STLTableau.rule_complete_preserving hr σ P α k hi₀ hst₀
      ((Judgement.holds_ofFinite σ P α k (.predicate p₀)).1 hs)
    exact ⟨_,.finite hr hm,(hfresh C hm).1,(hfresh C hm).2,
      (Judgement.holds_ofFinite σ P α k C).2 hC,
      (Judgement.evaluatedInvariant_ofFinite σ P α k C).2 hI,
      GeneratorStability.finite_branch_stable hr hm σ P hst₀⟩
  | @infinite p₀ Bs rule B₀ _ =>
    obtain ⟨Bs',hr,hfresh⟩ := infinite_fresh_rule_at rule Γ x hx
    have hi₀ : ∀ hk : k.val < P.size, UnboundedClocked.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
    obtain ⟨C,hm,hC,hI⟩ := UnboundedClocked.rule_complete_preserving hr σ P α k hi₀ hst₀
      ((Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).1 hs)
    exact ⟨_,.infinite hr hm,(hfresh C hm).1,(hfresh C hm).2,
      (Judgement.holds_ofUnbounded σ P α k C).2 hC,
      (Judgement.evaluatedInvariant_ofUnbounded σ P α k C).2 hI,
      GeneratorStability.infinite_branch_stable hr hm σ P hst₀⟩
  | opening c m kind a φ =>
    obtain ⟨m',hm⟩ := (UnboundedClocked.opening_correct σ P α k x kind a φ).1
      ((Judgement.holds_ofUnbounded σ P α k (.plain _)).1 hs)
    have hxΓ : x ∉ syntaxClocks Γ := fun h => hx (Or.inl h)
    have hfresh : FreshFor (.plain (UnboundedClocked.formula kind a φ))
        (Judgement.ofUnbounded (UnboundedClocked.opening x m' kind a φ)) Γ := by
      simpa [FreshFor,resetNames,syntaxClocks,Judgement.ofUnbounded,
        UnboundedClocked.opening,Set.disjoint_left] using hxΓ
    have hreset : resetNames (Judgement.ofUnbounded (UnboundedClocked.opening x m' kind a φ)) ⊆
        syntaxClocks (.predicate (.plain (UnboundedClocked.formula kind a φ))) ∪ {x} := by
      simp [resetNames,syntaxClocks,Judgement.ofUnbounded,UnboundedClocked.opening]
    exact ⟨_,.opening x m' kind a φ,hfresh,hreset,
      (Judgement.holds_ofUnbounded σ P α k _).2 hm,
      (Judgement.evaluatedInvariant_ofUnbounded σ P α k _).2
        (UnboundedClocked.opening_preserves σ P α k x m' kind a φ hm),
      GeneratorStability.opening_branch_stable x m' kind a φ σ P hst⟩

/-- Reconstruct the actual child for a supplied branch. Its semantic premises
are supplied by actual rule completeness in the caller-name wrapper below. -/
theorem ordinary_child_present_selected
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A) (hNext : NextPrivate J)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right)
    (Γ : MixedJ Clock Var)
    (hΓfold : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : p.Ready) (hΓready : Γ.Ready)
    (hsΓ : Judgement.holds σ P (R.apply α) k Γ)
    (hiΓ : Γ.EvaluatedInvariant σ P (R.apply α) k)
    (hstΓ : Γ.UnderlyingStable σ P)
    (x : Clock) (hxW : x ∉ W) (B : MixedJ Clock Var) (raw : RawBranch p B)
    (hfresh : FreshFor p B (.reset (copyActiveResets R (left ++ right)) Γ))
    (hreset : resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x})
    (hBtrue : Judgement.holds σ P (R.apply α) k B)
    (hBfull : B.EvaluatedInvariant σ P (R.apply α) k)
    (hBstable : B.UnderlyingStable σ P) :
    ∃ (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) Rc W'),
      x ∉ W ∧ RawBranch p B ∧
      FreshFor p B (.reset (copyActiveResets R (left ++ right)) Γ) ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.conj (.predicate p) Γ) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).Ready ∧
      Judgement.holds σ P (R.apply α) k (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).EvaluatedInvariant σ P (R.apply α) k ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).UnderlyingStable σ P ∧
      NextPrivate (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (∀ c ∈ activeSupport (left ++ right), Rc.value c = R.value c) ∧
      (∀ U, U ⊆ W → Disjoint R.clocks U → Disjoint Rc.clocks U) ∧
      (∀ c∈W, (Rc.union R).value c = R.value c) ∧
      Rc=currentResetMap (.conj B (.reset (copyActiveResets R (left++right)) Γ)) := by
  let S := copyActiveResets R (left ++ right)
  have hHistory : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W := by
    apply Set.disjoint_left.2
    intro c hc hcW
    rcases hreset hc.1 with hcp | hcx
    · exact hc.2 hcp
    · have he : c = x := hcx
      subst c
      exact hxW hcW
  have hBsupport := raw.syntaxClocks_subset_source_union_singleton x hreset
  obtain ⟨Rb,Lb,Nb,Cb,hbshape,hBC,hbweight,hlen,hflat,_,hbSafe,hbSource,hbReset,hRbMap⟩ :=
    raw.canonical_with_exact_reset_map
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
  refine ⟨_,W',child,hxW,raw,hfresh,hreset,hWW',hchildProtected,hchildReset,hsmall,
    ⟨raw.ready hp,hΓready⟩,⟨hBtrue,hsReset⟩,⟨hBfull,hiReset⟩,hstable,?_,?_,?_,?_,?_⟩
  · exact hregroup.nextPrivate_iff.2 hchildNext
  · exact ordinary_child_common_reset_agrees owned p left right hsplit Rb hRbW
  · intro U hU hRU
    exact ordinary_child_reset_avoids_fixed_set R Rb (left ++ right) W U x hxW hU hRU
      hbSource hbReset hBsupport
  · exact ordinary_child_inherited_reset_agrees R Rb (left++right) W hRbW
  · change Rb.union S = (currentResetMap B).union ((currentResetMap Γ).union S)
    rw [hRbMap,fold_locals_next_reset_map_empty (left++right) owned.nextInputs hΓfold]
    rfl

/-- Fix the newly introduced rule name before selecting the preserving branch.
No infinite clock supply or finite-pool existence assertion is used. -/
theorem exists_ordinary_child_present_at [Nontrivial Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A) (hNext : NextPrivate J)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (x : Clock) (hxW : x ∉ W)
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
    ∃ (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) Rc W'),
      x ∉ W ∧ RawBranch p B ∧
      FreshFor p B (.reset (copyActiveResets R (left ++ right)) Γ) ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.conj (.predicate p) Γ) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).Ready ∧
      Judgement.holds σ P (R.apply α) k (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).EvaluatedInvariant σ P (R.apply α) k ∧
      (.conj B (.reset (copyActiveResets R (left ++ right)) Γ) : MixedJ Clock Var).UnderlyingStable σ P ∧
      NextPrivate (.conj B (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (∀ c ∈ activeSupport (left ++ right), Rc.value c = R.value c) ∧
      (∀ U, U ⊆ W → Disjoint R.clocks U → Disjoint Rc.clocks U) ∧
      (∀ c∈W, (Rc.union R).value c = R.value c) ∧
      Rc=currentResetMap (.conj B (.reset (copyActiveResets R (left++right)) Γ)) := by
  let S := copyActiveResets R (left ++ right)
  have hpW : syntaxClocks (.predicate p) ⊆ W := by
    have hm : Local.predicate p ∈ owned.locals := by rw [hsplit]; simp
    intro c hc
    exact owned.covers_input (Or.inl (Or.inr (canonical_local_support owned.shape hm hc)))
  have hΓW := (remaining_body_support owned p left right hsplit Γ hΓfold).1
  have hSW : S.clocks ⊆ W := by
    intro c hc
    have hc' : c ∈ (copyActiveResets R (left ++ right)).clocks := hc
    rw [copyActiveResets_clocks] at hc'
    exact owned.covers_input (Or.inr hc'.1)
  have hxFresh : x ∉ syntaxClocks (.reset S Γ) ∪ syntaxClocks (.predicate p) := by
    rintro (hcontext | hsource)
    · rcases hcontext with hS | hΓ
      · exact hxW (hSW hS)
      · exact hxW (hΓW hΓ)
    · exact hxW (hpW hsource)
  obtain ⟨B,raw,hfresh,hreset,hBtrue,hBfull,hBstable⟩ :=
    RawBranch.select_preserving_at p hp hn (.reset S Γ) x hxFresh σ P (R.apply α) k hip hstp hsp
  obtain ⟨Rc,W',child,h⟩ := ordinary_child_present_selected owned A hA hprotected hNext
    p left right hsplit Γ hΓfold σ P α k hp hΓready hsΓ hiΓ hstΓ
    x hxW B raw hfresh hreset hBtrue hBfull hBstable
  exact ⟨B,Rc,W',child,h⟩

omit [DecidableEq Clock] in
private theorem reset_ext {T U : ClockResetSet Clock} (h : T.value = U.value) : T = U := by
  cases T
  cases U
  cases h
  rfl

omit [DecidableEq Clock] in
private theorem copied_empty (R : ClockResetSet Clock) :
    copyActiveResets R ([] : List (Local Clock Var)) = ClockResetSet.empty := by
  apply reset_ext
  funext c
  simp [copyActiveResets,Finiteness.LocalResetSupport.restrictResets,activeSupport,ClockResetSet.empty]

omit [DecidableEq Clock] in
private theorem union_empty_right (R : ClockResetSet Clock) : R.union ClockResetSet.empty = R := by
  apply reset_ext
  funext c
  change (match R.value c with | some a => some a | none => none) = R.value c
  cases R.value c <;> rfl


/-- Singleton child construction for an actual selected branch. -/
theorem ordinary_child_solo_selected
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right)
    (hAbsent : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = none)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : p.Ready)
    (x : Clock) (hxW : x ∉ W) (B : MixedJ Clock Var) (raw : RawBranch p B)
    (hSolo : FreshWithoutContext p B)
    (hreset : resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x})
    (hBtrue : Judgement.holds σ P (R.apply α) k B)
    (hBfull : B.EvaluatedInvariant σ P (R.apply α) k)
    (hBstable : B.UnderlyingStable σ P) :
    ∃ (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending B Rc W'),
      x ∉ W ∧ RawBranch p B ∧ FreshWithoutContext p B ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.predicate p) ∧
      B.Ready ∧ Judgement.holds σ P (R.apply α) k B ∧
      B.EvaluatedInvariant σ P (R.apply α) k ∧ B.UnderlyingStable σ P ∧ NextPrivate B ∧
      (∀ c ∈ activeSupport (left ++ right), Rc.value c = R.value c) ∧
      (∀ U, U ⊆ W → Disjoint R.clocks U → Disjoint Rc.clocks U) ∧
      (∀ c∈W, (Rc.union R).value c = R.value c) ∧
      Rc=currentResetMap B := by
  have hempty : left ++ right = [] ∧ owned.nextInputs = [] := by
    simpa only [foldCurrent_none_iff,List.append_eq_nil_iff,List.map_eq_nil_iff] using hAbsent
  have hHistory : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W := by
    apply Set.disjoint_left.2
    intro c hc hcW
    rcases hreset hc.1 with hcp | hcx
    · exact hc.2 hcp
    · have he : c = x := hcx
      subst c
      exact hxW hcW
  have hBsupport := raw.syntaxClocks_subset_source_union_singleton x hreset
  obtain ⟨Rb,Lb,Nb,Cb,hbshape,hBC,hbweight,hlen,hflat,_,hbSafe,hbSource,hbReset,hRbMap⟩ :=
    raw.canonical_with_exact_reset_map
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
  have hRbW : Disjoint Rb.clocks W := hHistory.mono_left (by
    intro c hc
    exact ⟨hbReset hc,fun hs => Set.disjoint_left.1 hbSource hc hs⟩)
  refine ⟨_,W',child,hxW,raw,hSolo,hreset,hWW',hchildProtected,hchildReset,hsmall,
    raw.ready hp,hBtrue,hBfull,hBstable,raw.next_private,?_,?_,?_,?_⟩
  · exact ordinary_child_common_reset_agrees owned p left right hsplit Rb hRbW
  · intro U hU hRU
    exact ordinary_child_reset_avoids_fixed_set R Rb (left ++ right) W U x hxW hU hRU
      hbSource hbReset hBsupport
  · exact ordinary_child_inherited_reset_agrees R Rb (left++right) W hRbW
  · exact hRc.trans hRbMap

/-- Caller-selected rule clock for literal singleton resolution. -/
theorem exists_ordinary_child_solo_at [Nontrivial Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (x : Clock) (hxW : x ∉ W)
    (hAbsent : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = none)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hp : p.Ready)
    (hip : ∀ hk : k.val < P.size, p.Invariant σ P (R.apply α) k hk)
    (hstp : σ.StablePartition p.formula P)
    (hsp : Judgement.holds σ P (R.apply α) k (.predicate p)) :
    ∃ (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending B Rc W'),
      x ∉ W ∧ RawBranch p B ∧ FreshWithoutContext p B ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight (.predicate p) ∧
      B.Ready ∧ Judgement.holds σ P (R.apply α) k B ∧
      B.EvaluatedInvariant σ P (R.apply α) k ∧ B.UnderlyingStable σ P ∧ NextPrivate B ∧
      (∀ c ∈ activeSupport (left ++ right), Rc.value c = R.value c) ∧
      (∀ U, U ⊆ W → Disjoint R.clocks U → Disjoint Rc.clocks U) ∧
      (∀ c∈W, (Rc.union R).value c = R.value c) ∧
      Rc=currentResetMap B := by
  have hpW : syntaxClocks (.predicate p) ⊆ W := by
    have hm : Local.predicate p ∈ owned.locals := by rw [hsplit]; simp
    intro c hc
    exact owned.covers_input (Or.inl (Or.inr (canonical_local_support owned.shape hm hc)))
  have hxFresh : x ∉ syntaxClocks J ∪ syntaxClocks (.predicate p) := by
    rintro (hJ | hp)
    · exact hxW (owned.covers_input (Or.inl (Or.inl hJ)))
    · exact hxW (hpW hp)
  obtain ⟨B,raw,hfresh,hreset,hBtrue,hBfull,hBstable⟩ :=
    RawBranch.select_preserving_at p hp hn J x hxFresh σ P (R.apply α) k hip hstp hsp
  obtain ⟨Rc,W',child,h⟩ := ordinary_child_solo_selected owned A hA hprotected
    p left right hsplit hAbsent σ P α k hp x hxW B raw
    (hfresh.mono_right Set.subset_union_right) hreset hBtrue hBfull hBstable
  exact ⟨B,Rc,W',child,h⟩

end STLTableau.Section4.Finiteness
