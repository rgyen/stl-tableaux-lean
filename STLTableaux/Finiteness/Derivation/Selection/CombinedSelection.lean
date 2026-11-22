import STLTableaux.Finiteness.Derivation.Selection.SelectedRealization
import STLTableaux.Finiteness.Derivation.Selection.SelectedResetMap
import STLTableaux.Finiteness.Derivation.Selection.EligibilityTransport
import STLTableaux.Finiteness.Derivation.Selection.SelectedPlainConsumption
import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedBoundary
import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedStep
import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedSolo
import STLTableaux.Finiteness.Derivation.CanonicalResetMap
import STLTableaux.Finiteness.Derivation.InheritedRetention
import STLTableaux.Finiteness.Derivation.Pending.PendingGeneralOuterAssembly

/-! Combined maximal boundary-priority selection. The output contains the same
intrinsically indexed tree whose realization is the actual Resolve witness. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

def strictBoundaryGuards (U : Set Clock) : Set (Section3.Guard Clock) :=
  {g | ∃ c∈U, g = ⟨c,.gt,0⟩}

noncomputable def choiceInput {E : Set (Predicate Clock Var)}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) : MixedJ Clock Var :=
  ordinarySelectedInput R (choice.left++choice.right) choice.B
    (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))

/-- Semantic output properties; these are conclusions, never fields of
eligibility or of the syntactic selected tree. -/
def SelectedOutputFacts
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (_owned : OwnedPending J R W) (A U : Set Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (H Er : MixedJ Clock Var)
    (F : Section3.TransitionForm Clock Var) : Prop :=
  SafeNormalization H F ∧ SafeNormalization Er F.atomicProjection ∧
  F.holds σ P α k ∧ F.EvaluatedInvariant σ P α k ∧ F.UnderlyingStable σ P ∧ F.Ready ∧
  NextPrivate H ∧ NextPrivate Er ∧ nextCurrentPrivate F ∧
  F.current.guards ⊆ currentGuards J ∪ strictBoundaryGuards U ∧
  Disjoint F.current.resets.clocks A ∧ ∀c∈W,F.current.resets.value c=R.value c

/-- The very same intrinsically indexed tree supplies actual Resolve and the
raw output indices certified by the semantic conclusions. -/
def SelectedConclusion
    (E : Set (Predicate Clock Var)) {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Prop :=
  ∃ (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
    (_T : SelectedTree E U owned H Er), SelectedOutputFacts owned A U σ P α k H Er F

omit [DecidableEq Clock] in
private def reindex_owned
    {J K : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (h : K=J) : OwnedPending K R W where
  guards := owned.guards
  locals := owned.locals
  nextInputs := owned.nextInputs
  canonical := owned.canonical
  shape := owned.shape
  regroup := by rw [h]; exact owned.regroup
  regroup_nonincrease := by rw [h]; exact owned.regroup_nonincrease
  locals_nodup := owned.locals_nodup
  private_sources := owned.private_sources
  source_next := owned.source_next
  next_private := owned.next_private
  next_flat := owned.next_flat
  absent_body_reset := owned.absent_body_reset
  input_safe := owned.input_safe
  finite_budget := owned.finite_budget
  covers_input := by rw [h]; exact owned.covers_input

private theorem select_ordinary_choice [Infinite Clock]
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock} (owned : OwnedPending J R W)
    (A : Set Clock) (hA : A⊆W) (hProtected : protectedActive owned A) (hNext : NextPrivate J)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals=left++Local.predicate p::right)
    (hMax : MaximalSource owned.locals p) (hAllowed : OrdinaryAllowed E owned.locals p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    ∃ choice : OrdinaryChoice E owned, choice.p=p ∧
      pendingWeight choice.child.canonical < pendingWeight owned.canonical ∧
      (choiceInput owned choice).Ready ∧
      Judgement.holds σ P (R.apply α) k (choiceInput owned choice) ∧
      (choiceInput owned choice).EvaluatedInvariant σ P (R.apply α) k ∧
      (choiceInput owned choice).UnderlyingStable σ P ∧ NextPrivate (choiceInput owned choice) ∧
      currentGuards (choiceInput owned choice) = ∅ ∧
      protectedActive choice.child (A ∪ syntaxClocks (.predicate choice.p)) ∧
      Disjoint choice.childR.clocks (A ∪ syntaxClocks (.predicate choice.p)) := by
  classical
  obtain ⟨x,hx⟩ := owned.finite_budget.exists_notMem
  have hSource := owned_selected_facts owned p left right hsplit σ P α k hReady hHolds hInv hStable
  cases hΓ : foldCurrent ((left++right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    obtain ⟨B,Rc,W',child,hx',raw,hfresh,hreset,hWW,hProtect,hRChild,hSmall,
        hCr,hCt,hCi,hCs,hCn,hAgree,hU,hAbsorb,hOrigin⟩ :=
      exists_ordinary_child_solo_at owned A hA hProtected p left right hsplit hMax.1 x hx hΓ
        σ P α k hSource.1 hSource.2.2.1 hSource.2.2.2.1 hSource.2.1
    let choice : OrdinaryChoice E owned := {
      p:=p,left:=left,right:=right,split:=hsplit,maximal:=hMax,allowed:=hAllowed,
      x:=x,fresh_name:=hx,B:=B,branch:=raw,
      fresh:=by simpa only [ordinarySelectedFresh,hΓ] using hfresh,
      reset_support:=hreset,childR:=Rc,childW:=W',
      child:=reindex_owned child (by simp only [ordinarySelectedInput,hΓ]),
      grows:=hWW,reset_origin:=by simpa only [ordinarySelectedInput,hΓ] using hOrigin,
      old_absorption:=hAbsorb,agreement:=hAgree,fixed_guard_support:=hU }
    refine ⟨choice,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [choice,reindex_owned,owned_selected_solo_weight owned p left right hsplit hΓ] using hSmall
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCr
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCt
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCi
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCs
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCn
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using raw.currentGuards_empty
    · simpa only [choice,reindex_owned,protectedActive] using hProtect
    · exact hRChild
  | some Γ =>
    have hΓfacts := hSource.2.2.2.2 Γ hΓ
    obtain ⟨B,Rc,W',child,hx',raw,hfresh,hreset,hWW,hProtect,hRChild,hSmall,
        hCr,hCt,hCi,hCs,hCn,hAgree,hU,hAbsorb,hOrigin⟩ :=
      exists_ordinary_child_present_at owned A hA hProtected hNext p left right hsplit hMax.1 x hx Γ hΓ
        σ P α k hSource.1 hΓfacts.1 hSource.2.2.1 hSource.2.2.2.1 hSource.2.1
        hΓfacts.2.1 hΓfacts.2.2.1 hΓfacts.2.2.2
    let choice : OrdinaryChoice E owned := {
      p:=p,left:=left,right:=right,split:=hsplit,maximal:=hMax,allowed:=hAllowed,
      x:=x,fresh_name:=hx,B:=B,branch:=raw,
      fresh:=by simpa only [ordinarySelectedFresh,hΓ] using hfresh,
      reset_support:=hreset,childR:=Rc,childW:=W',
      child:=reindex_owned child (by simp only [ordinarySelectedInput,hΓ]),
      grows:=hWW,reset_origin:=by simpa only [ordinarySelectedInput,hΓ] using hOrigin,
      old_absorption:=hAbsorb,agreement:=hAgree,fixed_guard_support:=hU }
    refine ⟨choice,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [choice,reindex_owned,owned_selected_weight owned p left right hsplit Γ hΓ] using hSmall
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCr
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCt
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCi
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCs
    · simpa only [choiceInput,choice,ordinarySelectedInput,hΓ] using hCn
    · change currentGuards (ordinarySelectedInput R (left++right) B
        (foldCurrent ((left++right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) = ∅
      rw [hΓ]
      change currentGuards B ∪ currentGuards Γ = ∅
      rw [raw.currentGuards_empty,residual_guard_empty hΓ,Set.union_empty]
    · simpa only [choice,reindex_owned,protectedActive] using hProtect
    · exact hRChild

omit [DecidableEq Clock] in
private theorem select_boundary_lists
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hBound : Local.predicate (.bounded c d m (¬ₘ ℓ) kind I φ) ∈ owned.locals)
    (hMarker : Local.marker ℓ ∈ owned.locals)
    (hPlain : required=true → Local.predicate (.plain (timedFormula kind I φ)) ∈ owned.locals) :
    ∃left right rest, owned.locals=left++Local.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)::right ∧
      (left++right).Perm (if required then
        .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest) := by
  classical
  obtain ⟨left,right,hsplit⟩ := List.mem_iff_append.mp hBound
  have hm : Local.marker ℓ ∈ left++right := by simpa [hsplit] using hMarker
  cases required with
  | false => exact ⟨left,right,(left++right).erase (.marker ℓ),hsplit,List.perm_cons_erase hm⟩
  | true =>
    have hp : Local.predicate (.plain (timedFormula kind I φ)) ∈ left++right := by
      simpa [hsplit] using hPlain rfl
    have hm' : Local.marker ℓ ∈ (left++right).erase (.predicate (.plain (timedFormula kind I φ))) :=
      (List.mem_erase_of_ne (by intro h; cases h)).2 hm
    exact ⟨left,right,((left++right).erase (.predicate (.plain (timedFormula kind I φ)))).erase (.marker ℓ),
      hsplit,(List.perm_cons_erase hp).trans (.cons _ (List.perm_cons_erase hm'))⟩

noncomputable def boundaryChoiceInput {E : Set (Predicate Clock Var)}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required) : MixedJ Clock Var :=
  boundaryReplacementChild choice.c choice.m choice.ell choice.kind choice.I choice.phi
    (.reset (copyActiveResets R (choice.left++choice.right)) choice.Gamma)

private theorem select_boundary_choice
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock} (owned : OwnedPending J R W)
    (A U : Set Clock) (hProtected : protectedActive owned A) (hRU : Disjoint R.clocks U)
    (hNext : NextPrivate J) (required : Bool) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hBound : Local.predicate (.bounded c d m (¬ₘ ℓ) kind I φ) ∈ owned.locals)
    (hMarker : Local.marker ℓ ∈ owned.locals)
    (hPlain : required=true → Local.predicate (.plain (timedFormula kind I φ)) ∈ owned.locals)
    (hE : Predicate.bounded c d m (¬ₘ ℓ) kind I φ ∈ E)
    (hMax : MaximalSource owned.locals (if required then .plain (timedFormula kind I φ)
      else .bounded c d m (¬ₘ ℓ) kind I φ))
    (hr : R.value d=some 0) (hfrozen : FrozenByUpper c d m ℓ kind I φ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hc : (0:ℝ) <[Marker.imp ℓ m] ((R.apply α) c : ℝ))
    (ht : Judgement.holds σ P (R.apply α) k (.predicate (.plain (timedFormula kind I φ))))
    (hu : Marker.imp ℓ m=○ → c∈U) :
    ∃choice : BoundaryChoice E owned required,
      (boundaryChoiceInput owned choice).Ready ∧
      Judgement.holds σ P (R.apply α) k (boundaryChoiceInput owned choice) ∧
      (boundaryChoiceInput owned choice).EvaluatedInvariant σ P (R.apply α) k ∧
      (boundaryChoiceInput owned choice).UnderlyingStable σ P ∧
      NextPrivate (boundaryChoiceInput owned choice) ∧ protectedActive choice.child A ∧
      Disjoint (copyActiveResets R (choice.left++choice.right)).clocks U ∧
      currentGuards (boundaryChoiceInput owned choice) ⊆ strictBoundaryGuards U ∧
      pendingWeight choice.child.canonical ≤ pendingWeight owned.canonical ∧
      (required=true → pendingWeight choice.child.canonical < pendingWeight owned.canonical) := by
  obtain ⟨left,right,rest,hsplit,hselection⟩ :=
    select_boundary_lists owned required c d m ℓ kind I φ hBound hMarker hPlain
  obtain ⟨Γ,child,hdΓ,hΓ,hG,hL,hNs,hCr,hCt,hCi,hCs,hCn,hProtect,hSU,hWeight,hStrict⟩ :=
    select_boundary_child owned hNext A U hProtected hRU required c d m ℓ kind I φ
      left right rest hsplit hselection hr hfrozen σ P α k hReady hHolds hInv hStable hc (fun _ => ht)
  let choice : BoundaryChoice E owned required := {
    c:=c,d:=d,m:=m,ell:=ℓ,kind:=kind,I:=I,phi:=φ,left:=left,right:=right,rest:=rest,
    split:=hsplit,selection:=hselection,eligible:=hE,maximal:=hMax,right_zero:=hr,frozen:=hfrozen,
    Gamma:=Γ,residual:=hΓ,child:=child }
  refine ⟨choice,hCr,hCt,hCi,hCs,hCn,hProtect,hSU,?_,hWeight,hStrict⟩
  have hΓEmpty : currentGuards Γ=∅ := by
    rw [hΓ]
    cases hrest : foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none => rfl
    | some C =>
      simpa only [prependCurrent,currentGuards,Set.empty_union] using residual_guard_empty hrest
  change currentGuards (boundaryReplacementChild c m ℓ kind I φ
    (.reset (copyActiveResets R (left++right)) Γ)) ⊆ strictBoundaryGuards U
  cases hb : Marker.imp ℓ m with
  | closed =>
    simp only [boundaryReplacementChild,currentGuards,withBoundaryGuard,hb,hΓEmpty,Set.empty_union]
    exact Set.empty_subset _
  | «open» =>
    simp only [boundaryReplacementChild,currentGuards,withBoundaryGuard,hb,hΓEmpty,
      Set.union_empty,Set.empty_union]
    intro g hg
    have he : g=⟨c,.gt,0⟩ := hg
    exact ⟨c,hu hb,he⟩

omit [DecidableEq Clock] in
private theorem reset_protected_of_agreement
    {F : Section3.TransitionForm Clock Var} {R : ClockResetSet Clock} {W A : Set Clock}
    (hmap : ∀c∈W,F.current.resets.value c=R.value c) (hA : A⊆W) (hR : Disjoint R.clocks A) :
    Disjoint F.current.resets.clocks A := by
  apply Set.disjoint_left.2
  rintro c ⟨v,hv⟩ hcA
  have he := hmap c (hA hcA)
  exact Set.disjoint_left.1 hR ⟨v,he.symm.trans hv⟩ hcA

private theorem selected_zero
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock) (hA : A⊆W) (hR : Disjoint R.clocks A)
    (hz : pendingWeight owned.canonical=0) (hNext : NextPrivate J)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : J.Ready)
    (hHolds : Judgement.holds σ P α k J) (hInv : J.EvaluatedInvariant σ P α k)
    (hStable : J.UnderlyingStable σ P) : SelectedConclusion E owned A U σ P α k := by
  obtain ⟨F,hSafe⟩ := owned.input_safe
  let T : SelectedTree E U owned owned.canonical owned.canonical := .zero owned hz
  have hmap := T.normalized_reset_agreement hSafe
  have hn := owned.regroup.nextPrivate_iff.1 hNext
  refine ⟨_,_,F,T,hSafe,PendingCompletionBase.erased_safe _ hz hSafe,
    (hSafe.holds σ P α k).2 ((owned.regroup.holds_iff σ P α k).1 hHolds),
    (hSafe.fullInvariant σ P α k).2 ((owned.regroup.invariant_iff σ P α k).1 hInv),
    (hSafe.stable σ P).2 ((owned.regroup.stable_iff σ P).1 hStable),
    hSafe.ready.2 (T.realize.ready hReady).1,hn,hn,?_,?_,
    reset_protected_of_agreement hmap hA hR,hmap⟩
  · apply canonical_next_state_private owned.shape hSafe owned.next_private
    intro K hK
    exact ((canonical_nextPrivate_iff owned.shape).1 hn K hK).1
  · rw [hSafe.currentGuards_eq,←owned.regroup.currentGuards_eq]
    exact Set.subset_union_left

omit [DecidableEq Clock] in
private theorem guard_spine_weight_zero (G : List (Section3.Guard Clock)) (C : MixedJ Clock Var)
    (h : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var)))=some C) : pendingWeight C=0 := by
  induction G generalizing C with
  | nil => simp [foldCurrent] at h
  | cons g gs ih =>
    rw [List.map_cons,foldCurrent_cons] at h
    have he := Option.some.inj h
    subst C
    cases ht : foldCurrent (gs.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => cases g; rfl
    | some T =>
      have hz := ih T ht
      cases g; simpa only [prependCurrent,pendingWeight,Section3.Guard.toJudgement,Nat.zero_add] using hz

private theorem finish_outside
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock) (hA : A⊆W) (hR : Disjoint R.clocks A)
    (Body : MixedJ Clock Var) (hBody : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next)=some Body)
    {H Er : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (T : SelectedTree E U owned (outsidePending owned.guards R H) (outsidePending owned.guards R Er))
    (hH : SafeNormalization (.reset R H) F) (hEr : SafeNormalization (.reset R Er) F.atomicProjection)
    (hGuards : F.current.guards⊆strictBoundaryGuards U)
    (hPrivate : nextCurrentPrivate F) (hNextH : NextPrivate H) (hNextEr : NextPrivate Er)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : J.Ready)
    (hHolds : Judgement.holds σ P α k J) (hInv : J.EvaluatedInvariant σ P α k)
    (hStable : J.UnderlyingStable σ P) (hNext : NextPrivate J)
    (hf : F.holds σ P α k) (hif : F.EvaluatedInvariant σ P α k)
    (hsf : F.UnderlyingStable σ P) :
    ∃ Fout, SelectedOutputFacts owned A U σ P α k
      (outsidePending owned.guards R H) (outsidePending owned.guards R Er) Fout := by
  have hJG : currentGuards J={g | g∈owned.guards} :=
    owned.regroup.currentGuards_eq.trans (canonical_currentGuards owned.shape)
  have hcs := (owned.regroup.holds_iff σ P α k).1 hHolds
  have hci := (owned.regroup.invariant_iff σ P α k).1 hInv
  have hct := (owned.regroup.stable_iff σ P).1 hStable
  have hcn := owned.regroup.nextPrivate_iff.1 hNext
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have hSafe : SafeNormalization (outsidePending owned.guards R H) F := by
      simpa only [outsidePending,hg] using hH
    have hSafeEr : SafeNormalization (outsidePending owned.guards R Er) F.atomicProjection := by
      simpa only [outsidePending,hg] using hEr
    have hmap := T.normalized_reset_agreement hSafe
    refine ⟨F,hSafe,hSafeEr,hf,hif,hsf,hSafe.ready.2 (T.realize.ready hReady).1,
      ?_,?_,hPrivate,hGuards.trans Set.subset_union_right,
      reset_protected_of_agreement hmap hA hR,hmap⟩
    · simpa only [outsidePending,hg,NextPrivate] using hNextH
    · simpa only [outsidePending,hg,NextPrivate] using hNextEr
  | some G =>
    have he : .conj G (.reset R Body)=owned.canonical := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
    rw [←he] at hcs hci hct hcn
    obtain ⟨S,hS,hSr,hSl,hCompat⟩ := CanonicalSafety.guard_spine owned.guards G hg
    let Fout := (Section3.TransitionForm.ofState S).union F
    have hp : (Section3.TransitionForm.ofState S).atomicProjection=Section3.TransitionForm.ofState S :=
      PendingCompletionBase.projection_fixed G (guard_spine_weight_zero _ _ hg) hS
    have hSafe : SafeNormalization (outsidePending owned.guards R H) Fout := by
      simpa only [outsidePending,hg] using SafeNormalization.conj hS hH (hCompat F)
    have hSafeEr : SafeNormalization (outsidePending owned.guards R Er) Fout.atomicProjection := by
      change SafeNormalization _ ((Section3.TransitionForm.ofState S).union F).atomicProjection
      rw [DerivationNormalization.projection_union,hp]
      simpa only [outsidePending,hg] using SafeNormalization.conj hS hEr (hCompat F.atomicProjection)
    have ht : (outsidePending owned.guards R H).UnderlyingStable σ P := by
      simp only [outsidePending,hg]
      intro φ hφ
      rcases hφ with hgφ | hhφ
      · exact hct φ (Or.inl hgφ)
      · exact (hH.stable σ P).1 hsf φ hhφ
    have hmap := T.normalized_reset_agreement hSafe
    refine ⟨Fout,hSafe,hSafeEr,(hSafe.holds σ P α k).2 ?_,
      (hSafe.fullInvariant σ P α k).2 ?_,(hSafe.stable σ P).2 ht,
      hSafe.ready.2 (T.realize.ready hReady).1,?_,?_,hPrivate,?_,
      reset_protected_of_agreement hmap hA hR,hmap⟩
    · simpa only [outsidePending,hg,Section3.Judgement.holds] using And.intro hcs.1 ((hH.holds σ P α k).1 hf)
    · simpa only [outsidePending,hg,Section3.Judgement.EvaluatedInvariant] using And.intro hci.1 ((hH.fullInvariant σ P α k).1 hif)
    · simpa only [outsidePending,hg,NextPrivate] using And.intro hcn.1 hNextH
    · simpa only [outsidePending,hg,NextPrivate] using And.intro hcn.1 hNextEr
    · have hShapeG : canonicalSyntax ClockResetSet.empty owned.guards [] []=some G := by
        simp only [canonicalSyntax,hg,List.map_nil,List.nil_append,foldCurrent,Option.map_none,optionalConj]
      have hSG : S.guards=currentGuards J :=
        hS.currentGuards_eq.trans ((canonical_currentGuards hShapeG).trans hJG.symm)
      change S.guards ∪ F.current.guards ⊆ _
      rw [hSG]
      exact Set.union_subset Set.subset_union_left (hGuards.trans Set.subset_union_right)

omit [DecidableEq Clock] in
private theorem guard_noncapture
    (R : ClockResetSet Clock) (U : Set Clock) (F : Section3.TransitionForm Clock Var)
    (hRU : Disjoint R.clocks U) (hG : F.current.guards⊆strictBoundaryGuards U) :
    Disjoint R.clocks F.current.guardClocks := by
  apply Set.disjoint_left.2
  rintro c hc ⟨g,hg,hgc⟩
  obtain ⟨x,hx,rfl⟩ := hG hg
  have he : x=c := hgc
  subst c
  exact Set.disjoint_left.1 hRU hc hx

private theorem finish_ordinary
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock) (hA : A⊆W)
    (hRA : Disjoint R.clocks A) (hRU : Disjoint R.clocks U)
    (choice : OrdinaryChoice E owned)
    (hEmpty : currentGuards (choiceInput owned choice)=∅)
    {H Er : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (tail : SelectedTree E U choice.child H Er)
    (facts : SelectedOutputFacts choice.child (A∪syntaxClocks (.predicate choice.p)) U
      σ P (R.apply α) k H Er F)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hNext : NextPrivate J) :
    ∃ Fout, SelectedOutputFacts owned A U σ P α k
      (outsidePending owned.guards R (.conj (.predicate choice.p) H))
      (outsidePending owned.guards R Er) Fout := by
  rcases facts with ⟨hH,hEr,hf,hif,hsf,hFr,hHN,hEN,hPrivate,hG,hReset,hMap⟩
  change F.current.guards⊆currentGuards (choiceInput owned choice) ∪ strictBoundaryGuards U at hG
  rw [hEmpty,Set.empty_union] at hG
  have hSource := owned_selected_facts owned choice.p choice.left choice.right choice.split
    σ P α k hReady hHolds hInv hStable
  have hdRetain := hReset.mono_right ((free_subset_syntax (.predicate choice.p)).trans Set.subset_union_right)
  obtain ⟨hFull,hErased,hTrue,hFullInv,hSt,hRead,hNH,hNE,hPriv,hRA',hGuards,hNextPart⟩ :=
    inherited_retention_output hH hEr choice.p choice.maximal.1 hSource.1 R hdRetain
      (guard_noncapture R U F hRU hG) A hRA (hReset.mono_right Set.subset_union_left)
      hPrivate hHN hEN σ P α k hSource.2.1 hSource.2.2.1 hSource.2.2.2.1 hf hif hsf hFr
  obtain ⟨Body,hBody,hExpose⟩ := owned_selected_exposure owned choice.p choice.left choice.right choice.split
  have T : SelectedTree E U owned _ _ := .ordinary owned choice tail
  exact finish_outside owned A U hA hRA Body hBody T hFull hErased (hGuards ▸ hG)
    hPriv hNH hNE σ P α k hReady hHolds hInv hStable hNext hTrue hFullInv hSt

private theorem finish_boundary
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock) (hA : A⊆W)
    (hRA : Disjoint R.clocks A) (hRU : Disjoint R.clocks U)
    {required : Bool} (choice : BoundaryChoice E owned required)
    (hChildGuards : currentGuards (boundaryChoiceInput owned choice)⊆strictBoundaryGuards U)
    {H Er : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (T : SelectedTree E U owned (outsidePending owned.guards R H) (outsidePending owned.guards R Er))
    (facts : SelectedOutputFacts choice.child A U σ P (R.apply α) k H Er F)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hNext : NextPrivate J) :
    ∃ Fout, SelectedOutputFacts owned A U σ P α k
      (outsidePending owned.guards R H) (outsidePending owned.guards R Er) Fout := by
  rcases facts with ⟨hH,hEr,hf,hif,hsf,hFr,hHN,hEN,hPrivate,hG,hReset,hMap⟩
  have hG' : F.current.guards⊆strictBoundaryGuards U :=
    hG.trans (Set.union_subset hChildGuards (Set.Subset.refl _))
  have hd := guard_noncapture R U F hRU hG'
  have hFull : SafeNormalization (.reset R H) (F.underReset R) := .reset R hH hd
  have hErased : SafeNormalization (.reset R Er) (F.underReset R).atomicProjection :=
    .reset R hEr hd
  have hfR : (F.underReset R).holds σ P α k :=
    (hFull.holds σ P α k).2 ((hH.holds σ P (R.apply α) k).1 hf)
  have hiR : (F.underReset R).EvaluatedInvariant σ P α k :=
    (hFull.fullInvariant σ P α k).2 ((hH.fullInvariant σ P (R.apply α) k).1 hif)
  have hsR : (F.underReset R).UnderlyingStable σ P :=
    (hFull.stable σ P).2 ((hH.stable σ P).1 hsf)
  obtain ⟨Body,hBody,hExpose⟩ := owned_selected_exposure owned
    (.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi)
    choice.left choice.right choice.split
  exact finish_outside owned A U hA hRA Body hBody T hFull hErased hG'
    hPrivate hHN hEN σ P α k hReady hHolds hInv hStable hNext hfR hiR hsR

private theorem forced_upper_maximal
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : BoundaryChoice E owned false) :
    MaximalSource choice.child.locals (.upper choice.c choice.m choice.kind choice.I choice.phi) := by
  refine ⟨by simp [Predicate.IsAtomic],?_⟩
  intro q hq hn
  rcases (boundary_child_current owned choice q).1 hq with he | hr
  · subst q
    exact le_rfl
  · exact choice.maximal.2 q (boundary_rest_subset owned choice hr) hn

private theorem upper_ordinary_allowed
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {U : Set Clock} {σ : FiniteSignal Var}
    {P : IntervalPartition σ.domain} {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    (hE : Eligibility E owned U σ P α k) (choice : BoundaryChoice E owned false) :
    OrdinaryAllowed E choice.child.locals (.upper choice.c choice.m choice.kind choice.I choice.phi) := by
  refine ⟨?_,?_⟩
  · intro he
    exact hE.bounded _ he
  · rintro ⟨q,hq,hm,he⟩
    cases he

/-- Maximal selection gives boundary priority, including immediate expansion
of an optionally extended upper. The same tree realizes the actual raw output. -/
theorem combined_selection_exists [Infinite Clock]
    (E : Set (Predicate Clock Var))
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A U : Set Clock)
    (hA : A⊆W) (hProtected : protectedActive owned A) (hRA : Disjoint R.clocks A)
    (hU : U⊆W) (hRU : Disjoint R.clocks U) (hNext : NextPrivate J)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hReady : J.Ready)
    (hHolds : Judgement.holds σ P α k J) (hInv : J.EvaluatedInvariant σ P α k)
    (hStable : J.UnderlyingStable σ P) (hE : Eligibility E owned U σ P α k) :
    SelectedConclusion E owned A U σ P α k := by
  classical
  have go : ∀ n, ∀{J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
      (owned : OwnedPending J R W) (A : Set Clock) (α : ClockValuation Clock),
      pendingWeight owned.canonical=n → A⊆W → protectedActive owned A → Disjoint R.clocks A →
      U⊆W → Disjoint R.clocks U → NextPrivate J → J.Ready → Judgement.holds σ P α k J →
      J.EvaluatedInvariant σ P α k → J.UnderlyingStable σ P → Eligibility E owned U σ P α k →
      SelectedConclusion E owned A U σ P α k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J R W owned A α hWeight hA hProtected hRA hU hRU hNext hReady hHolds hInv hStable hE
      by_cases hz : pendingWeight owned.canonical=0
      · exact selected_zero owned A U hA hRA hz hNext σ P α k hReady hHolds hInv hStable
      obtain ⟨p,left,right,hsplit,hn,hmax⟩ := owned_select_maximal owned hz
      have hLoc : Local.predicate p∈owned.locals := by rw [hsplit]; simp
      have hMax : MaximalSource owned.locals p := ⟨hn,hmax⟩
      by_cases hReq : ∃q∈E, Local.predicate q∈owned.locals ∧ p=.plain q.formula
      · obtain ⟨q,hq,hqLoc,hp⟩ := hReq
        obtain ⟨c,d,m,ell,kind,I,φ,hqEq,⟨frozen⟩,hMarker,hr,ht,hc,hu⟩ := hE.current q hq hqLoc
        subst q
        have hform : (Predicate.bounded c d m (Marker.complement ell) kind I φ : Predicate Clock Var).formula =
            timedFormula kind I φ := by cases kind <;> rfl
        rw [hform] at hp
        have hPlain : Local.predicate (.plain (timedFormula kind I φ))∈owned.locals := hp ▸ hLoc
        have hMax' : MaximalSource owned.locals (.plain (timedFormula kind I φ)) := hp ▸ hMax
        obtain ⟨choice,hCr,hCt,hCi,hCs,hCn,hProtect,hSU,hCG,hLe,hStrict⟩ :=
          select_boundary_choice owned A U hProtected hRU hNext true c d m ell kind I φ hqLoc hMarker
            (fun _ => hPlain) hq hMax' hr frozen σ P α k hReady hHolds hInv hStable hc ht hu
        have hSRA : Disjoint (copyActiveResets R (choice.left++choice.right)).clocks A := by
          rw [copyActiveResets_clocks]
          exact hRA.mono_left Set.inter_subset_left
        obtain ⟨H,Er,F,T,facts⟩ := ih (pendingWeight choice.child.canonical)
          (by simpa only [←hWeight] using hStrict rfl) choice.child A (R.apply α) rfl
          hA hProtect hSRA hU hSU hCn hCr hCt hCi hCs (hE.boundary choice)
        have Troot : SelectedTree E U owned _ _ := .required owned choice T
        obtain ⟨Fout,hOut⟩ := finish_boundary owned A U hA hRA hRU choice hCG Troot facts
          hReady hHolds hInv hStable hNext
        exact ⟨_,_,Fout,Troot,hOut⟩
      · by_cases hpE : p∈E
        · obtain ⟨c,d,m,ell,kind,I,φ,hpEq,⟨frozen⟩,hMarker,hr,ht,hc,hu⟩ := hE.current p hpE hLoc
          subst p
          obtain ⟨choice,hCr,hCt,hCi,hCs,hCn,hProtect,hSU,hCG,hLe,hStrict⟩ :=
            select_boundary_choice owned A U hProtected hRU hNext false c d m ell kind I φ hLoc hMarker
              (by intro h; cases h) hpE hMax hr frozen σ P α k hReady hHolds hInv hStable hc ht hu
          have huLoc : Local.predicate (.upper choice.c choice.m choice.kind choice.I choice.phi)∈choice.child.locals :=
            (boundary_child_current owned choice _).2 (Or.inl rfl)
          obtain ⟨ul,ur,hupSplit⟩ := List.mem_iff_append.mp huLoc
          obtain ⟨upper,hForced,hSmall,hUr,hUt,hUi,hUs,hUn,hUEmpty,hUProtect,hURA⟩ :=
            select_ordinary_choice choice.child A hA hProtect hCn
              (.upper choice.c choice.m choice.kind choice.I choice.phi) ul ur hupSplit
              (forced_upper_maximal owned choice) (upper_ordinary_allowed owned hE choice)
              σ P (R.apply α) k hCr hCt hCi hCs
          have hA' : A∪syntaxClocks (.predicate upper.p)⊆upper.childW := by
            apply Set.union_subset (hA.trans upper.grows)
            intro z hz
            have hm : Local.predicate upper.p∈choice.child.locals := by rw [upper.split]; simp
            exact upper.grows (choice.child.covers_input
              (Or.inl (Or.inr (canonical_local_support choice.child.shape hm hz))))
          have hU' : U⊆upper.childW := hU.trans upper.grows
          have hRU' := upper.fixed_guard_support U hU hSU
          obtain ⟨H,Er,F,T,facts⟩ := ih (pendingWeight upper.child.canonical)
            (by have hh:=hSmall.trans_le hLe; simpa only [←hWeight] using hh)
            upper.child (A∪syntaxClocks (.predicate upper.p))
            ((copyActiveResets R (choice.left++choice.right)).apply (R.apply α)) rfl
            hA' hUProtect hURA hU' hRU' hUn hUr hUt hUi hUs ((hE.boundary choice).ordinary upper)
          obtain ⟨Fmid,hMid⟩ := finish_ordinary choice.child A U hA
            (hRA.mono_left (by rw [copyActiveResets_clocks]; exact Set.inter_subset_left)) hSU
            upper hUEmpty T facts hCr hCt hCi hCs hCn
          have Troot : SelectedTree E U owned _ _ := .optional owned choice upper hForced T
          obtain ⟨Fout,hOut⟩ := finish_boundary owned A U hA hRA hRU choice hCG Troot hMid
            hReady hHolds hInv hStable hNext
          exact ⟨_,_,Fout,Troot,hOut⟩
        · obtain ⟨choice,hpEq,hSmall,hCr,hCt,hCi,hCs,hCn,hEmpty,hProtect,hRChild⟩ :=
            select_ordinary_choice owned A hA hProtected hNext p left right hsplit hMax ⟨hpE,hReq⟩
              σ P α k hReady hHolds hInv hStable
          have hA' : A∪syntaxClocks (.predicate choice.p)⊆choice.childW := by
            apply Set.union_subset (hA.trans choice.grows)
            intro z hz
            have hm : Local.predicate choice.p∈owned.locals := by rw [choice.split]; simp
            exact choice.grows (owned.covers_input
              (Or.inl (Or.inr (canonical_local_support owned.shape hm hz))))
          obtain ⟨H,Er,F,T,facts⟩ := ih (pendingWeight choice.child.canonical)
            (by simpa only [←hWeight] using hSmall) choice.child
            (A∪syntaxClocks (.predicate choice.p)) (R.apply α) rfl
            hA' hProtect hRChild (hU.trans choice.grows) (choice.fixed_guard_support U hU hRU)
            hCn hCr hCt hCi hCs (hE.ordinary choice)
          obtain ⟨Fout,hOut⟩ := finish_ordinary owned A U hA hRA hRU choice hEmpty T facts
            hReady hHolds hInv hStable hNext
          exact ⟨_,_,Fout,.ordinary owned choice T,hOut⟩
  exact go (pendingWeight owned.canonical) owned A α rfl hA hProtected hRA hU hRU hNext
    hReady hHolds hInv hStable hE

/-- A safely normalized input yields the selected output on its exact state. -/
theorem selected_output_exists [Infinite Clock]
    (E : Set (Predicate Clock Var))
    {N : Section3.StateForm Clock Var} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock}
    (hInput : SafeNormalization J (.ofState N))
    (owned : OwnedPending J R W) (A U : Set Clock)
    (hA : A⊆W) (hProtected : protectedActive owned A) (hRA : Disjoint R.clocks A)
    (hU : U⊆W) (hRU : Disjoint R.clocks U) (hNext : NextPrivate J)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : (Section3.TransitionForm.ofState N).Ready)
    (hHolds : (Section3.TransitionForm.ofState N).holds σ P α k)
    (hInv : (Section3.TransitionForm.ofState N).EvaluatedInvariant σ P α k)
    (hStable : (Section3.TransitionForm.ofState N).UnderlyingStable σ P)
    (hE : Eligibility E owned U σ P α k) :
    ∃ (H Er : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var)
      (_T : SelectedTree E U owned H Er),
      SelectedOutputFacts owned A U σ P α k H Er F ∧
      F.current.guards ⊆ N.guards ∪ strictBoundaryGuards U := by
  obtain ⟨H,Er,F,T,facts⟩ := combined_selection_exists E owned A U hA hProtected hRA hU hRU hNext
    σ P α k (hInput.ready.1 hReady) ((hInput.holds σ P α k).1 hHolds)
    ((hInput.fullInvariant σ P α k).1 hInv) ((hInput.stable σ P).1 hStable) hE
  have hGuard := facts.2.2.2.2.2.2.2.2.2.1
  have hNGuard : N.guards = currentGuards J := hInput.currentGuards_eq
  refine ⟨H,Er,F,T,facts,?_⟩
  rw [hNGuard]
  exact hGuard

end STLTableau.Section4.Finiteness
