import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryCopiedChild
import STLTableaux.Finiteness.Derivation.BoundaryReplacementSemantics
import STLTableaux.Finiteness.Derivation.Pending.PendingInputSemantics

/-! The actual selected boundary step at the inherited valuation. The IH
source contains only copied residual resets; outer R and old guards stay out. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem outside_body_facts
    (G : List (Section3.Guard Clock)) (R : ClockResetSet Clock) (K : MixedJ Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hr : (outsidePending G R K).Ready)
    (hs : Judgement.holds σ P α k (outsidePending G R K))
    (hi : (outsidePending G R K).EvaluatedInvariant σ P α k)
    (ht : (outsidePending G R K).UnderlyingStable σ P) :
    K.Ready ∧ Judgement.holds σ P (R.apply α) k K ∧
      K.EvaluatedInvariant σ P (R.apply α) k ∧ K.UnderlyingStable σ P := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
      simp only [outsidePending,hg] at hr hs hi ht
      exact ⟨hr,hs,hi,ht⟩
  | some Guards =>
      simp only [outsidePending,hg] at hr hs hi ht
      exact ⟨hr.2,hs.2,hi.2,fun φ hφ => ht φ (Or.inr hφ)⟩

/-- The selected original input supplies every premise for the copied child;
no child ownership or child semantic fact is an assumption. -/
theorem select_boundary_child
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (hNext : NextPrivate J)
    (A U : Set Clock) (hprotected : protectedActive owned A) (hU : Disjoint R.clocks U)
    (required : Bool) (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (left right rest : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate (.bounded c d m (¬ₘ ℓ) kind I φ) :: right)
    (hselection : (left ++ right).Perm (if required then
      .predicate (.plain (timedFormula kind I φ)) :: .marker ℓ :: rest else .marker ℓ :: rest))
    (hr : R.value d = some 0) (hfrozen : FrozenByUpper c d m ℓ kind I φ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ))
    (hplain : required = false → Judgement.holds σ P (R.apply α) k
      (.predicate (.plain (timedFormula kind I φ)))) :
    ∃ (Γ : MixedJ Clock Var) (child : OwnedPending
      (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ))
      (copyActiveResets R (left ++ right)) W),
      d ∉ Γ.freeClocks ∧
      Γ = prependCurrent (.marker ℓ)
        (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) ∧
      child.guards = boundaryChildGuards c (Marker.imp ℓ m) [] ∧
      child.locals = PendingCollection.collect (.predicate (.upper c m kind I φ) :: .marker ℓ :: .marker ℓ :: rest) ∧
      child.nextInputs = owned.nextInputs ∧
      (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)).Ready ∧
      Judgement.holds σ P (R.apply α) k
        (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)).EvaluatedInvariant σ P (R.apply α) k ∧
      (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)).UnderlyingStable σ P ∧
      NextPrivate (boundaryReplacementChild c m ℓ kind I φ (.reset (copyActiveResets R (left ++ right)) Γ)) ∧
      protectedActive child A ∧ Disjoint (copyActiveResets R (left ++ right)).clocks U ∧
      pendingWeight child.canonical ≤ pendingWeight owned.canonical ∧
      (required = true → pendingWeight child.canonical < pendingWeight owned.canonical) := by
  obtain ⟨Γ,Target,hdΓ,hΓ,htarget,hJT⟩ :
      ∃ Γ Target, d ∉ Γ.freeClocks ∧
        Γ = prependCurrent (.marker ℓ)
          (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)) ∧
        optionalConj (foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))))
          (some (.reset R (boundaryReplacementInput required c d m ℓ kind I φ Γ))) = some Target ∧
        StructuralEq J Target := by
    cases required with
    | false => exact owned_optional_boundary_exposure owned c d m ℓ kind I φ left right rest hsplit hselection hr
    | true => exact owned_required_boundary_exposure owned c d m ℓ kind I φ left right rest hsplit hselection hr
  have hTarget : Target = outsidePending owned.guards R (boundaryReplacementInput required c d m ℓ kind I φ Γ) := by
    cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) <;>
      simpa only [outsidePending,hg,optionalConj,Option.some.injEq] using htarget.symm
  have htr := hJT.ready_iff.1 hReady
  have hts := (hJT.holds_iff σ P α k).1 hHolds
  have hti := (hJT.invariant_iff σ P α k).1 hInv
  have htt := (hJT.stable_iff σ P).1 hStable
  rw [hTarget] at htr hts hti htt
  obtain ⟨hir,his,hii,hit⟩ := outside_body_facts owned.guards R _ σ P α k htr hts hti htt
  have hbr := boundaryReplacement_ready required c d m ℓ kind I φ Γ hir
  have hbs := boundaryReplacement_holds required σ P (R.apply α) k c d m ℓ kind I φ Γ
    hfrozen.distinct hdΓ hc hplain his
  have hbi := boundaryReplacement_invariant required σ P (R.apply α) k c d m ℓ kind I φ Γ
    hfrozen.distinct hdΓ hii
  have hbt := boundaryReplacement_stable required σ P c d m ℓ kind I φ Γ hit
  obtain ⟨child,hG,hL,hNs,hprot,hS,hSU,hNextChild⟩ := construct_copied_boundary_child_owned
    owned hNext A U hprotected hU required c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ
  have hSc : c ∉ (copyActiveResets R (left ++ right)).clocks :=
    fun hx => Set.disjoint_left.1 hS hx (Or.inr (Or.inl rfl))
  have hcopy := boundary_child_copy_reset (copyActiveResets R (left ++ right)) c m ℓ kind I φ Γ hSc
  have hcopiedr := hcopy.ready_iff.1 hbr
  have hcopieds : Judgement.holds σ P (R.apply α) k
      (.reset (copyActiveResets R (left ++ right)) (boundaryReplacementChild c m ℓ kind I φ Γ)) := by
    change Judgement.holds σ P ((copyActiveResets R (left ++ right)).apply (R.apply α)) k _
    rw [copyActiveResets_apply_inherited]
    exact hbs
  have hcopiedi : (.reset (copyActiveResets R (left ++ right))
      (boundaryReplacementChild c m ℓ kind I φ Γ) : MixedJ Clock Var).EvaluatedInvariant σ P (R.apply α) k := by
    change (boundaryReplacementChild c m ℓ kind I φ Γ).EvaluatedInvariant σ P
      ((copyActiveResets R (left ++ right)).apply (R.apply α)) k
    rw [copyActiveResets_apply_inherited]
    exact hbi
  have hcopiedt := (hcopy.stable_iff σ P).1 hbt
  have hw := copied_boundary_child_weight_compare owned required c d m ℓ kind I φ left right rest hsplit hselection Γ hΓ child
  exact ⟨Γ,child,hdΓ,hΓ,hG,hL,hNs,hcopiedr,
    (hcopy.holds_iff σ P (R.apply α) k).1 hcopieds,
    (hcopy.invariant_iff σ P (R.apply α) k).1 hcopiedi,
    hcopiedt,hNextChild,hprot,hSU,hw.1,hw.2⟩

end STLTableau.Section4.Finiteness
