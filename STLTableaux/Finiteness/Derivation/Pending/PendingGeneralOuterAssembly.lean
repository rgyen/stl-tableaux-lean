import STLTableaux.Finiteness.Derivation.Pending.PendingOrdinaryBase
import STLTableaux.Finiteness.Derivation.Pending.PendingStep

/-! Outside-guard assembly with an arbitrary additional tail guard footprint.
Original guards remain before the inherited reset, even when names overlap. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem guard_fold_weight_zero (G : List (Section3.Guard Clock))
    (C : MixedJ Clock Var)
    (h : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some C) :
    pendingWeight C = 0 := by
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
      cases g; simpa only [prependCurrent,pendingWeight,Section3.Guard.toJudgement,
        Nat.zero_add] using hz

/-- Outside guards are retained literally and normalized by capture-free
compatibility; no separation from inherited reset names is assumed. -/
theorem assemble_owned_outside_guards_general
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock)
    (Body : MixedJ Clock Var)
    (hBody : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body)
    {H E : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (tail : Resolve (.reset R Body) H E)
    (hH : SafeNormalization H F) (hE : SafeNormalization E F.atomicProjection)
    (hReset : Disjoint F.current.resets.clocks A)
    (hPrivate : nextCurrentPrivate F) (hNextH : NextPrivate H) (hNextE : NextPrivate E)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P)
    (hf : F.holds σ P α k) (hif : F.EvaluatedInvariant σ P α k)
    (hsf : F.UnderlyingStable σ P) (hNextJ : NextPrivate J) :
    ∃ (Hout Eout : MixedJ Clock Var) (Fout : Section3.TransitionForm Clock Var),
      Nonempty (Resolve J Hout Eout) ∧ SafeNormalization Hout Fout ∧
      SafeNormalization Eout Fout.atomicProjection ∧ Fout.holds σ P α k ∧
      Fout.EvaluatedInvariant σ P α k ∧ Fout.UnderlyingStable σ P ∧ Fout.Ready ∧
      NextPrivate Hout ∧ NextPrivate Eout ∧
      Fout.current.guards = currentGuards J ∪ F.current.guards ∧
      Disjoint Fout.current.resets.clocks A ∧ nextCurrentPrivate Fout ∧
      Fout.nextPart = F.nextPart := by
  have hJG : currentGuards J = {g | g ∈ owned.guards} :=
    owned.regroup.currentGuards_eq.trans (canonical_currentGuards owned.shape)
  have hcr := owned.regroup.ready_iff.1 hReady
  have hcs := (owned.regroup.holds_iff σ P α k).1 hHolds
  have hci := (owned.regroup.invariant_iff σ P α k).1 hInv
  have hct := (owned.regroup.stable_iff σ P).1 hStable
  have hcn := owned.regroup.nextPrivate_iff.1 hNextJ
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have he : .reset R Body = owned.canonical := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
    have hGnil : owned.guards = [] := by
      simpa only [List.map_eq_nil_iff] using (foldCurrent_none_iff _).1 hg
    have D : Resolve J H E := .structural (owned.regroup.trans (he ▸ .refl _)) tail
    refine ⟨H,E,F,⟨D⟩,hH,hE,hf,hif,hsf,hH.ready.2 (D.ready hReady).1,
      hNextH,hNextE,?_,hReset,hPrivate,rfl⟩
    rw [hJG,hGnil]
    simp only [List.not_mem_nil,Set.setOf_false,Set.empty_union]
  | some Guards =>
    have he : .conj Guards (.reset R Body) = owned.canonical := by
      simpa only [canonicalSyntax,hg,hBody,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
    rw [← he] at hcr hcs hci hct hcn
    obtain ⟨S,hS,hSr,hSl,hCompatible⟩ := CanonicalSafety.guard_spine owned.guards Guards hg
    have hProjection : (Section3.TransitionForm.ofState S).atomicProjection =
        Section3.TransitionForm.ofState S :=
      PendingCompletionBase.projection_fixed Guards (guard_fold_weight_zero _ _ hg) hS
    have hSafeH : SafeNormalization (.conj Guards H)
        ((Section3.TransitionForm.ofState S).union F) := .conj hS hH (hCompatible F)
    have hSafeE : SafeNormalization (.conj Guards E)
        ((Section3.TransitionForm.ofState S).union F).atomicProjection := by
      rw [DerivationNormalization.projection_union,hProjection]
      exact .conj hS hE (hCompatible F.atomicProjection)
    have D : Resolve J (.conj Guards H) (.conj Guards E) :=
      .structural (owned.regroup.trans (he ▸ .refl _))
        (.conj (PendingCompletionBase.resolve_zero _ (guard_fold_weight_zero _ _ hg)) tail)
    have hTrue : Judgement.holds σ P α k (.conj Guards H) :=
      ⟨hcs.1,(hH.holds σ P α k).1 hf⟩
    have hFull : (.conj Guards H : MixedJ Clock Var).EvaluatedInvariant σ P α k :=
      ⟨hci.1,(hH.fullInvariant σ P α k).1 hif⟩
    have hStableOut : (.conj Guards H : MixedJ Clock Var).UnderlyingStable σ P := by
      intro φ hφ
      rcases hφ with hgφ | hhφ
      · exact hct φ (Or.inl hgφ)
      · exact (hH.stable σ P).1 hsf φ hhφ
    refine ⟨_,_,_,⟨D⟩,hSafeH,hSafeE,(hSafeH.holds σ P α k).2 hTrue,
      (hSafeH.fullInvariant σ P α k).2 hFull,(hSafeH.stable σ P).2 hStableOut,
      hSafeH.ready.2 (D.ready hReady).1,⟨hcn.1,hNextH⟩,⟨hcn.1,hNextE⟩,?_,?_,?_,rfl⟩
    · have hShapeG : canonicalSyntax ClockResetSet.empty owned.guards [] [] = some Guards := by
        simp only [canonicalSyntax,hg,List.map_nil,List.nil_append,foldCurrent,Option.map_none,optionalConj]
      change S.guards ∪ F.current.guards = currentGuards J ∪ F.current.guards
      have hSG : S.guards = currentGuards J :=
        hS.currentGuards_eq.trans ((canonical_currentGuards hShapeG).trans hJG.symm)
      exact congrArg (fun G => G ∪ F.current.guards) hSG
    · change Disjoint (S.resets.union F.current.resets).clocks A
      rw [ClockResetSet.clocks_union,hSr,empty_reset_clocks,Set.empty_union]
      exact hReset
    · exact hPrivate

end STLTableau.Section4.Finiteness
