import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Backward assembly for an already constructed tail resolution. Retaining a
CURRENT source needs freshness from current resets only; next resets may reuse
its clocks legitimately. No complete resolver existence is assumed or proved. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def retainedSource (p : Predicate Clock Var) (F : Section3.TransitionForm Clock Var) :
    Section3.TransitionForm Clock Var :=
  (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal (.predicate p))).union F

 theorem retainedSource_compatible (p : Predicate Clock Var)
    (F : Section3.TransitionForm Clock Var)
    (hd : Disjoint F.current.resets.clocks
      (Section3.Judgement.freeClocks (.predicate p))) :
    (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal (.predicate p))).UnionCompatible F := by
  apply Section3.TransitionForm.unionCompatible_of_captureFree
  · intro c a b ha
    cases ha
  · apply hd.mono_right
    intro c hc
    rcases hc.1 with ⟨l,hl,hfree⟩ | hfalse
    · have he : l = .predicate p := hl
      subst l
      exact hfree
    · exact False.elim hfalse
  · apply Set.disjoint_left.mpr
    rintro c ⟨a,ha⟩ _
    cases ha
  · intro N M hn
    cases hn
  · intro N M hn
    cases hn
  · intro N M hn
    cases hn

 theorem SafeNormalization.retain_source {H : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (hH : SafeNormalization H F)
    (p : Predicate Clock Var) (hd : Disjoint F.current.resets.clocks
      (Section3.Judgement.freeClocks (.predicate p))) :
    SafeNormalization (.conj (.predicate p) H) (retainedSource p F) :=
  .conj (.predicate p) hH (retainedSource_compatible p F hd)

 theorem retainedSource_projection (p : Predicate Clock Var) (hp : ¬ p.IsAtomic)
    (F : Section3.TransitionForm Clock Var) :
    (retainedSource p F).atomicProjection = F.atomicProjection :=
  DerivationNormalization.projection_add_nonatomic p hp F

 theorem retainedSource_invariant (p : Predicate Clock Var)
    (F : Section3.TransitionForm Clock Var) (hd : Disjoint F.current.resets.clocks
      (Section3.Judgement.freeClocks (.predicate p)))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hp : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hF : F.EvaluatedInvariant σ P α k) :
    (retainedSource p F).EvaluatedInvariant σ P α k := by
  apply (retainedSource_compatible p F hd).evaluatedInvariant σ P α k _ hF
  refine ⟨?_,?_⟩
  · intro l hl
    have he : l = .predicate p := hl
    subst l
    simpa only [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Local.EvaluatedInvariant,Local.toJudgement,
      Section3.Judgement.EvaluatedInvariant,ClockResetSet.apply_empty] using hp
  · intro N hn
    cases hn

 theorem retainedSource_holds (p : Predicate Clock Var)
    (F : Section3.TransitionForm Clock Var) (hd : Disjoint F.current.resets.clocks
      (Section3.Judgement.freeClocks (.predicate p)))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hp : Section3.Judgement.holds σ P α k (.predicate p)) (hF : F.holds σ P α k) :
    (retainedSource p F).holds σ P α k := by
  apply ((retainedSource_compatible p F hd).holds σ P α k).2
  refine ⟨⟨⟨?_,?_⟩,trivial⟩,hF⟩
  · intro g hg
    exact False.elim hg
  · intro l hl
    have he : l = .predicate p := hl
    subst l
    simpa only [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,ClockResetSet.apply_empty,Local.holds,Local.toJudgement] using hp

/-- Backward assembly from the strict smaller pending context's actual tail
resolution and safety certificates. No whole-resolver existence premise. -/
theorem assemble_expandCtx [DecidableEq Clock] {p : Predicate Clock Var}
    {B Γ H A : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (raw : RawBranch p B) (hp : ¬ p.IsAtomic) (fresh : FreshFor p B Γ)
    (tail : Resolve (.conj B Γ) H A)
    (hH : SafeNormalization H F) (hA : SafeNormalization A F.atomicProjection)
    (hd : Disjoint F.current.resets.clocks (Section3.Judgement.freeClocks (.predicate p))) :
    Nonempty (Resolve (.conj (.predicate p) Γ) (.conj (.predicate p) H) A) ∧
      SafeNormalization (.conj (.predicate p) H) (retainedSource p F) ∧
      SafeNormalization A (retainedSource p F).atomicProjection := by
  refine ⟨⟨.expandCtx raw hp fresh tail⟩,hH.retain_source p hd,?_⟩
  rw [retainedSource_projection p hp]
  exact hA

 theorem assemble_expandSolo [DecidableEq Clock] {p : Predicate Clock Var}
    {B H A : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (raw : RawBranch p B) (hp : ¬ p.IsAtomic) (fresh : FreshWithoutContext p B)
    (tail : Resolve B H A)
    (hH : SafeNormalization H F) (hA : SafeNormalization A F.atomicProjection)
    (hd : Disjoint F.current.resets.clocks (Section3.Judgement.freeClocks (.predicate p))) :
    Nonempty (Resolve (.predicate p) (.conj (.predicate p) H) A) ∧
      SafeNormalization (.conj (.predicate p) H) (retainedSource p F) ∧
      SafeNormalization A (retainedSource p F).atomicProjection := by
  refine ⟨⟨.expandSolo raw hp fresh tail⟩,hH.retain_source p hd,?_⟩
  rw [retainedSource_projection p hp]
  exact hA

end STLTableau.Section4.Finiteness
