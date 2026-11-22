import STLTableaux.Finiteness.Derivation.Pending.PendingBackwardSemantics
import STLTableaux.Finiteness.Derivation.NextStatePrivacy

/-! Retention under inherited resets with explicit current-guard noncapture.
New boundary guards are permitted; no original-guard equality is asserted. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

 theorem retainedSource_guardClocks (p : Predicate Clock Var)
    (F : Section3.TransitionForm Clock Var) :
    (retainedSource p F).current.guardClocks = F.current.guardClocks := by
  change {c | ∃g∈(∅ ∪ F.current.guards),g.clock=c} = _
  rw [Set.empty_union]
  rfl

/-- Safe full/erased normalization and all ordinary semantic promises survive
retention and inherited reset when its actual current guards avoid the frame.
The footprint is preserved exactly, including any newly added boundary guards. -/
theorem inherited_retention_output
    {H E : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (hH : SafeNormalization H F) (hE : SafeNormalization E F.atomicProjection)
    (p : Predicate Clock Var) (hp : ¬p.IsAtomic) (hpReady : p.Ready)
    (R : ClockResetSet Clock)
    (hdRetain : Disjoint F.current.resets.clocks (Section3.Judgement.freeClocks (.predicate p)))
    (hdGuard : Disjoint R.clocks F.current.guardClocks)
    (A : Set Clock) (hR : Disjoint R.clocks A) (hFA : Disjoint F.current.resets.clocks A)
    (hPrivate : nextCurrentPrivate F) (hNextH : NextPrivate H) (hNextE : NextPrivate E)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hSource : Judgement.holds σ P (R.apply α) k (.predicate p))
    (hSourceInv : ∀hk : k.val < P.size,p.Invariant σ P (R.apply α) k hk)
    (hSourceStable : σ.StablePartition p.formula P)
    (hf : F.holds σ P (R.apply α) k)
    (hif : F.EvaluatedInvariant σ P (R.apply α) k)
    (hsf : F.UnderlyingStable σ P) (hfReady : F.Ready) :
    SafeNormalization (.reset R (.conj (.predicate p) H)) ((retainedSource p F).underReset R) ∧
    SafeNormalization (.reset R E) ((retainedSource p F).underReset R).atomicProjection ∧
    ((retainedSource p F).underReset R).holds σ P α k ∧
    ((retainedSource p F).underReset R).EvaluatedInvariant σ P α k ∧
    ((retainedSource p F).underReset R).UnderlyingStable σ P ∧
    ((retainedSource p F).underReset R).Ready ∧
    NextPrivate (.reset R (.conj (.predicate p) H)) ∧ NextPrivate (.reset R E) ∧
    nextCurrentPrivate ((retainedSource p F).underReset R) ∧
    Disjoint ((retainedSource p F).underReset R).current.resets.clocks A ∧
    ((retainedSource p F).underReset R).current.guards = F.current.guards ∧
    ((retainedSource p F).underReset R).nextPart = F.nextPart := by
  have hdFull : Disjoint R.clocks (retainedSource p F).current.guardClocks := by
    rw [retainedSource_guardClocks]
    exact hdGuard
  have hFull : SafeNormalization (.reset R (.conj (.predicate p) H))
      ((retainedSource p F).underReset R) := .reset R (hH.retain_source p hdRetain) hdFull
  have hAtomicGuard : F.atomicProjection.current.guardClocks = F.current.guardClocks := rfl
  have hErased : SafeNormalization (.reset R E)
      ((retainedSource p F).underReset R).atomicProjection := by
    rw [DerivationNormalization.projection_underReset,retainedSource_projection p hp]
    exact .reset R hE (hAtomicGuard ▸ hdGuard)
  have facts := inherited_ordinary_output_facts hH p R hdRetain hdFull A hR hFA
    σ P α k hSource hSourceInv hSourceStable hf hif hsf
  refine ⟨hFull,hErased,facts.1,facts.2.1,facts.2.2.1,
    hFull.ready.2 ⟨hpReady,hH.ready.1 hfReady⟩,⟨trivial,hNextH⟩,hNextE,?_,
    facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2⟩
  intro N hn
  rw [facts.2.2.2.2.2] at hn
  exact hPrivate N hn

end STLTableau.Section4.Finiteness
