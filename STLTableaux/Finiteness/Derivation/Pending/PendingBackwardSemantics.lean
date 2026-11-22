import STLTableaux.Finiteness.Derivation.Pending.PendingBackwardStep

/-! Semantic and scope promises preserved when an ordinary tail is assembled
under its inherited reset. No tail-existence premise is used as a conclusion. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem inherited_ordinary_output_facts
    {H : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (hH : SafeNormalization H F) (p : Predicate Clock Var) (R : ClockResetSet Clock)
    (hdRetain : Disjoint F.current.resets.clocks (Section3.Judgement.freeClocks (.predicate p)))
    (hdGuard : Disjoint R.clocks (retainedSource p F).current.guardClocks)
    (A : Set Clock) (hR : Disjoint R.clocks A) (hFA : Disjoint F.current.resets.clocks A)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hp : Judgement.holds σ P (R.apply α) k (.predicate p))
    (hip : ∀hk : k.val < P.size, p.Invariant σ P (R.apply α) k hk)
    (hsp : σ.StablePartition p.formula P)
    (hf : F.holds σ P (R.apply α) k)
    (hif : F.EvaluatedInvariant σ P (R.apply α) k)
    (hsf : F.UnderlyingStable σ P) :
    ((retainedSource p F).underReset R).holds σ P α k ∧
    ((retainedSource p F).underReset R).EvaluatedInvariant σ P α k ∧
    ((retainedSource p F).underReset R).UnderlyingStable σ P ∧
    Disjoint ((retainedSource p F).underReset R).current.resets.clocks A ∧
    ((retainedSource p F).underReset R).current.guards = F.current.guards ∧
    ((retainedSource p F).underReset R).nextPart = F.nextPart := by
  have hSafe : SafeNormalization (.reset R (.conj (.predicate p) H))
      ((retainedSource p F).underReset R) := .reset R (hH.retain_source p hdRetain) hdGuard
  have ht : H.UnderlyingStable σ P := (hH.stable σ P).1 hsf
  refine ⟨(hSafe.holds σ P α k).2 ⟨hp,(hH.holds σ P (R.apply α) k).1 hf⟩,
    (hSafe.fullInvariant σ P α k).2 ⟨hip,(hH.fullInvariant σ P (R.apply α) k).1 hif⟩,
    (hSafe.stable σ P).2 ?_,?_,?_,?_⟩
  · intro φ hφ
    rcases hφ with hφ | hφ
    · have he : φ = p.formula := hφ
      subst φ
      exact hsp
    · exact ht φ hφ
  · change Disjoint (((ClockResetSet.empty.union F.current.resets).union R).clocks) A
    rw [ClockResetSet.clocks_union,ClockResetSet.clocks_union,empty_reset_clocks,Set.empty_union]
    exact hFA.union_left hR
  · change (∅ ∪ F.current.guards) = F.current.guards
    exact Set.empty_union _
  · rfl

end STLTableau.Section4.Finiteness
