import STLTableaux.Closure.Correctness.FaithfulClosureCompleteness
import STLTableaux.Closure.Support.BranchFreeClocks
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace FaithfulClosure
theorem preserving_step_free [DecidableEq Clock] [Infinite Clock]
    (S : StateForm Clock Var) (Φ : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hext : SyntacticallySubsumed (TransitionForm.ofState S) Φ)
    (hs : Φ.holds σ P α k) (hi : Φ.EvaluatedInvariant σ P α k)
    (hst : Φ.UnderlyingStable σ P)
    (hfree : Φ.freeClocks ⊆ S.freeClocks)
    (hc : ¬ ConcreteContextual.catalogue.IsClosed Φ) :
    ∃ U, SyntacticallySubsumed (TransitionForm.ofState S) U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P ∧ U.freeClocks ⊆ S.freeClocks ∧
      rank ConcreteContextual.catalogue U < rank ConcreteContextual.catalogue Φ := by
  classical
  obtain ⟨p, hp, hopen⟩ : ∃ p, Local.predicate p ∈ Φ.current.locals ∧
      ¬ ConcreteContextual.catalogue.RuleClosedFor Φ p := by
    obtain ⟨p, hp⟩ := not_forall.mp hc
    exact ⟨p, (Classical.not_imp.mp hp).1, (Classical.not_imp.mp hp).2⟩
  have hex : ∃ B, ConcreteContextual.catalogue.Branch p Φ.current.resets B := by
    by_contra hn
    exact hopen (Or.inl hn)
  obtain ⟨B, R, A, hR, ha, hB⟩ := hex
  have hip : ∀ hk : k.1 < P.size, p.Invariant σ P (Φ.current.resets.apply α) k hk :=
    hi.1 (.predicate p) hp
  have hsp : Judgement.holds σ P (Φ.current.resets.apply α) k (.predicate p) :=
    hs.1.2 (.predicate p) hp
  have hstp : σ.StablePartition p.formula P := hst _ (Or.inl ⟨p, hp, rfl⟩)
  obtain ⟨F, hF, hFs, hFi, hFst⟩ := mixed_raw_complete p ⟨R, hR⟩ σ P
    (Φ.current.resets.apply α) k hip hstp hsp
  obtain ⟨e, Fa, hfix, hFa, hcompat, hsat, hInv⟩ :=
    TransitionForm.contextual_satisfied_union Φ F (FaithfulClosure.mixed_branch_currentGuards_empty hF)
      σ P α k hs hFs hi hFi
  let U := (Φ.alphaNext e).union (Fa.underReset Φ.current.resets)
  have hanchor : SyntacticallySubsumed (TransitionForm.ofState S) (Φ.alphaNext e) :=
    ⟨hext.current, hext.outerFresh, by intro N hn; cases hn⟩
  have hFaBranch : ConcreteContextual.catalogue.Branch p
      (Φ.alphaNext e).current.resets (Fa.underReset Φ.current.resets) :=
    ⟨F, Fa, hF, hFa, rfl⟩
  have hstableSource : (Φ.alphaNext e).UnderlyingStable σ P :=
    ((TransitionForm.AlphaEquivalent.next Φ e hfix).underlyingStable σ P).2 hst
  have hstableBranch : (Fa.underReset Φ.current.resets).UnderlyingStable σ P :=
    (hFa.underlyingStable σ P).2 hFst
  refine ⟨U, hanchor.trans hcompat.left, hsat, hInv, ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [TransitionForm.underlyingFormulas_union] at hψ
    exact hψ.elim (hstableSource ψ) (hstableBranch ψ)
  · intro c hc
    have hu := TransitionForm.freeClocks_union_subset (Φ.alphaNext e)
      (Fa.underReset Φ.current.resets) hc
    apply hfree
    rcases hu with h | h
    · rwa [TransitionForm.alphaNext_freeClocks Φ e hfix] at h
    · have hg : Fa.current.guards = ∅ := by
        exact hFa.current_guards.trans (mixed_branch_currentGuards_empty hF)
      have hf := TransitionForm.freeClocks_underReset_subset Fa Φ.current.resets hg h
      have hfp : c ∈ (Judgement.predicate p).freeClocks :=
        ConcreteMixed.branch_freeClocks hF (hFa.freeClocks ▸ hf.1)
      exact Or.inr ⟨Or.inl ⟨.predicate p, hp, hfp⟩, hf.2⟩
  · have hdecrease := ConcreteContextual.union_rank_decrease (Φ.alphaNext e)
      (Fa.underReset Φ.current.resets) p hp
      (fun h => hopen ((ConcreteContextual.ruleClosed_alphaNext_iff Φ e hfix p).1 h))
      hFaBranch hcompat
    rwa [ConcreteContextual.rank_alphaNext Φ e hfix] at hdecrease

/-- A satisfied generator has a literal minimal faithful closure satisfying
the judgement, the full scoped invariant, and stability of every underlying
formula in both current and successor parts. -/
theorem satisfied_closure_exists_free [DecidableEq Clock] [Infinite Clock]
    (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : S.holds σ P α k) (hi : S.EvaluatedInvariant σ P α k)
    (hst : S.UnderlyingStable σ P) :
    ∃ U, ConcreteContextual.catalogue.IsClosure (TransitionForm.ofState S) U ∧
      U.holds σ P α k ∧ U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P ∧ U.freeClocks ⊆ S.freeClocks := by
  let anchor := TransitionForm.ofState S
  let Q := fun U : TransitionForm Clock Var =>
    SyntacticallySubsumed anchor U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P ∧ U.freeClocks ⊆ S.freeClocks
  have hq : Q anchor :=
    ⟨.refl anchor, ⟨hs, trivial⟩, ⟨hi, by intro N hn; cases hn⟩,
      by simpa only [anchor, TransitionForm.UnderlyingStable,
        TransitionForm.underlyingFormulas_ofState, StateForm.UnderlyingStable] using hst,
      by simpa only [anchor, TransitionForm.freeClocks, TransitionForm.bodyFreeClocks,
        TransitionForm.ofState, Set.union_empty, StateForm.freeClocks] using
        (Set.Subset.refl S.freeClocks)⟩
  have hstep : ∀ U, Q U → ¬ ConcreteContextual.catalogue.IsClosed U →
      ∃ V, Q V ∧ rank ConcreteContextual.catalogue V < rank ConcreteContextual.catalogue U := by
    intro U hU hc
    obtain ⟨V, hext, hsat, hInv, hStable, hFree, hRank⟩ :=
      preserving_step_free S U σ P α k hU.1 hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.2.2.2.2 hc
    exact ⟨V, ⟨hext, hsat, hInv, hStable, hFree⟩, hRank⟩
  have hdown : ∀ U V, SyntacticallySubsumed anchor V → SyntacticallySubsumed V U →
      Q U → Q V := by
    intro U V hAV hVU hU
    exact ⟨hAV, hVU.sound σ P α k hU.2.1,
      hVU.evaluatedInvariant σ P α k hU.2.2.1,
      hVU.underlyingStable σ P hU.2.2.2.1,
      (fun c hc => hU.2.2.2.2 (Or.elim hc
        (fun hg => Or.inl ⟨hg.choose, hVU.current.guards hg.choose_spec.1, hg.choose_spec.2⟩)
        (fun hb => Or.inr (hVU.unboundBody_mono hb))))⟩
  obtain ⟨U, hc, hU⟩ := ConcreteContextual.catalogue.anchored_minimal_closure_of_decreasing_step
    (rank ConcreteContextual.catalogue) Q anchor (fun _ h => h.1) hstep anchor hq hdown
  exact ⟨U, hc, hU.2⟩

end FaithfulClosure
end STLTableau.Section3
