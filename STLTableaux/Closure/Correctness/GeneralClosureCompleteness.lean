import STLTableaux.Closure.Correctness.FaithfulClosureCompleteness

/-! Faithful closure completeness for arbitrary transition forms. Existing
next binders may require alpha conversion before literal minimization; the
inherited current reset and current predicates are never renamed. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

/-- A finite sequence of capture-avoiding conversions of existing next
binders. No semantic or closure property is a constructor. -/
inductive NextAlphaPath : TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | refl (F) : NextAlphaPath F F
  | step (F) (e : Equiv.Perm Clock)
      (hf : ∀ N, F.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
      {G} : NextAlphaPath (F.alphaNext e) G → NextAlphaPath F G

namespace NextAlphaPath

theorem trans {F G H : TransitionForm Clock Var} (h : NextAlphaPath F G)
    (g : NextAlphaPath G H) : NextAlphaPath F H := by
  induction h with
  | refl => exact g
  | step F e hf tail ih => exact .step F e hf (ih g)

theorem alphaEquivalent {F G : TransitionForm Clock Var} (h : NextAlphaPath F G) :
    TransitionForm.AlphaEquivalent G F := by
  induction h with
  | refl => exact .refl _
  | step F e hf tail ih => exact ih.trans (.next F e hf)

theorem current {F G : TransitionForm Clock Var} (h : NextAlphaPath F G) :
    G.current = F.current := by
  induction h with
  | refl => rfl
  | step F e hf tail ih => exact ih

/-- Transport the smaller source along the larger form's binder
conversions. The next no-capture clause supplies source-safe permutations. -/
theorem transport_subsumed {F G Ga : TransitionForm Clock Var}
    (h : SyntacticallySubsumed F G) (hp : NextAlphaPath G Ga) :
    ∃ Fa, NextAlphaPath F Fa ∧ SyntacticallySubsumed Fa Ga := by
  induction hp generalizing F with
  | refl => exact ⟨F, .refl F, h⟩
  | step G e hf tail ih =>
      obtain ⟨Fa, hpF, hsub⟩ := ih (h.alphaNext e hf)
      exact ⟨Fa, .step F e (h.next_fix_of_subsumed e hf) hpF, hsub⟩

end NextAlphaPath

namespace GeneralClosure
open FaithfulClosure

/-- One invariant-preserving step for a source with a next component.
The source's next representative is explicit in the conclusion. -/
theorem preserving_step [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) (hc : ¬ ConcreteContextual.catalogue.IsClosed F) :
    ∃ (e : Equiv.Perm Clock) (U : TransitionForm Clock Var),
      (∀ N, F.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      SyntacticallySubsumed (F.alphaNext e) U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P ∧
      rank ConcreteContextual.catalogue U < rank ConcreteContextual.catalogue F := by
  classical
  obtain ⟨p, hp, hopen⟩ : ∃ p, Local.predicate p ∈ F.current.locals ∧
      ¬ ConcreteContextual.catalogue.RuleClosedFor F p := by
    obtain ⟨p, hp⟩ := not_forall.mp hc
    exact ⟨p, (Classical.not_imp.mp hp).1, (Classical.not_imp.mp hp).2⟩
  have hex : ∃ B, ConcreteContextual.catalogue.Branch p F.current.resets B := by
    by_contra hn
    exact hopen (Or.inl hn)
  obtain ⟨B, R, A, hR, ha, hB⟩ := hex
  have hip : ∀ hk : k.1 < P.size, p.Invariant σ P (F.current.resets.apply α) k hk :=
    hi.1 (.predicate p) hp
  have hsp : Judgement.holds σ P (F.current.resets.apply α) k (.predicate p) :=
    hs.1.2 (.predicate p) hp
  have hstp : σ.StablePartition p.formula P := hst _ (Or.inl ⟨p, hp, rfl⟩)
  obtain ⟨R', hR', hRs, hRi, hRst⟩ := mixed_raw_complete p ⟨R, hR⟩ σ P
    (F.current.resets.apply α) k hip hstp hsp
  obtain ⟨e, A', hf, hA', hcon, hsat, hInv⟩ :=
    TransitionForm.contextual_satisfied_union F R' (mixed_branch_currentGuards_empty hR')
      σ P α k hs hRs hi hRi
  have hbranch : ConcreteContextual.catalogue.Branch p
      (F.alphaNext e).current.resets (A'.underReset F.current.resets) :=
    ⟨R', A', hR', hA', rfl⟩
  have hstableF : (F.alphaNext e).UnderlyingStable σ P :=
    ((TransitionForm.AlphaEquivalent.next F e hf).underlyingStable σ P).2 hst
  have hstableB : (A'.underReset F.current.resets).UnderlyingStable σ P :=
    (hA'.underlyingStable σ P).2 hRst
  refine ⟨e, _, hf, hcon.left, hsat, hInv, hstableF.union hstableB, ?_⟩
  have hdec := ConcreteContextual.union_rank_decrease (F.alphaNext e)
    (A'.underReset F.current.resets) p hp
    (fun h => hopen ((ConcreteContextual.ruleClosed_alphaNext_iff F e hf p).1 h))
    hbranch hcon
  rwa [ConcreteContextual.rank_alphaNext F e hf] at hdec

/-- General faithful completeness, with the source representative recorded.
This theorem does not identify literal subsumption with alpha equivalence. -/
theorem satisfied_alpha_closure_exists [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ Fa U, NextAlphaPath F Fa ∧ ConcreteContextual.catalogue.IsClosure Fa U ∧
      U.holds σ P α k ∧ U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  have hw : WellFounded (fun A B : TransitionForm Clock Var =>
      rank ConcreteContextual.catalogue A < rank ConcreteContextual.catalogue B) :=
    (measure (rank ConcreteContextual.catalogue)).wf
  have aux : ∀ G : TransitionForm Clock Var,
      G.holds σ P α k → G.EvaluatedInvariant σ P α k → G.UnderlyingStable σ P →
      ∃ Ga V, NextAlphaPath G Ga ∧ SyntacticallySubsumed Ga V ∧
        ConcreteContextual.catalogue.IsClosed V ∧ V.holds σ P α k ∧
        V.EvaluatedInvariant σ P α k ∧ V.UnderlyingStable σ P := by
    intro G
    induction G using hw.induction with
    | h G ih =>
      intro hsG hiG hstG
      by_cases hcG : ConcreteContextual.catalogue.IsClosed G
      · exact ⟨G, G, .refl G, .refl G, hcG, hsG, hiG, hstG⟩
      · obtain ⟨e, V, hf, hsub, hsV, hiV, hstV, hlt⟩ :=
          preserving_step G σ P α k hsG hiG hstG hcG
        obtain ⟨Va, W, hpV, hVW, hcW, hsW, hiW, hstW⟩ := ih V hlt hsV hiV hstV
        obtain ⟨Ga, hpG, hGa⟩ := NextAlphaPath.transport_subsumed hsub hpV
        exact ⟨Ga, W, .step G e hf hpG, hGa.trans hVW, hcW, hsW, hiW, hstW⟩
  obtain ⟨Fa, V, hp, hsub, hcV, hsV, hiV, hstV⟩ := aux F hs hi hst
  obtain ⟨U, hcU, hUV⟩ := ConcreteContextual.catalogue.exists_minimal_closed_extension_below
    hsub hcV
  exact ⟨Fa, U, hp, hcU, hUV.sound σ P α k hsV,
    hUV.evaluatedInvariant σ P α k hiV, hUV.underlyingStable σ P hstV⟩

/-- Theorem 4.22 (closure completeness) up to renaming of the next reset
clocks. The representative is alpha-equivalent to the source and has
the same current state, including the inherited resets. -/
theorem satisfied_closure_exists_up_to_next_alpha [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ Fa U, TransitionForm.AlphaEquivalent Fa F ∧ Fa.current = F.current ∧
      ConcreteContextual.catalogue.IsClosure Fa U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  obtain ⟨Fa, U, hp, hc, hsat, hInv, hStable⟩ :=
    satisfied_alpha_closure_exists F σ P α k hs hi hst
  exact ⟨Fa, U, hp.alphaEquivalent, hp.current, hc, hsat, hInv, hStable⟩

end GeneralClosure
end STLTableau.Section3
