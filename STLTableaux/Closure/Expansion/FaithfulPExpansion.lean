import STLTableaux.Closure.Correctness.GeneralClosureCompleteness

/-! The globally minimal single-predicate step used to guide closure search.
It is included in the revised branchwise relation; it takes only the identity
on a source that is already rule-closed for the selected predicate.
Preservation records source-next alpha conversion explicitly. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ClosureCatalogue

/-- The auxiliary single-predicate step. Membership of p in the current
source is supplied by the surrounding search. -/
def PExpansion (E : ClosureCatalogue Clock Var) (p : Predicate Clock Var)
    (F G : TransitionForm Clock Var) : Prop :=
  (E.RuleClosedFor F p ∧ G = F) ∨
    (¬ E.RuleClosedFor F p ∧ SyntacticallySubsumed F G ∧ E.RuleClosedFor G p ∧
      ∀ H, SyntacticallySubsumed F H → E.RuleClosedFor H p →
        SyntacticallySubsumed H G → SyntacticallySubsumed G H)

/-- Minimize a single-predicate-closed extension inside a fixed upper bound.
All six component names and reset assignments are kept literal here. -/
theorem pExpansion_exists_below (E : ClosureCatalogue Clock Var)
    {F U : TransitionForm Clock Var} (p : Predicate Clock Var)
    (hext : SyntacticallySubsumed F U) (hc : E.RuleClosedFor U p) :
    ∃ G, E.PExpansion p F G ∧ SyntacticallySubsumed G U := by
  classical
  by_cases hcF : E.RuleClosedFor F p
  · exact ⟨F, Or.inl ⟨hcF, rfl⟩, hext⟩
  let Candidate := fun G : TransitionForm Clock Var =>
    SyntacticallySubsumed F G ∧ E.RuleClosedFor G p ∧ SyntacticallySubsumed G U
  obtain ⟨G, hG⟩ := exists_minimalFor_of_wellFoundedLT Candidate
    TransitionForm.componentCount ⟨U, hext, hc, .refl U⟩
  refine ⟨G, Or.inr ⟨hcF, hG.1.1, hG.1.2.1, ?_⟩, hG.1.2.2⟩
  intro H hFH hcH hHG
  have hcount := hHG.componentCount_le
  have hmin := hG.2 ⟨hFH, hcH, hHG.trans hG.1.2.2⟩ hcount
  have heq := hHG.eq_of_componentCount_eq (Nat.le_antisymm hcount hmin)
  subst H
  exact .refl G

theorem PExpansion.extension {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.PExpansion p F G) : SyntacticallySubsumed F G := by
  rcases h with ⟨_, rfl⟩ | ⟨_, h, _⟩
  · exact .refl _
  · exact h

theorem PExpansion.target_ruleClosed {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.PExpansion p F G) : E.RuleClosedFor G p := by
  rcases h with ⟨h, rfl⟩ | ⟨_, _, h, _⟩ <;> exact h

end ClosureCatalogue

namespace ConcreteContextual
open FaithfulClosure

/-- Normalize a satisfied branch after safe next-binder conversion.
Keep the branch witness for refinement relative to that branch. -/
theorem preserving_union_for [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ F.current.locals) (hopen : ¬ catalogue.RuleClosedFor F p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ (e : Equiv.Perm Clock) (B U : TransitionForm Clock Var),
      (∀ N, F.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      SyntacticallySubsumed (F.alphaNext e) U ∧
      catalogue.Branch p (F.alphaNext e).current.resets B ∧ SyntacticallySubsumed B U ∧
      U.holds σ P α k ∧ U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  classical
  have hex : ∃ B, catalogue.Branch p F.current.resets B := by
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
  have hbranch : catalogue.Branch p (F.alphaNext e).current.resets
      (A'.underReset F.current.resets) := ⟨R', A', hR', hA', rfl⟩
  have hstableF : (F.alphaNext e).UnderlyingStable σ P :=
    ((TransitionForm.AlphaEquivalent.next F e hf).underlyingStable σ P).2 hst
  have hstableB : (A'.underReset F.current.resets).UnderlyingStable σ P :=
    (hA'.underlyingStable σ P).2 hRst
  exact ⟨e, _, _, hf, hcon.left, hbranch, hcon.right,
    hsat, hInv, hstableF.union hstableB⟩

/-- Proposition 4.16 and Lemma 4.21, with the
current-predicate premise and source alpha representative explicit. The same
minimal expansion satisfies the judgement and full scoped invariant. -/
theorem satisfied_pExpansion_preserving [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ F.current.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ Fa G, NextAlphaPath F Fa ∧ catalogue.PExpansion p Fa G ∧ G.holds σ P α k ∧
      G.EvaluatedInvariant σ P α k ∧ G.UnderlyingStable σ P := by
  classical
  by_cases hc : catalogue.RuleClosedFor F p
  · exact ⟨F, F, .refl F, Or.inl ⟨hc, rfl⟩, hs, hi, hst⟩
  · obtain ⟨e, B, U, hf, hext, hb, hBU, hsat, hInv, hStable⟩ :=
      preserving_union_for F p hp hc σ P α k hs hi hst
    have hclosed : catalogue.RuleClosedFor U p := Or.inr (branch_rebase hb hBU)
    obtain ⟨G, hG, hGU⟩ := catalogue.pExpansion_exists_below p hext hclosed
    exact ⟨F.alphaNext e, G, .step F e hf (.refl _), hG,
      hGU.sound σ P α k hsat, hGU.evaluatedInvariant σ P α k hInv,
      hGU.underlyingStable σ P hStable⟩

end ConcreteContextual
end STLTableau.Section3
