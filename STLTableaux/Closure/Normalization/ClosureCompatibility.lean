import STLTableaux.Closure.Residual.SatisfiedClosure
import STLTableaux.Closure.Residual.BranchExtension

/-! Compatible source representatives for satisfied expansion branches.
Only inherited next binders of the source are freshened; the current source,
its predicate names, and its current reset valuation remain literal.
This discharges local branch compatibility up to the explicit
capture-avoiding representative convention, not for an arbitrary fixed source.
-/
namespace STLTableau
open scoped STL
variable {Clock Var : Type*}

namespace TransitionForm

/-- Choose a permutation that freshens the next reset while fixing the next
locals' free clocks. -/
theorem fresh_next_permutation [Infinite Clock]
    (Φ : TransitionForm Clock Var) (U : Set Clock) (hU : U.Finite)
    (hcurrent : Disjoint Φ.current.resets.clocks U) :
    ∃ e : Equiv.Perm Clock,
      (∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      Disjoint (Φ.alphaNext e).boundClocks U := by
  cases hn : Φ.nextPart with
  | none =>
      exact ⟨Equiv.refl _, by simp, by simpa [alphaNext,boundClocks,hn] using hcurrent⟩
  | some N =>
      obtain ⟨e,he,hd⟩ := exists_fresh_clock_permutation N.resets.clocks
        (N.localClocks \ N.resets.clocks) U N.resets.finite_domain
        N.localClocks_finite.sdiff hU
        (Set.disjoint_left.2 (fun c hc hf => hf.2 hc))
      refine ⟨e,?_,?_⟩
      · intro M hm
        have heq : M = N := Option.some.inj hm.symm
        subst M
        exact he
      · simpa [alphaNext,boundClocks,hn,StateForm.alphaReset,StateForm.rename]
          using hcurrent.union_left hd

/-- Freshen only next binders, retaining the entire current state form. -/
theorem fresh_next_preserving_current [Infinite Clock]
    (Φ : TransitionForm Clock Var) (U : Set Clock) (hU : U.Finite)
    (hcurrent : Disjoint Φ.current.resets.clocks U) :
    ∃ Φa : TransitionForm Clock Var, Φa.AlphaEquivalent Φ ∧
      Φa.current = Φ.current ∧ Disjoint Φa.boundClocks U := by
  obtain ⟨e, hfix, hfresh⟩ := Φ.fresh_next_permutation U hU hcurrent
  exact ⟨Φ.alphaNext e, .next Φ e hfix, rfl, hfresh⟩

end TransitionForm

namespace ConcreteRule
variable [DecidableEq Clock] [Infinite Clock]

theorem branch_current_constraints_empty
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) {Ψ : Judgement Clock Var} (hΨ : Ψ ∈ R.branches)
    {G : TransitionForm Clock Var} (hg : TransitionForm.toTransitionForm? Ψ = some G) :
    G.current.constraints = ∅ := by
  cases hr <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr, ExpansionRule.plainUntil,
      ExpansionRule.plainRelease, ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways, ExpansionRule.upperEventually,
      ExpansionRule.boundedEventually, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish,
      Judgement.markedLT_eq_clock, Judgement.markedGT_eq_clock,
      TransitionForm.toTransitionForm?, TransitionForm.ofState, TransitionForm.ofNextState,
      TransitionForm.prependReset, TransitionForm.union, TransitionForm.unionNext,
      StateForm.ofLocal, StateForm.ofClock, StateForm.empty, StateForm.union] at hg <;>
    subst G <;> rfl

theorem compatible_branch_nextPermutation
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) {Ψ : Judgement Clock Var} (hΨ : Ψ ∈ R.branches)
    (Φ : TransitionForm Clock Var) :
    ∃ (e : Equiv.Perm Clock) (B : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      AlphaBranchRepresentation Φ.current.resets Ψ B ∧ (Φ.alphaNext e).UnionCompatible B := by
  let F := hr.branchTransitionForm hΨ Φ.current.resets
  have hrep : BranchRepresentation Φ.current.resets Ψ F :=
    hr.branchTransitionForm_represents hΨ Φ.current.resets
  have hfree : Disjoint Φ.current.resets.clocks F.freeClocks := by
    apply Set.disjoint_left.2
    intro c hc hf
    have hguard : (Classical.choose (hr.branch_has_transitionForm hΨ)).current.constraints = ∅ :=
      hr.branch_current_constraints_empty hΨ (Classical.choose_spec (hr.branch_has_transitionForm hΨ))
    simp only [F, ConcreteRule.branchTransitionForm, TransitionForm.freeClocks,
      TransitionForm.underReset, hguard, Set.image_empty, Set.empty_union,
      TransitionForm.bodyFreeClocks, ClockResetSet.clocks_union] at hf
    exact hf.2 (Or.inr hc)
  obtain ⟨e,hfix,hleft⟩ := Φ.fresh_next_permutation F.freeClocks F.freeClocks_finite hfree
  obtain ⟨B,hB,hfresh⟩ := F.exists_fresh_alpha (Φ.alphaNext e).allClocks
    (Φ.alphaNext e).allClocks_finite
  refine ⟨e,B,hfix,⟨F,hrep,hB⟩,?_⟩
  apply (Φ.alphaNext e).unionCompatible_of_boundFresh B ?_ hfresh
  apply Set.disjoint_left.2
  intro c hc hb
  rcases hb with hb | hb
  · exact Set.disjoint_left.1 hleft hc (hB.freeClocks ▸ hb)
  · exact Set.disjoint_left.1 hfresh hb (Or.inr hc)

/-- Every branch, including satisfied defer branches with free next clocks,
has compatible representatives while the current source remains unchanged. -/
theorem compatible_branch_preserving_current
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) {Ψ : Judgement Clock Var} (hΨ : Ψ ∈ R.branches)
    (Φ : TransitionForm Clock Var) :
    ∃ Φa B : TransitionForm Clock Var,
      Φa.AlphaEquivalent Φ ∧ Φa.current = Φ.current ∧
      AlphaBranchRepresentation Φ.current.resets Ψ B ∧ Φa.UnionCompatible B := by
  obtain ⟨e, B, hfix, hrep, hcompat⟩ := hr.compatible_branch_nextPermutation hΨ Φ
  exact ⟨Φ.alphaNext e, B, .next Φ e hfix, rfl, hrep, hcompat⟩

end ConcreteRule

namespace AlphaBranchRepresentation
variable [DecidableEq Clock] [Infinite Clock]

theorem satisfied_pExpansion_nextPermutation
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    (hΨ : Ψ ∈ R.branches) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : Φ.Satisfies σ P α k)
    (hbranch : Judgement.Satisfies σ P (Φ.current.resets.apply α) k Ψ) :
    ∃ (e : Equiv.Perm Clock) (U : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      expansionRules.PExpansion p (Φ.alphaNext e) U ∧ U.Satisfies σ P α k := by
  obtain ⟨e,B,hfix,hrep,hcompat⟩ := hr.compatible_branch_nextPermutation hΨ Φ
  obtain ⟨U,hU,hsU⟩ := satisfied_pExpansion_of_compatible_branch (Φ := Φ.alphaNext e) hp hr hΨ hrep hcompat
    ((Φ.alphaNext_equivalent e hfix σ P α k).2 hs) hbranch
  exact ⟨e,U,hfix,hU,hsU⟩

/-- A satisfied branch yields a satisfied minimal expansion of a compatible
representative. -/
theorem satisfied_pExpansion_up_to_alpha
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    (hΨ : Ψ ∈ R.branches) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : Φ.Satisfies σ P α k)
    (hbranch : Judgement.Satisfies σ P (Φ.current.resets.apply α) k Ψ) :
    ∃ Φa U : TransitionForm Clock Var, Φa.AlphaEquivalent Φ ∧
      Φa.current = Φ.current ∧ expansionRules.PExpansion p Φa U ∧ U.Satisfies σ P α k := by
  obtain ⟨e, U, hfix, hU, hsU⟩ :=
    satisfied_pExpansion_nextPermutation hp hr hΨ σ P α k hs hbranch
  exact ⟨Φ.alphaNext e, U, .next Φ e hfix, rfl, hU, hsU⟩

/-- Rule completeness supplies a satisfied minimal expansion after choosing
a compatible source representative. -/
theorem satisfied_pExpansion_of_rule_complete_up_to_alpha
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, IntervalPredicate.Invariant (P.interval ⟨k.1,hk⟩)
      (Φ.current.resets.apply α) p)
    (hst : σ.StablePartition p.formula P) (hs : Φ.Satisfies σ P α k) :
    ∃ Φa U : TransitionForm Clock Var, Φa.AlphaEquivalent Φ ∧
      Φa.current = Φ.current ∧ expansionRules.PExpansion p Φa U ∧ U.Satisfies σ P α k := by
  obtain ⟨Ψ,hΨ,hbranch⟩ := hr.branch_complete σ P (Φ.current.resets.apply α) k
    hi hst (hs.2.1 (.predicate p) hp)
  exact satisfied_pExpansion_up_to_alpha hp hr hΨ σ P α k hs hbranch

/-- A satisfied source has a satisfied minimal expansion up to alpha-equivalence. -/
theorem satisfied_alphaExpansion_of_rule_complete
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, IntervalPredicate.Invariant (P.interval ⟨k.1,hk⟩)
      (Φ.current.resets.apply α) p)
    (hst : σ.StablePartition p.formula P) (hs : Φ.Satisfies σ P α k) :
    ∃ U : TransitionForm Clock Var, expansionRules.AlphaExpansion Φ U ∧ U.Satisfies σ P α k := by
  obtain ⟨Φa,U,hΦ,_,hU,hsU⟩ :=
    satisfied_pExpansion_of_rule_complete_up_to_alpha hp hr σ P α k hi hst hs
  exact ⟨U,⟨p,Φa,U,hΦ,hU,.refl U⟩,hsU⟩

end AlphaBranchRepresentation
end STLTableau
