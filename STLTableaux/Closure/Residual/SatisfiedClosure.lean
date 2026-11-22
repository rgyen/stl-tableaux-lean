/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.ClosureSemantics

/-! # Satisfaction-preserving minimization and conditional closure construction

The remaining local obligation is existence of a satisfied compatible branch.
The purely syntactic branch selection in `BranchExtension` does not discharge it.
-/
namespace STLTableau
open scoped STL
namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Uniform rule completeness with exactly the underlying-formula stability
and current source-invariant assumptions used by the concrete rule catalog. -/
theorem branch_complete {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.Satisfies σ P α k (.predicate p)) : R.BranchSatisfied σ P α k := by
  cases hr with
  | plainAnd φ ψ => exact (ExpansionRule.plainAnd_correct_at φ ψ σ P α k).1 hs
  | plainOr φ ψ => exact ExpansionRule.plainOr_complete_at φ ψ σ P α k hst hs
  | plainUntil φ ψ => exact ExpansionRule.plainUntil_complete_at φ ψ σ P α k hst hs
  | plainRelease φ ψ => exact ExpansionRule.plainRelease_complete_at φ ψ σ P α k hst hs
  | openEventually c I φ => exact (ExpansionRule.openEventually_correct_at c I φ σ P α k).1 hs
  | openAlways c I φ => exact (ExpansionRule.openAlways_correct_at c I φ σ P α k).1 hs
  | upperAlways c d b I φ hcd =>
      exact ExpansionRule.upperAlways_complete_at c d b I φ hcd σ P α k hst hs
  | boundedAlways c d b q I φ hcd =>
      exact ExpansionRule.boundedAlways_complete_at c d b q I φ hcd σ P α k hi hst hs
  | upperEventually c d b I φ hcd =>
      exact ExpansionRule.upperEventually_complete_at c d b I φ hcd σ P α k hi hst hs
  | boundedEventually c d b q I φ hcd =>
      exact ExpansionRule.boundedEventually_complete_at c d b q I φ hcd σ P α k hi hst hs

end ConcreteRule

namespace ExpansionRules
variable {Clock Var : Type*}

theorem satisfied_pExpansion_of_extension {E : ExpansionRules Clock Var}
    {Φ U : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hsub : Φ ⊑ U)
    (hu : E.RuleClosedFor U p) {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P} (hs : U.Satisfies σ P α k) :
    ∃ F, E.PExpansion p Φ F ∧ F.Satisfies σ P α k := by
  obtain ⟨F, hf, hFU⟩ := pExpansion_exists_of_extension hp hsub hu
  exact ⟨F, hf, transitionForm_subsumption_sound hFU hs⟩

/-- The rank argument preserves satisfaction and any invariant property
transported by minimal expansion. Local satisfied extensions are still an
explicit hypothesis; this is not unconditional concrete completeness. -/
theorem satisfied_closure_exists_of_extensions (E : ExpansionRules Clock Var)
    (Property : TransitionForm Clock Var → Prop)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hpreserve : ∀ {p Φ F}, E.PExpansion p Φ F → Property Φ →
      F.Satisfies σ P α k → Property F)
    (hstep : ∀ Φ p, Property Φ → Φ.Satisfies σ P α k →
      Judgement.predicate p ∈ Φ.current.locals → ¬ E.RuleClosedFor Φ p →
      ∃ U, (Φ ⊑ U) ∧ E.RuleClosedFor U p ∧ U.Satisfies σ P α k)
    (Φ : TransitionForm Clock Var) (hprop : Property Φ) (hs : Φ.Satisfies σ P α k) :
    ∃ U, E.IsClosure Φ U ∧ U.Satisfies σ P α k := by
  classical
  have hw : WellFounded (fun F G : TransitionForm Clock Var => RankLT (E.rank F) (E.rank G)) :=
    rankLT_wellFounded.onFun
  have aux : ∀ F : TransitionForm Clock Var, Property F → F.Satisfies σ P α k →
      ∃ U, (F ⊑ U) ∧ E.IsClosed U ∧ U.Satisfies σ P α k := by
    intro F
    induction F using hw.induction with
    | h F ih =>
        intro hpF hsF
        by_cases hc : E.IsClosed F
        · exact ⟨F, syntacticallySubsumed_refl ∅ F (by simp), hc, hsF⟩
        · obtain ⟨p, hp, hopen⟩ : ∃ p, Judgement.predicate p ∈ F.current.locals ∧
              ¬ E.RuleClosedFor F p := by simpa [IsClosed] using hc
          obtain ⟨U, hFU, hu, hsU⟩ := hstep F p hpF hsF hp hopen
          obtain ⟨G, he, hsG⟩ := satisfied_pExpansion_of_extension hp hFU hu hsU
          obtain ⟨V, hGV, hv, hsV⟩ :=
            ih G (he.rankDecrease hopen) (hpreserve he hpF hsG) hsG
          exact ⟨V, he.extension.trans hGV, hv, hsV⟩
  obtain ⟨V, hΦV, hv, hsV⟩ := aux Φ hprop hs
  obtain ⟨U, hu, hUV⟩ := closure_exists_of_closed_extension hΦV hv
  exact ⟨U, hu, transitionForm_subsumption_sound hUV hsV⟩

end ExpansionRules

namespace AlphaBranchRepresentation
variable {Clock Var : Type*} [DecidableEq Clock]

/-- A satisfied branch yields a satisfied minimal expansion when its complete
representation is compatible with the original enclosing form. -/
theorem satisfied_pExpansion_of_compatible_branch
    {Φ B : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    (hΨ : Ψ ∈ R.branches) (hb : AlphaBranchRepresentation Φ.current.resets Ψ B)
    (hc : Φ.UnionCompatible B) {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hs : Φ.Satisfies σ P α k)
    (hsΨ : Judgement.Satisfies σ P (Φ.current.resets.apply α) k Ψ) :
    ∃ U, expansionRules.PExpansion p Φ U ∧ U.Satisfies σ P α k := by
  have hsB := (hb.evaluation σ P α k).1.mpr hsΨ
  have hsU := (Φ.satisfies_union_iff B hc.leftSubsumed hc.rightSubsumed
    hc.currentConsistent hc.nextConsistent σ P α k).mpr ⟨hs, hsB⟩
  apply ExpansionRules.satisfied_pExpansion_of_extension hp hc.leftSubsumed ?_ hsU
  refine ⟨hc.leftSubsumed.currentLocals hp, Or.inr ⟨R, hr, Ψ, hΨ, B, ?_, hc.rightSubsumed⟩⟩
  apply hb.mono hc.leftSubsumed.currentResets
  apply Set.disjoint_left.2
  intro c hextra hfree
  apply Set.disjoint_left.1 hc.leftSubsumed.outerFresh hextra
  refine ⟨Or.inl (Set.mem_iUnion₂.2 ⟨Judgement.predicate p, hp, ?_⟩), hfree.2⟩
  exact hr.branchFreeClocks hΨ hfree.1

/-- Rule completeness supplies the satisfied raw branch. Converting it to a
compatible representation remains an explicit local obligation. -/
theorem satisfied_pExpansion_of_rule_complete
    {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) (hr : ConcreteRule p R)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hi : ∀ hk : k.1 < P.size, IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩)
      (Φ.current.resets.apply α) p)
    (hst : σ.StablePartition p.formula P) (hs : Φ.Satisfies σ P α k)
    (hcompatible : ∀ Ψ ∈ R.branches,
      Judgement.Satisfies σ P (Φ.current.resets.apply α) k Ψ →
      ∃ B, AlphaBranchRepresentation Φ.current.resets Ψ B ∧ Φ.UnionCompatible B) :
    ∃ U, expansionRules.PExpansion p Φ U ∧ U.Satisfies σ P α k := by
  obtain ⟨Ψ, hΨ, hsΨ⟩ := hr.branch_complete σ P (Φ.current.resets.apply α) k
    hi hst (hs.2.1 (.predicate p) hp)
  obtain ⟨B, hb, hc⟩ := hcompatible Ψ hΨ hsΨ
  exact satisfied_pExpansion_of_compatible_branch hp hr hΨ hb hc hs hsΨ

end AlphaBranchRepresentation
end STLTableau
