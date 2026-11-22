import STLTableaux.Closure.Residual.AlphaClosure

namespace STLTableau.ConcreteRule
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

set_option maxHeartbeats 2000000 in
theorem branch_current_subformula {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {B : Judgement Clock Var} (hB : B ∈ R.branches)
    {q : IntervalPredicate Clock Var} (hq : q ∈ B.currentPredicates) :
    q.formula.IsSubformula p.formula := by
  classical
  cases hrule <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr,
      ExpansionRule.plainUntil, ExpansionRule.plainRelease,
      ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways,
      ExpansionRule.upperEventually, ExpansionRule.boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Judgement.currentPredicates, Judgement.markedLT, Judgement.markedGT,
      ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish,
      IntervalPredicate.formula, Formula.or, Formula.release, Formula.untimedUntil,
      Formula.eventually, Formula.always] <;>
    try solve_by_elim (maxDepth := 8) [Formula.IsSubformula.refl, Formula.IsSubformula.neg,
      Formula.IsSubformula.and_left, Formula.IsSubformula.and_right,
      Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]
  all_goals rcases hq with rfl | rfl
  all_goals simp only [IntervalPredicate.formula]
  all_goals solve_by_elim [Formula.IsSubformula.refl, Formula.IsSubformula.and_left,
    Formula.IsSubformula.and_right, Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]

theorem branch_current_stable {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) {B : Judgement Clock Var} (hB : B ∈ R.branches)
    {q : IntervalPredicate Clock Var} (hq : q ∈ B.currentPredicates)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    (hst : σ.StablePartition p.formula P) : σ.StablePartition q.formula P := by
  intro j ψ hψ
  exact hst j ψ (hψ.trans (branch_current_subformula hr hB hq))

end STLTableau.ConcreteRule

namespace STLTableau.AlphaBranchRepresentation
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

theorem expansion_preservesCurrentStability
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {Φ U : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hexp : expansionRules.PExpansion p Φ U)
    (hΦ : ExpansionRules.AllCurrentPredicates Φ (fun q => σ.StablePartition q.formula P)) :
    ExpansionRules.AllCurrentPredicates U (fun q => σ.StablePartition q.formula P) := by
  apply hexp.preservesAllCurrentPredicates hΦ
  intro R Ψ B hR hΨ hB _ q hq
  obtain ⟨B₀, hb, ha⟩ := hB
  have ht := ha.allCurrentPredicates (fun q => σ.StablePartition q.formula P)
    (by
      intro e r
      cases r with
      | plain φ => rfl
      | upper c b kind I φ => cases kind <;> rfl
      | bounded c d b q kind I φ => cases kind <;> rfl)
  apply (ht.2 ?_) q hq
  intro r hr
  exact ConcreteRule.branch_current_stable hR hΨ (hb.currentPredicate_mem r hr) (hΦ p hexp.1)

theorem closure_preservesCurrentStability
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {Φ U : TransitionForm Clock Var} (hc : expansionRules.IsClosure Φ U)
    (hΦ : ExpansionRules.AllCurrentPredicates Φ (fun q => σ.StablePartition q.formula P)) :
    ExpansionRules.AllCurrentPredicates U (fun q => σ.StablePartition q.formula P) :=
  hc.expansionPath.preserve (fun _ he => expansion_preservesCurrentStability he) hΦ

end STLTableau.AlphaBranchRepresentation
