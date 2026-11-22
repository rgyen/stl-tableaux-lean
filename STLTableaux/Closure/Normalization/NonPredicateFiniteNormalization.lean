import STLTableaux.Semantics.Invariants.NumericInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace ConcreteFinite
open STLTableau.ExpansionRule
set_option maxHeartbeats 32000000 in
set_option linter.unusedSimpArgs false in
theorem branch_nonPredicate_normalization [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) (Λ : ClockResetSet Clock) :
    ∃ F, TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        (F.underReset Λ).nonPredicateHolds σ P α k ↔ Judgement.nonPredicateHolds σ P (Λ.apply α) k (Judgement.ofFinite Ψ) := by
  classical
  (cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
      upperAlways, boundedAlways, upperEventually, boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlways_defer, upperAlways_check, boundedAlways_defer,
      boundedAlways_check, boundedAlways_finish, upperEventually_defer,
      upperEventually_check, boundedEventually_defer, boundedEventually_check,
      boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock]) <;>
    (try simp only [Judgement.ofFinite, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset]) <;>
    refine ⟨_, rfl, ?_⟩ <;> intro σ P α k <;>
    by_cases hk : k.1 < P.size <;>
    simp only [TransitionForm.normalize?, Judgement.ofFinite, TransitionForm.underReset,
      TransitionForm.union, TransitionForm.unionNext, TransitionForm.ofNextState,
      TransitionForm.ofState, StateForm.ofLocal, StateForm.ofGuard, StateForm.empty,
      StateForm.union, TransitionForm.nonPredicateHolds, StateForm.nonPredicateHolds,
      Local.nonPredicateHolds, Local.toJudgement, Guard.holds, Judgement.nonPredicateHolds, Judgement.nonPredicateHolds, Predicate.ofFinite, Option.some.injEq,
       hk, dif_pos, dif_neg, ClockResetSet.apply_union_eq_comp,
      ClockResetSet.apply_empty, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, forall_eq, forall_eq', forall_const, or_imp, forall_and,
      true_and, and_true, false_and, and_false, and_assoc, and_comm,
      and_left_comm, false_implies, implies_true, ↓reduceDIte, iff_self, and_self] <;> simp [Judgement.nonPredicateHolds, Guard.holds]

end ConcreteFinite

end STLTableau.Section3
