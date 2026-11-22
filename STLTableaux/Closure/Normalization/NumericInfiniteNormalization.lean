import STLTableaux.Semantics.Invariants.NumericInvariant

namespace STLTableau.Section3.ConcreteInfinite
open STLTableau.Section3
open STLTableau.UnboundedClocked
variable {Clock Var : Type*}

-- Enumerating literal branch schemas elaborates nested finite-set unions.
set_option maxHeartbeats 32000000 in
set_option linter.unusedSimpArgs false in
/-- Transition forms for unbounded clocked rule branches. -/
theorem branch_numeric_normalization [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : UnboundedClocked.Node Clock Var}
    (hΨ : Ψ ∈ Bs) (Λ : ClockResetSet Clock) :
    ∃ F : TransitionForm Clock Var,
      TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        (F.underReset Λ).EvaluatedNumeric σ P α k ↔ Judgement.EvaluatedNumeric σ P (Λ.apply α) k (Judgement.ofUnbounded Ψ) := by
  classical
  (cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
      boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
      upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
      boundedEventuallyFinish, UnboundedClocked.Node.lt, UnboundedClocked.Node.gt]) <;>
    (try simp only [Judgement.ofUnbounded, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset]) <;>
    refine ⟨_, rfl, ?_⟩ <;> intro σ P α k <;>
    by_cases hk : k.1 < P.size <;>
    simp only [TransitionForm.normalize?, Judgement.ofUnbounded, TransitionForm.underReset,
      TransitionForm.union, TransitionForm.unionNext, TransitionForm.ofNextState,
      TransitionForm.ofState, StateForm.ofLocal, StateForm.ofGuard, StateForm.empty,
      StateForm.union, TransitionForm.EvaluatedNumeric, StateForm.EvaluatedNumeric,
      Local.Numeric, Local.toJudgement, Judgement.EvaluatedNumeric, Predicate.Numeric, Predicate.ofUnbounded, Option.some.injEq,
       hk, dif_pos, dif_neg, ClockResetSet.apply_union_eq_comp,
      ClockResetSet.apply_empty, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, forall_eq, forall_eq', forall_const, or_imp, forall_and,
      true_and, and_true, false_and, and_false, and_assoc, and_comm,
      and_left_comm, false_implies, implies_true, ↓reduceDIte, iff_self, and_self] <;> simp

/-- The two unbounded TemporalOpen schemas normalize without a cap. -/
theorem opening_numeric_normalization [DecidableEq Clock] (c : Clock) (m : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) (Λ : ClockResetSet Clock) :
    ∃ F : TransitionForm Clock Var,
      TransitionForm.normalize? (Judgement.ofUnbounded (opening c m kind a φ)) = some F ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        (F.underReset Λ).EvaluatedNumeric σ P α k ↔
          Judgement.EvaluatedNumeric σ P (Λ.apply α) k (Judgement.ofUnbounded (opening c m kind a φ)) := by
  refine ⟨_, rfl, ?_⟩
  intro σ P α k
  by_cases hk : k.1 < P.size <;>
    simp [opening, Judgement.ofUnbounded, TransitionForm.normalize?, TransitionForm.underReset,
      TransitionForm.union, TransitionForm.unionNext, TransitionForm.ofNextState,
      TransitionForm.ofState, StateForm.ofLocal, StateForm.ofGuard, StateForm.empty,
      StateForm.union, TransitionForm.EvaluatedNumeric, StateForm.EvaluatedNumeric,
      Local.Numeric, Local.toJudgement, Judgement.EvaluatedNumeric, Predicate.Numeric, Predicate.ofUnbounded, Option.some.injEq,
       hk, ClockResetSet.apply_union_eq_comp, and_assoc, and_comm, and_left_comm]

end STLTableau.Section3.ConcreteInfinite
