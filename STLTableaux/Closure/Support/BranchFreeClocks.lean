import STLTableaux.Closure.Correctness.MixedConcreteClosure

namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace TransitionForm

set_option maxHeartbeats 800000 in
theorem freeClocks_union_subset (F G : TransitionForm Clock Var) :
    (F.union G).freeClocks ⊆ F.freeClocks ∪ G.freeClocks := by
  have hg (S T : StateForm Clock Var) :
      (S.union T).guardClocks = S.guardClocks ∪ T.guardClocks := by
    ext c
    simp only [StateForm.guardClocks, StateForm.union, Set.mem_setOf_eq, Set.mem_union]
    aesop
  have hl (S T : StateForm Clock Var) :
      (S.union T).localClocks = S.localClocks ∪ T.localClocks := by
    ext c
    simp only [StateForm.localClocks, StateForm.union, Set.mem_setOf_eq, Set.mem_union]
    aesop
  have hr (S T : StateForm Clock Var) :
      (S.union T).resets.clocks = S.resets.clocks ∪ T.resets.clocks :=
    ClockResetSet.clocks_union _ _
  cases hF : F.nextPart <;> cases hG : G.nextPart <;>
    simp only [freeClocks, bodyFreeClocks, union, unionNext, hF, hG,
      StateForm.freeClocks, hg, hl, hr] <;>
    intro c hc <;> simp only [Set.mem_union, Set.mem_diff] at * <;> tauto

theorem freeClocks_underReset_subset (F : TransitionForm Clock Var)
    (Λ : ClockResetSet Clock) (hg : F.current.guards = ∅) :
    (F.underReset Λ).freeClocks ⊆ F.freeClocks \ Λ.clocks := by
  intro c hc
  have hguard : F.current.guardClocks = ∅ := by
    simp [StateForm.guardClocks, hg]
  simp only [freeClocks, underReset, bodyFreeClocks,
    StateForm.guardClocks, StateForm.localClocks, hg,
    Set.mem_setOf_eq, Set.mem_empty_iff_false, false_and, exists_false,
    false_or, Set.mem_diff, ClockResetSet.clocks_union, Set.mem_union] at hc ⊢
  aesop
end TransitionForm

namespace ConcreteFinite
open STLTableau.ExpansionRule
set_option maxHeartbeats 16000000 in
set_option linter.unusedSimpArgs false in
theorem branch_freeClocks [DecidableEq Clock]
    {p : Predicate Clock Var} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p ClockResetSet.empty B) :
    B.freeClocks ⊆ (Judgement.predicate p).freeClocks := by
  classical
  obtain ⟨p₀, R, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hb
  (cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
      upperAlways, boundedAlways, upperEventually, boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [upperAlways_defer, upperAlways_check, boundedAlways_defer,
      boundedAlways_check, boundedAlways_finish, upperEventually_defer,
      upperEventually_check, boundedEventually_defer, boundedEventually_check,
      boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock,
      Judgement.ofFinite, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset] at hF <;>
    cases hF <;>
    simp [TransitionForm.freeClocks, TransitionForm.bodyFreeClocks,
      TransitionForm.underReset, TransitionForm.ofState, TransitionForm.ofNextState,
      TransitionForm.union, TransitionForm.unionNext, StateForm.freeClocks, StateForm.guardClocks,
      StateForm.localClocks, StateForm.union, StateForm.ofLocal, StateForm.ofGuard,
      StateForm.empty, Local.freeClocks, Local.toJudgement, Judgement.freeClocks,
      Predicate.ofFinite, ClockResetSet.clocks_union, Set.subset_def] <;> aesop
end ConcreteFinite
namespace ConcreteInfinite
open UnboundedClocked
set_option maxHeartbeats 16000000 in
set_option linter.unusedSimpArgs false in
theorem branch_freeClocks [DecidableEq Clock]
    {p : Predicate Clock Var} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p ClockResetSet.empty B) :
    B.freeClocks ⊆ (Judgement.predicate p).freeClocks := by
  classical
  obtain ⟨p₀, Bs, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hb
  (cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
      alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
      boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
      Judgement.ofUnbounded, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset] at hF <;>
    cases hF <;>
    simp [TransitionForm.freeClocks, TransitionForm.bodyFreeClocks,
      TransitionForm.underReset, TransitionForm.ofState, TransitionForm.ofNextState,
      TransitionForm.union, TransitionForm.unionNext, StateForm.freeClocks, StateForm.guardClocks,
      StateForm.localClocks, StateForm.union, StateForm.ofLocal, StateForm.ofGuard,
      StateForm.empty, Local.freeClocks, Local.toJudgement, Judgement.freeClocks,
      Predicate.ofUnbounded, ClockResetSet.clocks_union, Set.subset_def] <;> aesop
end ConcreteInfinite

namespace ConcreteOpening
open UnboundedClocked
set_option linter.unusedSimpArgs false in
theorem branch_freeClocks [DecidableEq Clock]
    {p : Predicate Clock Var} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p ClockResetSet.empty B) :
    B.freeClocks ⊆ (Judgement.predicate p).freeClocks := by
  classical
  obtain ⟨c, m, kind, a, φ, F, rfl, hF, rfl⟩ := hb
  cases kind <;>
    simp only [opening, Judgement.ofUnbounded, TransitionForm.normalize?, Option.bind_some,
      Option.map_some, TransitionForm.unionNext, TransitionForm.ofState,
      TransitionForm.ofNextState, TransitionForm.union, TransitionForm.underReset] at hF <;>
    cases hF <;>
    simp [TransitionForm.freeClocks, TransitionForm.bodyFreeClocks,
      TransitionForm.underReset, TransitionForm.ofState, TransitionForm.ofNextState,
      TransitionForm.union, TransitionForm.unionNext, StateForm.freeClocks, StateForm.guardClocks,
      StateForm.localClocks, StateForm.union, StateForm.ofLocal, StateForm.ofGuard,
      StateForm.empty, Local.freeClocks, Local.toJudgement, Judgement.freeClocks,
      Predicate.ofUnbounded, ClockResetSet.clocks_union, Set.subset_def]
end ConcreteOpening

namespace ConcreteMixed
theorem branch_freeClocks [DecidableEq Clock]
    {p : Predicate Clock Var} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p ClockResetSet.empty B) :
    B.freeClocks ⊆ (Judgement.predicate p).freeClocks := by
  rcases hb with h | (h | h)
  · exact ConcreteFinite.branch_freeClocks h
  · exact ConcreteInfinite.branch_freeClocks h
  · exact ConcreteOpening.branch_freeClocks h
end ConcreteMixed
end STLTableau.Section3
