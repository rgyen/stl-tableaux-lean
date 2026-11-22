import STLTableaux.Rules.Invariants.NumericBranchPreservation
import STLTableaux.Closure.Subsumption.SubsumptionAppendix

/-! The guard/type projection omits terminal judgements. A branch that
includes a terminal judgement has only unclocked predicate obligations, whose
numeric invariants are trivial; other branches use the existing arithmetic. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

private def TerminalFree (F : TransitionForm Clock Var) : Prop :=
  Local.terminal ∉ F.current.locals ∧
    ∀ N, F.nextPart = some N → Local.terminal ∉ N.locals

private theorem terminal_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    Local.terminal ∈ (S.rename e).locals ↔ Local.terminal ∈ S.locals := by
  change Local.terminal ∈ Local.rename e '' S.locals ↔ _
  constructor
  · rintro ⟨l, hl, he⟩
    cases l <;> simp_all [Local.rename]
  · intro h
    exact ⟨.terminal, h, rfl⟩

private theorem terminal_alpha {A B : TransitionForm Clock Var} (h : A.AlphaEquivalent B) :
    TerminalFree A ↔ TerminalFree B := by
  induction h with
  | refl => rfl
  | outer F e hf =>
      cases hn : F.nextPart <;>
        simp [TerminalFree, TransitionForm.alphaOuter, StateForm.alphaReset, hn, terminal_rename]
  | next F e hf =>
      cases hn : F.nextPart <;>
        simp [TerminalFree, TransitionForm.alphaNext, StateForm.alphaReset, hn, terminal_rename]
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

private theorem fullState_of_guardTypes (S : StateForm Clock Var)
    (hf : Local.terminal ∉ S.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (h : (S.restrictLocals Local.IsMarker).nonPredicateHolds σ P α k) :
    S.nonPredicateHolds σ P α k := by
  refine ⟨h.1, ?_⟩
  intro l hl
  cases l with
  | terminal => exact (hf hl).elim
  | predicate p => trivial
  | marker m => exact h.2 (.marker m) ⟨hl, trivial⟩

private theorem full_of_guardTypes (F : TransitionForm Clock Var)
    (hf : TerminalFree F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (h : (F.restrictLocals Local.IsMarker Local.IsMarker).nonPredicateHolds σ P α k) :
    F.nonPredicateHolds σ P α k := by
  refine ⟨fullState_of_guardTypes _ hf.1 σ P α k h.1, ?_⟩
  cases hn : F.nextPart with
  | none => trivial
  | some N =>
    have hs := h.2
    simp only [TransitionForm.nonPredicateHolds, TransitionForm.restrictLocals, hn, Option.map_some] at hs
    by_cases hk : k.1 < P.size
    · simp only [dif_pos hk] at hs ⊢
      exact fullState_of_guardTypes N (hf.2 N hn) σ P _ _ hs
    · simp only [dif_neg hk] at hs

namespace NumericBranch
open STLTableau.ExpansionRule

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 32000000 in
private theorem finite_shape [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {J : STLTableau.Judgement Clock Var}
    (hJ : J ∈ R.branches) {F : TransitionForm Clock Var}
    (hn : TransitionForm.normalize? (Judgement.ofFinite J) = some F) :
    TerminalFree F ∨
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        F.EvaluatedNumeric σ P α k := by
  classical
  (cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
      upperAlways, boundedAlways, upperEventually, boundedEventually,
      List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at hJ <;>
    (try split_ifs at hJ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hJ) <;>
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    try simp only [upperAlways_defer, upperAlways_check, boundedAlways_defer,
      boundedAlways_check, boundedAlways_finish, upperEventually_defer,
      upperEventually_check, boundedEventually_defer, boundedEventually_check,
      boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock, Judgement.ofFinite,
      TransitionForm.normalize?, Option.bind_some, Option.map_some] at hn
    have he : F = _ := (Option.some.inj hn).symm
    clear hn
    subst F
    first
    | left
      solve
      | simp [TerminalFree, upperAlways_defer, upperAlways_check, boundedAlways_defer,
          boundedAlways_check, boundedAlways_finish, upperEventually_defer,
          upperEventually_check, boundedEventually_defer, boundedEventually_check,
          boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
          STLTableau.Judgement.markedGT_eq_clock, Judgement.ofFinite,
          TransitionForm.normalize?, TransitionForm.union, TransitionForm.unionNext,
          TransitionForm.ofState, TransitionForm.ofNextState, TransitionForm.underReset,
          StateForm.ofLocal, StateForm.ofGuard, StateForm.empty, StateForm.union]
    | right
      intro σ P α k
      simp [Judgement.ofFinite, TransitionForm.normalize?, TransitionForm.union,
        TransitionForm.unionNext, TransitionForm.ofState, TransitionForm.ofNextState,
        StateForm.ofLocal, StateForm.ofGuard, StateForm.empty, StateForm.union,
        TransitionForm.EvaluatedNumeric, StateForm.EvaluatedNumeric,
        Local.Numeric, Local.toJudgement, Judgement.EvaluatedNumeric, Predicate.Numeric,
        Predicate.ofFinite]

open STLTableau.UnboundedClocked in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 32000000 in
private theorem infinite_shape [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {J : UnboundedClocked.Node Clock Var}
    (hJ : J ∈ Bs) {F : TransitionForm Clock Var}
    (hn : TransitionForm.normalize? (Judgement.ofUnbounded J) = some F) :
    TerminalFree F ∨
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        F.EvaluatedNumeric σ P α k := by
  classical
  (cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hJ <;>
    (try split_ifs at hJ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hJ) <;>
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    try simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
      boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
      upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
      boundedEventuallyFinish, UnboundedClocked.Node.lt, UnboundedClocked.Node.gt,
      Judgement.ofUnbounded, TransitionForm.normalize?, Option.bind_some, Option.map_some] at hn
    have he : F = _ := (Option.some.inj hn).symm
    clear hn
    subst F
    first
    | left
      solve
      | simp [TerminalFree, upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
          boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
          upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
          boundedEventuallyFinish, UnboundedClocked.Node.lt, UnboundedClocked.Node.gt,
          Judgement.ofUnbounded, TransitionForm.normalize?, TransitionForm.union,
          TransitionForm.unionNext, TransitionForm.ofState, TransitionForm.ofNextState,
          TransitionForm.underReset,
          StateForm.ofLocal, StateForm.ofGuard, StateForm.empty, StateForm.union]
    | right
      intro σ P α k
      simp [alwaysWait, alwaysLast, Judgement.ofUnbounded, TransitionForm.normalize?,
        TransitionForm.union, TransitionForm.unionNext, TransitionForm.ofState,
        TransitionForm.ofNextState, StateForm.ofLocal, StateForm.ofGuard, StateForm.empty,
        StateForm.union, TransitionForm.EvaluatedNumeric, StateForm.EvaluatedNumeric,
        Local.Numeric, Local.toJudgement, Judgement.EvaluatedNumeric, Predicate.Numeric,
        Predicate.ofUnbounded]

private theorem raw_shape [DecidableEq Clock]
    {p : Predicate Clock Var} {R : TransitionForm Clock Var}
    (hR : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    TerminalFree R ∨
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
        R.EvaluatedNumeric σ P α k := by
  rcases hR with h | h | h
  · obtain ⟨p₀, rules, J, F, rfl, hr, hm, hn, rfl⟩ := h
    rcases finite_shape hr hm hn with hf | h
    · exact Or.inl hf
    · exact Or.inr (fun σ P α k => (F.underReset_numeric _ σ P α k).2 (h σ P _ k))
  · obtain ⟨p₀, Bs, J, F, rfl, hr, hm, hn, rfl⟩ := h
    rcases infinite_shape hr hm hn with hf | h
    · exact Or.inl hf
    · exact Or.inr (fun σ P α k => (F.underReset_numeric _ σ P α k).2 (h σ P _ k))
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := h
    have he : F = _ := (Option.some.inj hn).symm
    subst F
    left
    simp [TerminalFree, UnboundedClocked.opening, Judgement.ofUnbounded,
      TransitionForm.normalize?, TransitionForm.union, TransitionForm.unionNext,
      TransitionForm.ofState, TransitionForm.ofNextState, TransitionForm.underReset,
      StateForm.ofLocal, StateForm.ofGuard, StateForm.empty, StateForm.union]

/-- Numeric propagation needs guards and type judgements, not terminal truth. -/
theorem contextual_preserves_of_guardTypes [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : (B.restrictLocals Local.IsMarker Local.IsMarker).nonPredicateHolds σ P α k) :
    B.EvaluatedNumeric σ P α k := by
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  rcases raw_shape hR with hf | hn
  · have hf' : TerminalFree (A.underReset Λ) := (terminal_alpha ha).2 hf
    exact contextual_preserves ⟨R, A, hR, ha, rfl⟩ σ P α k hi
      (full_of_guardTypes _ hf' σ P α k hs)
  · exact (A.underReset_numeric Λ σ P α k).2
      ((ha.evaluatedNumeric σ P (Λ.apply α) k).2 (hn σ P (Λ.apply α) k))

end NumericBranch
end STLTableau.Section3
