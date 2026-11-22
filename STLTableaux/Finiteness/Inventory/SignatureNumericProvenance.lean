import STLTableaux.Finiteness.Inventory.RootClockConstants

/-! Signature-local numeric provenance. Inherited outer resets are deliberately
excluded from the contextual conclusion. -/
namespace STLTableau.Section4.Finiteness.SignatureNumericProvenance
open Section3
open STLTableau.ExpansionRule
open scoped STL
variable {Clock Var : Type*}

noncomputable def predicateConstants : Predicate Clock Var → Finset NNReal
  | .plain φ => rootClockConstants φ
  | .upper _ _ _ I _ | .bounded _ _ _ _ _ I _ => intervalClockConstants I

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
theorem finite_raw_constants [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {Ψ : STLTableau.Judgement Clock Var}
    (hΨ : Ψ ∈ R.branches) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F) :
    FormConstantsWithin (predicateConstants (Predicate.ofFinite p)) F := by
  (cases hr <;>
    simp only [plainAnd,plainOr,plainUntil,plainRelease,openEventually,openAlways,
      upperAlways,boundedAlways,upperEventually,boundedEventually,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try simp only [upperAlways_defer,upperAlways_check,boundedAlways_defer,boundedAlways_check,
      boundedAlways_finish,upperEventually_defer,upperEventually_check,
      boundedEventually_defer,boundedEventually_check,boundedEventually_finish,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock] at hnorm) <;>
    simp [Judgement.ofFinite,TransitionForm.normalize?,Option.bind_some,Option.map_some,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.TransitionForm.underReset,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Option.some.injEq] at hnorm <;>
    subst F <;>
    simp [FormConstantsWithin,StateConstantsWithin,predicateConstants,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [predicateConstants,rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofFinite,IntervalPredicate.formula,Formula.eventually,Formula.always])

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Infinite clocked raw branches have the same direct label support. -/
theorem infinite_raw_constants [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : UnboundedClocked.Node Clock Var}
    (hΨ : Ψ ∈ Bs) {F : Section3.TransitionForm Clock Var}
    (hnorm : TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F) :
    FormConstantsWithin (predicateConstants (Predicate.ofUnbounded p)) F := by
  open UnboundedClocked in
    (cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hΨ <;>
      (try split_ifs at hΨ) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
      rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        UnboundedClocked.Node.lt, UnboundedClocked.Node.gt] at hnorm) <;>
    simp [Judgement.ofUnbounded,TransitionForm.normalize?,Option.bind_some,Option.map_some,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.TransitionForm.underReset,Section3.StateForm.union,Section3.StateForm.empty,
      Section3.StateForm.ofGuard,Section3.StateForm.ofLocal,Option.some.injEq] at hnorm <;>
    subst F <;>
    simp [FormConstantsWithin,StateConstantsWithin,predicateConstants,rootClockConstants,intervalClockConstants,
      Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always,
      Section3.StateForm.union,Section3.StateForm.empty,Section3.StateForm.ofLocal,
      Section3.StateForm.ofGuard]
  all_goals repeat' first | apply And.intro | apply reset_union | apply reset_empty
  all_goals (apply reset_singleton; simp [predicateConstants,rootClockConstants,intervalClockConstants,
    Section3.Predicate.formula,Section3.Predicate.ofUnbounded,UnboundedClocked.formula,Formula.eventually,Formula.always])



/-- The inventory depends on the immediate clocked interval, not on constants
inside its operand. Plain opening cases retain their formula inventory. -/
theorem mixed_raw_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {R : Section3.TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    FormConstantsWithin (predicateConstants p) R := by
  rcases h with h | h | h
  · obtain ⟨p,E,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact underReset_numeric_constants _ F _ (finite_raw_constants hr hm hn) (reset_empty _)
  · obtain ⟨p,E,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact underReset_numeric_constants _ F _ (infinite_raw_constants hr hm hn) (reset_empty _)
  · obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := h
    apply underReset_numeric_constants _ F _ _ (reset_empty _)
    have hh := opening_raw_branch_numeric_constants c m kind a φ hn
    cases kind <;> exact hh

/-- The actual branch has a scoped-alpha raw core with its own numeric
assignments confined before inherited outer resets are added. -/
theorem contextual_numeric_core [DecidableEq Clock]
    {p : Predicate Clock Var} {Γ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Γ B) :
    ∃R A, ConcreteMixed.catalogue.Branch p ClockResetSet.empty R ∧
      Section3.TransitionForm.AlphaEquivalent A R ∧ B = A.underReset Γ ∧
      FormConstantsWithin (predicateConstants p) A := by
  obtain ⟨R,A,hR,ha,hB⟩ := hb
  exact ⟨R,A,hR,ha,hB,(alpha_numeric_constants_iff _ ha).mpr (mixed_raw_constants hR)⟩

/-- Scoped alpha conversion changes clock names, but not their constants.
The inherited outer context may reset clocks to unrelated values, so the
conclusion confines current guards and the complete next state only. -/
theorem contextual_own_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {Γ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Γ B) :
    (∀g ∈ B.current.guards, g.bound ∈ predicateConstants p) ∧
      ∀N, B.nextPart = some N → StateConstantsWithin (predicateConstants p) N := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  have hA := (alpha_numeric_constants_iff (predicateConstants p) ha).mpr
    (mixed_raw_constants hR)
  exact ⟨hA.1.1,hA.2⟩

/-- Explicit same-signature interval conclusion for actual clocked parents. -/
theorem contextual_clocked_constants [DecidableEq Clock]
    {p : Predicate Clock Var} {Γ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Γ B)
    {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (hp : (∃c b,p = .upper c b kind I φ) ∨
      ∃c d b q,p = .bounded c d b q kind I φ) :
    (∀g ∈ B.current.guards, g.bound ∈ intervalClockConstants I) ∧
      ∀N, B.nextPart = some N → StateConstantsWithin (intervalClockConstants I) N := by
  have h := contextual_own_constants hb
  rcases hp with ⟨c,b,rfl⟩ | ⟨c,d,b,q,rfl⟩ <;> exact h

end STLTableau.Section4.Finiteness.SignatureNumericProvenance
