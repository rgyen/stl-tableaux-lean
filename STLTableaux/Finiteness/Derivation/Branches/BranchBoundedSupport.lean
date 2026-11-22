import STLTableaux.Finiteness.Derivation.Branches.BranchTripleDescendants

/-! Bounded branches introduce no new clock name at all. Consequently their
 whole literal next support, including guard-only payloads and resets, uses at
 most the inherited left/right pair. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem RawBranch.bounded_whole_support
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hp : p=.bounded c d m q kind I φ) : syntaxClocks B⊆{c,d} := by
  cases h with
  | finite hr hm =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
      (try split_ifs at hm) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [syntaxClocks,Section3.Judgement.ofFinite,Section3.Judgement.ofUnbounded,
      Predicate.ofFinite,Predicate.ofUnbounded,
      ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      ClockResetSet.clocks_union,Set.subset_def]
  | infinite hr hm =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
      (try split_ifs at hm) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [syntaxClocks,Section3.Judgement.ofFinite,Section3.Judgement.ofUnbounded,
      Predicate.ofFinite,Predicate.ofUnbounded,
      ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      ClockResetSet.clocks_union,Set.subset_def]
  | opening => cases hp

end STLTableau.Section4.Finiteness
