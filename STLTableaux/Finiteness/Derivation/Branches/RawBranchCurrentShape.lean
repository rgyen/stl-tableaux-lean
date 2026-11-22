import STLTableaux.Finiteness.Derivation.Derivation

/-! The current part of an ordinary expansion branch contains no `↑↓`
predicate. Such predicates can occur under next. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- A `↑↓` descendant can be carried under next, but is never a current
child of an actual ordinary raw branch. -/
theorem RawBranch.no_current_bounded [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Predicate.bounded c d m ℓ kind I φ ∉ B.currentPredicates := by
  cases h with
  | finite hr hb =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
        ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
        ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
        ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,
        ExpansionRule.boundedEventually_finish])
    all_goals simp [STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      Section3.Judgement.ofFinite,Section3.Predicate.ofFinite,
      Section3.Judgement.currentPredicates]
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
        UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
        UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
        UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
        UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
        UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt])
    all_goals simp [Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,
      Section3.Judgement.currentPredicates]
  | opening c m kind a φ =>
    simp [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,Section3.Judgement.currentPredicates]

end STLTableau.Section4.Finiteness
