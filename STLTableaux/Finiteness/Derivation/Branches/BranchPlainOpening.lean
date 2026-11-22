import STLTableaux.Finiteness.Derivation.Branches.BranchTripleAnnotations
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape

/-! Plain rules either have no clock syntax or are exact temporal openings.
 Thus non-temporal plain rules require no arbitrary temporal slot assignment. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

def PlainOpeningOrEmpty [DecidableEq Clock] (p : Predicate Clock Var) (B : MixedJ Clock Var) : Prop :=
  syntaxClocks B=∅ ∨ ∃c m kind I φ,
    p=.plain (timedFormula kind I φ) ∧
    B=.reset (ClockResetSet.singleton c 0) (.conj (.predicate (.upper c m kind I φ)) (.marker m))

set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
private theorem finite_plain_shape [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var} (hm : B∈R.branches)
    (hp : ∃φ,Predicate.ofFinite p=.plain φ) :
    PlainOpeningOrEmpty (Predicate.ofFinite p) (Judgement.ofFinite B) := by
  (cases hr <;>
    simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
      ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
      ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
      ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
    (try split_ifs at hm) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp_all [PlainOpeningOrEmpty,syntaxClocks,Section3.Judgement.ofFinite,
    Predicate.ofFinite,timedFormula,ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
    ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
    ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
    ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
    STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock]

 theorem RawBranch.plain_opening_or_empty [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (hp : ∃φ,p=.plain φ) : PlainOpeningOrEmpty p B := by
  cases h with
  | finite hr hm => exact finite_plain_shape hr hm hp
  | @infinite p Bs hr B hm => cases p <;> simp [Predicate.ofUnbounded] at hp
  | opening c m kind a φ =>
      exact Or.inr ⟨c,m,kind,.unbounded a,φ,rfl,rfl⟩

end STLTableau.Section4.Finiteness
