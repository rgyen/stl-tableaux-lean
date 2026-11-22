import STLTableaux.Finiteness.Derivation.Derivation

/-! Clock privacy of actual ordinary rule children, including the current
predicates INSIDE each literal next payload. Duplicate equal predicates are
allowed; this is not a bound or a completed pending ownership theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

 def privateRawCurrent (J : MixedJ Clock Var) : Prop :=
  ∀ p ∈ J.currentPredicates, ∀ q ∈ J.currentPredicates, p ≠ q →
    Disjoint (syntaxClocks (.predicate p)) (syntaxClocks (.predicate q))

/-- Every next payload has internally private distinct current predicates;
nested next is checked recursively as well. -/
def NextPrivate : MixedJ Clock Var → Prop
  | .next J => privateRawCurrent J ∧ NextPrivate J
  | .conj J K => NextPrivate J ∧ NextPrivate K
  | .reset _ J => NextPrivate J
  | _ => True

/-- Names occurring inside literal next payloads. Current reset binders do not
belong to this set; payload-internal resets do. -/
def nextSyntaxClocks : MixedJ Clock Var → Set Clock
  | .next J => syntaxClocks J
  | .conj J K => nextSyntaxClocks J ∪ nextSyntaxClocks K
  | .reset _ J => nextSyntaxClocks J
  | _ => ∅

private def currentNextPrivate (J : MixedJ Clock Var) : Prop :=
  ∀ p ∈ J.currentPredicates,
    Disjoint (syntaxClocks (.predicate p)) (nextSyntaxClocks J)

 theorem ACIdem.nextSyntaxClocks_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    nextSyntaxClocks J = nextSyntaxClocks K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib R J K => rfl
  | resetUnused R J hd => rfl
  | resetNested R S J => rfl

 theorem ACIdem.nextPrivate_iff {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    NextPrivate J ↔ NextPrivate K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr ih ig
  | reset R h ih => exact ih
  | resetDistrib R J K => rfl
  | resetUnused R J hd => rfl
  | resetNested R S J => rfl

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
private theorem actual_privacy [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) : privateRawCurrent B ∧ NextPrivate B ∧ currentNextPrivate B := by
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
      Section3.Judgement.ofFinite,Section3.Predicate.ofFinite,privateRawCurrent,NextPrivate,
      Section3.Judgement.currentPredicates,syntaxClocks,currentNextPrivate,nextSyntaxClocks]
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
      privateRawCurrent,NextPrivate,Section3.Judgement.currentPredicates,syntaxClocks,currentNextPrivate,nextSyntaxClocks]
  | opening c m kind a φ =>
    simp [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,privateRawCurrent,
      NextPrivate,Section3.Judgement.currentPredicates,currentNextPrivate,nextSyntaxClocks]

 theorem RawBranch.current_private [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) : privateRawCurrent B :=
  (actual_privacy h).1

 theorem RawBranch.next_private [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) : NextPrivate B :=
  (actual_privacy h).2.1

/-- A new branch's CURRENT children do not read any name in its own future
payload. This is stronger than privacy within either collection separately. -/
theorem RawBranch.current_next_private [DecidableEq Clock] {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : RawBranch p B) (q : Predicate Clock Var)
    (hq : q ∈ B.currentPredicates) :
    Disjoint (syntaxClocks (.predicate q)) (nextSyntaxClocks B) :=
  (actual_privacy h).2.2 q hq

end STLTableau.Section4.Finiteness
