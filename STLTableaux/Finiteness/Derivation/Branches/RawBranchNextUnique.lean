import STLTableaux.Finiteness.Derivation.Derivation

/-! A single actual ordinary source produces at most one distinct bounded
continuation among its literal next payloads. Plain next demands and retained
closure annotations are not counted. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

private def nextPayloads : MixedJ Clock Var → Set (MixedJ Clock Var)
  | .next K => {K}
  | .conj J K => nextPayloads J ∪ nextPayloads K
  | .reset _ J => nextPayloads J
  | _ => ∅

private theorem conjunct_payload_subset {B K : MixedJ Clock Var}
    (h : Conjunct B K) : nextPayloads K ⊆ nextPayloads B := by
  induction h with
  | here => exact Set.Subset.refl _
  | left h ih => exact ih.trans Set.subset_union_left
  | right h ih => exact ih.trans Set.subset_union_right

private theorem literal_next_mem {B N : MixedJ Clock Var}
    (h : Conjunct B (.next N)) : N ∈ nextPayloads B :=
  conjunct_payload_subset h rfl

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Two `↑↓` descendants in literal next payloads of the same actual branch
are the identical predicate, including clocks, both markers and formula data. -/
theorem RawBranch.next_bounded_unique [DecidableEq Clock]
    {p : Predicate Clock Var} {B N₁ N₂ : MixedJ Clock Var} (h : RawBranch p B)
    (hNext₁ : Conjunct B (.next N₁)) (hNext₂ : Conjunct B (.next N₂))
    (c₁ d₁ : Clock) (m₁ q₁ : Marker) (kind₁ : TemporalKind) (I₁ : TimeInterval) (φ₁ : Formula Var)
    (c₂ d₂ : Clock) (m₂ q₂ : Marker) (kind₂ : TemporalKind) (I₂ : TimeInterval) (φ₂ : Formula Var)
    (hq₁ : Predicate.bounded c₁ d₁ m₁ q₁ kind₁ I₁ φ₁ ∈ N₁.currentPredicates)
    (hq₂ : Predicate.bounded c₂ d₂ m₂ q₂ kind₂ I₂ φ₂ ∈ N₂.currentPredicates) :
    Predicate.bounded c₁ d₁ m₁ q₁ kind₁ I₁ φ₁ =
      Predicate.bounded c₂ d₂ m₂ q₂ kind₂ I₂ φ₂ := by
  have hn₁ := literal_next_mem hNext₁
  have hn₂ := literal_next_mem hNext₂
  cases h with
  | finite hr hb =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      Section3.Judgement.ofFinite,Section3.Predicate.ofFinite,
      Section3.Judgement.currentPredicates,nextPayloads]
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,
      Section3.Judgement.currentPredicates,nextPayloads]
  | opening c m kind a φ =>
    simp_all [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,Section3.Judgement.currentPredicates,nextPayloads]

end STLTableau.Section4.Finiteness
