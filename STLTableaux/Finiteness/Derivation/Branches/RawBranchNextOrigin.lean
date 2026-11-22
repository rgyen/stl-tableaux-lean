import STLTableaux.Finiteness.Derivation.Derivation

/-! Classification from actual ordinary raw branch membership. Freshness against
historical clocks is deliberately not a consequence of this syntax theorem. -/
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
/-- Every bounded current child of an actual literal next payload originates
from the same upper family, or the same bounded family with right marker
preserved. Clock names, temporal kind, interval and body are unchanged. -/
theorem RawBranch.next_bounded_source [DecidableEq Clock]
    {p : Predicate Clock Var} {B N : MixedJ Clock Var} (h : RawBranch p B)
    (hNext : Conjunct B (.next N))
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.bounded c d m q kind I φ ∈ N.currentPredicates) :
    (∃ b, p = .upper c b kind I φ ∧ c ≠ d) ∨
      (∃ b, p = .bounded c d b q kind I φ ∧ c ≠ d) := by
  have hn := literal_next_mem hNext
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

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- An upper-origin bounded child carries the literal defer/check freezing
scope of its actual next payload. No historical freshness is asserted. -/
theorem RawBranch.next_bounded_frozen_of_upper [DecidableEq Clock]
    {p : Predicate Clock Var} {B N : MixedJ Clock Var} (h : RawBranch p B)
    (hNext : Conjunct B (.next N))
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.bounded c d m q kind I φ ∈ N.currentPredicates)
    (hsource : ∃ b, p = .upper c b kind I φ) :
    ∃ ℓ, q = Marker.complement ℓ ∧ FrozenOccurrence N c d m ℓ kind I φ := by
  obtain ⟨b,hp⟩ := hsource
  have hn := literal_next_mem hNext
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
    all_goals rcases hp with ⟨rfl,rfl,rfl,rfl,rfl⟩
    all_goals first
      | exact ⟨.open,rfl,.defer (.right (.here _))⟩
      | exact ⟨.closed,rfl,.defer (.right (.here _))⟩
      | exact ⟨.open,rfl,.defer (.here _)⟩
      | exact ⟨.closed,rfl,.defer (.here _)⟩
      | exact ⟨.open,rfl,.check (.right (.here _))⟩
      | exact ⟨.closed,rfl,.check (.right (.here _))⟩

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
    all_goals rcases hp with ⟨rfl,rfl,rfl,rfl,rfl⟩
    all_goals first
      | exact ⟨.open,rfl,.defer (.right (.here _))⟩
      | exact ⟨.closed,rfl,.defer (.right (.here _))⟩
      | exact ⟨.open,rfl,.defer (.here _)⟩
      | exact ⟨.closed,rfl,.defer (.here _)⟩
      | exact ⟨.open,rfl,.check (.right (.here _))⟩
      | exact ⟨.closed,rfl,.check (.right (.here _))⟩

  | opening c m kind a φ =>
    simp_all [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,Section3.Judgement.currentPredicates,nextPayloads]

/-- Actual-history bridge: an upper origin includes the literal freezing scope;
a bounded origin preserves the right clock and right marker. -/
theorem RawBranch.next_bounded_origin [DecidableEq Clock]
    {p : Predicate Clock Var} {B N : MixedJ Clock Var} (h : RawBranch p B)
    (hNext : Conjunct B (.next N))
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.bounded c d m q kind I φ ∈ N.currentPredicates) :
    (∃ b, p = .upper c b kind I φ ∧ c ≠ d ∧
      ∃ ℓ, q = Marker.complement ℓ ∧ FrozenOccurrence N c d m ℓ kind I φ) ∨
      (∃ b, p = .bounded c d b q kind I φ ∧ c ≠ d) := by
  rcases h.next_bounded_source hNext c d m q kind I φ hq with ⟨b,hp,hcd⟩ | hb
  · obtain ⟨ℓ,hqℓ,hf⟩ := h.next_bounded_frozen_of_upper hNext c d m q kind I φ hq ⟨b,hp⟩
    exact Or.inl ⟨b,hp,hcd,ℓ,hqℓ,hf⟩
  · exact Or.inr hb

end STLTableau.Section4.Finiteness
