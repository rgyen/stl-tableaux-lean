import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalizedOrigin

/-! Actual schema restrictions used by the pending-only selection policy.
These facts do not restrict retained source annotations in a completed output. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- A predicate in the `↑` form in the current part comes from a plain
opening branch, with its reset and left marker. -/
theorem RawBranch.current_upper_opening [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.upper c m kind I φ ∈ B.currentPredicates) :
    p = .plain (timedFormula kind I φ) ∧
      B = .reset (ClockResetSet.singleton c 0)
        (.conj (.predicate (.upper c m kind I φ)) (.marker m)) := by
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
      Section3.Judgement.currentPredicates,timedFormula]
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
      Section3.Judgement.currentPredicates,timedFormula]
  | opening c m kind a φ =>
    cases kind <;> simp_all [UnboundedClocked.opening,UnboundedClocked.formula,timedFormula,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,Section3.Judgement.currentPredicates,timedFormula]

/-- An expansion branch has at most one current predicate in the `↑` form. -/
theorem RawBranch.current_upper_unique [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (c₁ : Clock) (m₁ : Marker) (kind₁ : TemporalKind) (I₁ : TimeInterval) (φ₁ : Formula Var)
    (c₂ : Clock) (m₂ : Marker) (kind₂ : TemporalKind) (I₂ : TimeInterval) (φ₂ : Formula Var)
    (h₁ : Predicate.upper c₁ m₁ kind₁ I₁ φ₁ ∈ B.currentPredicates)
    (h₂ : Predicate.upper c₂ m₂ kind₂ I₂ φ₂ ∈ B.currentPredicates) :
    Predicate.upper c₁ m₁ kind₁ I₁ φ₁ = Predicate.upper c₂ m₂ kind₂ I₂ φ₂ := by
  rw [(h.current_upper_opening c₁ m₁ kind₁ I₁ φ₁ h₁).2] at h₂
  have he : Predicate.upper c₂ m₂ kind₂ I₂ φ₂ = Predicate.upper c₁ m₁ kind₁ I₁ φ₁ := by
    simpa only [Section3.Judgement.currentPredicates,Set.mem_union,
      Set.mem_singleton_iff,Set.mem_empty_iff_false,or_false] using h₂
  exact he.symm

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
theorem RawBranch.literal_next_no_upper [DecidableEq Clock]
    {p : Predicate Clock Var} {B N : MixedJ Clock Var} (h : RawBranch p B)
    (hNext : Conjunct B (.next N))
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.upper c m kind I φ ∈ N.currentPredicates) : False := by
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

/-- A safely normalized next state of an actual branch never contains upper
locals. Such upper requirements exist only during current local resolution. -/
theorem RawBranch.normalized_next_no_upper [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Local.predicate (.upper c m kind I φ) ∉ N.locals := by
  intro hq
  obtain ⟨K,hK,hqK⟩ := h.normalized_next_predicate_origin hSafe hNext _ hq
  exact h.literal_next_no_upper hK c m kind I φ hqK

end STLTableau.Section4.Finiteness
