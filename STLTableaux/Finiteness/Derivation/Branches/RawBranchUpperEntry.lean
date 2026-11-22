import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalizedOrigin

/-! The next state of an expansion of the `↑` form carries the reset and
marker conditions needed for a boundary merge. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- The next part of a branch for the `↑` form records the reset `d = 0` and
its left marker. A strict boundary comparison leaves the left clock unreset. -/
theorem RawBranch.normalized_upper_entry [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Local.predicate (.bounded c d m q kind I φ) ∈ N.locals)
    (hsource : ∃ b, p = .upper c b kind I φ) :
    ∃ ℓ, q = Marker.complement ℓ ∧ Local.marker ℓ ∈ N.locals ∧
      N.resets.value d = some 0 ∧
      (Marker.imp ℓ m = Marker.open → N.resets.value c = none) := by
  obtain ⟨b,hp⟩ := hsource
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
    all_goals simp only [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
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
      Section3.Judgement.currentPredicates] at hSafe
    all_goals repeat' cases_type SafeNormalization
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
      Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,Section3.StateForm.empty,Section3.StateForm.union,
      Section3.Predicate.ofFinite,Section3.Predicate.ofUnbounded,
      ClockResetSet.union,ClockResetSet.empty,ClockResetSet.singleton,Marker.imp]
    all_goals subst N
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.Predicate.ofFinite,Section3.Predicate.ofUnbounded,
      ClockResetSet.union,ClockResetSet.empty,ClockResetSet.singleton,Marker.imp]
    all_goals rcases hp with ⟨rfl,rfl,rfl,rfl,rfl⟩
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,Marker.complement,Marker.imp,eq_comm]
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp only [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
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
      Section3.Judgement.currentPredicates] at hSafe
    all_goals repeat' cases_type SafeNormalization
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
      Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,Section3.StateForm.empty,Section3.StateForm.union,
      Section3.Predicate.ofFinite,Section3.Predicate.ofUnbounded,
      ClockResetSet.union,ClockResetSet.empty,ClockResetSet.singleton,Marker.imp]
    all_goals subst N
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.Predicate.ofFinite,Section3.Predicate.ofUnbounded,
      ClockResetSet.union,ClockResetSet.empty,ClockResetSet.singleton,Marker.imp]
    all_goals rcases hp with ⟨rfl,rfl,rfl,rfl,rfl⟩
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,Marker.complement,Marker.imp,eq_comm]
  | opening c m kind a φ =>
    simp [Predicate.ofUnbounded] at hp

/-- Complete entry certificate: actual normalized reset values and marker,
together with the literal freezing scope of the actual source branch. -/
theorem RawBranch.normalized_upper_entry_certificate [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Local.predicate (.bounded c d m q kind I φ) ∈ N.locals)
    (hsource : ∃ b, p = .upper c b kind I φ) :
    ∃ ℓ K, q = Marker.complement ℓ ∧ Local.marker ℓ ∈ N.locals ∧
      N.resets.value d = some 0 ∧
      (Marker.imp ℓ m = Marker.open → N.resets.value c = none) ∧
      Conjunct B (.next K) ∧ FrozenOccurrence K c d m ℓ kind I φ := by
  obtain ⟨ℓ,hqℓ,hm,hd,hc⟩ := h.normalized_upper_entry hSafe hNext c d m q kind I φ hq hsource
  obtain ⟨K,hK,hqK⟩ := h.normalized_next_predicate_origin hSafe hNext _ hq
  obtain ⟨ℓ',hqℓ',hf⟩ := h.next_bounded_frozen_of_upper hK c d m q kind I φ hqK hsource
  have he : ℓ' = ℓ := by
    simpa only [Marker.complement_complement] using
      congrArg Marker.complement (hqℓ'.symm.trans hqℓ)
  subst ℓ'
  exact ⟨ℓ,K,hqℓ,hm,hd,hc,hK,hf⟩

end STLTableau.Section4.Finiteness
