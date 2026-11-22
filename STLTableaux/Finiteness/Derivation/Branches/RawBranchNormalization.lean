import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Closure.Correctness.FaithfulClosureProgress
import STLTableaux.Closure.Normalization.NormalizedFiniteInvariant
import STLTableaux.Closure.Normalization.NormalizedInfiniteInvariant

/-! Structural safe normalization of actual concrete rule branches. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
private theorem finite_safe {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hb : B ∈ R.branches) : ∃ F, SafeNormalization (Section3.Judgement.ofFinite B) F := by
  classical
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
  all_goals simp only [Marker.imp,Marker.conj,Marker.notConj,Marker.complement,
    STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,Section3.Judgement.ofFinite]
  all_goals
    refine ⟨_, by
    repeat' first
      | exact SafeNormalization.terminal
      | exact SafeNormalization.predicate _
      | exact SafeNormalization.marker _
      | exact SafeNormalization.clock _ _ _
      | apply SafeNormalization.conj
      | apply SafeNormalization.reset
      | apply SafeNormalization.next
      | rfl
    all_goals try apply Section3.TransitionForm.unionCompatible_of_captureFree
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
      Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,
      Section3.StateForm.empty,Section3.StateForm.union,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Section3.StateForm.freeClocks,Local.freeClocks,Local.toJudgement,
      Section3.Judgement.freeClocks,ClockResetSet.clocks,ClockResetSet.empty,ClockResetSet.singleton,
      ClockResetSet.union,ClockResetSet.Consistent,Set.disjoint_left]
    ⟩

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
private theorem infinite_safe {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)} (hr : UnboundedClocked.ConcreteRule p Bs)
    {B : UnboundedClocked.Node Clock Var} (hb : B ∈ Bs) :
    ∃ F, SafeNormalization (Section3.Judgement.ofUnbounded B) F := by
  classical
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
  all_goals simp only [Marker.imp,Marker.conj,Marker.notConj,Marker.complement,
    STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,Section3.Judgement.ofUnbounded]
  all_goals
    refine ⟨_, by
    repeat' first
      | exact SafeNormalization.terminal
      | exact SafeNormalization.predicate _
      | exact SafeNormalization.marker _
      | exact SafeNormalization.clock _ _ _
      | apply SafeNormalization.conj
      | apply SafeNormalization.reset
      | apply SafeNormalization.next
      | rfl
    all_goals try apply Section3.TransitionForm.unionCompatible_of_captureFree
    all_goals simp_all [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.TransitionForm.union,Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
      Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,
      Section3.StateForm.empty,Section3.StateForm.union,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Section3.StateForm.freeClocks,Local.freeClocks,Local.toJudgement,
      Section3.Judgement.freeClocks,ClockResetSet.clocks,ClockResetSet.empty,ClockResetSet.singleton,
      ClockResetSet.union,ClockResetSet.Consistent,Set.disjoint_left]
    ⟩

set_option linter.unusedSimpArgs false in
/-- Every actual raw branch has a constructed safe normal form. In particular,
paired resets and bounded check branches use their rule's distinct-clock proof. -/
theorem RawBranch.safe_normalization {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) : ∃ F, SafeNormalization B F ∧ F.current.guards = ∅ := by
  cases h with
  | finite hr hb =>
    obtain ⟨F,hF⟩ := finite_safe hr hb
    exact ⟨F,hF,FaithfulClosure.normalize_currentGuards_empty _ hF.normalizes
      (FaithfulClosure.finite_branch_guardWidth hr hb)⟩
  | infinite hr hb =>
    obtain ⟨F,hF⟩ := infinite_safe hr hb
    exact ⟨F,hF,FaithfulClosure.normalize_currentGuards_empty _ hF.normalizes
      (FaithfulClosure.infinite_branch_guardWidth hr hb)⟩
  | opening c m kind a φ =>
    have safe : ∃ F, SafeNormalization
        (Section3.Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) F := by
      refine ⟨_, by
        simp only [UnboundedClocked.opening,Section3.Judgement.ofUnbounded]
        repeat' first
          | exact SafeNormalization.predicate _
          | exact SafeNormalization.marker _
          | apply SafeNormalization.conj
          | apply SafeNormalization.reset
        all_goals try apply Section3.TransitionForm.unionCompatible_of_captureFree
        all_goals simp [-ENNReal.none_eq_top,-ENNReal.some_eq_coe,
          Section3.TransitionForm.ofState,Section3.TransitionForm.bodyFreeClocks,
          Section3.StateForm.ofLocal,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
          Section3.TransitionForm.union,Section3.StateForm.union,
          ClockResetSet.clocks,ClockResetSet.empty,ClockResetSet.Consistent,Set.disjoint_left]
      ⟩
    obtain ⟨F,hF⟩ := safe
    exact ⟨F,hF,FaithfulClosure.normalize_currentGuards_empty _ hF.normalizes rfl⟩

/-- Full invariant correspondence for an actual raw branch, obtained from the
existing concrete normalization theorems and uniqueness of normalize?. -/
theorem RawBranch.invariant_normalization {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) {F : Section3.TransitionForm Clock Var}
    (hn : Section3.TransitionForm.normalize? B = some F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    F.EvaluatedInvariant σ P α k ↔ Section3.Judgement.EvaluatedInvariant σ P α k B := by
  cases h with
  | finite hr hb =>
    obtain ⟨G,hG,hi⟩ := ConcreteFinite.branch_invariant_normalization hr hb ClockResetSet.empty
    have he : G = F := Option.some.inj (hG.symm.trans hn)
    subst G
    have ht := (F.underReset_evaluatedInvariant ClockResetSet.empty σ P α k).symm.trans (hi σ P α k)
    simpa only [ClockResetSet.apply_empty,Section3.Judgement.evaluatedInvariant_ofFinite] using ht
  | infinite hr hb =>
    obtain ⟨G,hG,hi⟩ := ConcreteInfinite.branch_invariant_normalization hr hb ClockResetSet.empty
    have he : G = F := Option.some.inj (hG.symm.trans hn)
    subst G
    have ht := (F.underReset_evaluatedInvariant ClockResetSet.empty σ P α k).symm.trans (hi σ P α k)
    simpa only [ClockResetSet.apply_empty,Section3.Judgement.evaluatedInvariant_ofUnbounded] using ht
  | opening c m kind a φ =>
    obtain ⟨G,hG,hi⟩ := ConcreteInfinite.opening_invariant_normalization c m kind a φ ClockResetSet.empty
    have he : G = F := Option.some.inj (hG.symm.trans hn)
    subst G
    have ht := (F.underReset_evaluatedInvariant ClockResetSet.empty σ P α k).symm.trans (hi σ P α k)
    simpa only [ClockResetSet.apply_empty,Section3.Judgement.evaluatedInvariant_ofUnbounded] using ht

end STLTableau.Section4.Finiteness
