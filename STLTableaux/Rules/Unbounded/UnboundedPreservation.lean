import STLTableaux.Rules.Unbounded.UnboundedClockedRules
import STLTableaux.Rules.Unbounded.UnboundedPastHelpers
import STLTableaux.Rules.Unbounded.UnboundedAlwaysCompleteness
import STLTableaux.Rules.Unbounded.UnboundedEventuallyCompleteness
import STLTableaux.Rules.Unbounded.UnboundedSelectedBranches

/-! Direct unbounded predicate invariants are evaluated at the actual
reset/elapsed valuation, using the same signal-dependent invariant as the
unbounded semantics module. -/
namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

def EvaluatedInvariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Node Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, Invariant σ P α k hk p
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      EvaluatedInvariant σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩))
        ⟨k.1 + 1,by omega⟩ Ψ
  | k, .reset Λ Ψ => EvaluatedInvariant σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedInvariant σ P α k Φ ∧ EvaluatedInvariant σ P α k Ψ
  | _, _ => True

@[simp] theorem evaluated_lt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    EvaluatedInvariant σ P α k (Node.lt c m a) := by cases m <;> trivial
@[simp] theorem evaluated_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    EvaluatedInvariant σ P α k (Node.gt c m a) := by cases m <;> trivial

/-- Every satisfied always branch establishes the next start-position bound.
There is no eventuality premise for no past satisfaction hidden in this statement. -/
theorem always_branches_preserve [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) (B : Node Clock Var)
    (hB : B ∈ upperAlwaysBranches c d b a φ ∨ B ∈ boundedAlwaysBranches c d b q a φ)
    (hs : Node.holds σ P α k B) : EvaluatedInvariant σ P α k B := by
  rcases hB with hB | hB
  all_goals
    simp only [upperAlwaysBranches, boundedAlwaysBranches, List.mem_cons,
      List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      by_cases hk : k.1 < P.size <;> by_cases hn : k.1 + 1 < P.size <;>
      simp_all [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
        boundedAlwaysCheck, alwaysWait, alwaysLast, EvaluatedInvariant,
        Invariant, Node.holds, Node.lt, Node.gt, ClockRelation.Holds,
        ClockResetSet.apply, ClockResetSet.singleton, ClockResetSet.union,
        Marker.imp, Marker.complement] <;>
      cases b <;> cases q <;>
      simp_all <;> aesop

/-- Only the defer alternatives need this selection condition. It is
eliminated by branch selection in the final existential theorem. -/
def DeferCondition (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (b : Marker)
    (a : NNReal) (φ : Formula Var) : Prop :=
  ∀ hn : k.1 + 1 < P.size, ¬ Node.holds σ P α k (.plain φ) ∨
    (ClockResetSet.elapse α (Judgement.duration P ⟨k.1,by omega⟩) c : ℝ)
      <[Marker.imp b (P.interval ⟨k.1 + 1,hn⟩).leftBoundary] (a : ℝ)

theorem bounded_defer_preserves (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c d : Clock) (b q m : Marker)
    (a : NNReal) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .eventually a φ))
    (hc : DeferCondition σ P α k c b a φ) :
    EvaluatedInvariant σ P α k (boundedEventuallyDefer c d b q m a φ) := by
  simp only [boundedEventuallyDefer, EvaluatedInvariant, true_and]
  intro hk hn
  constructor
  · have hh := (hi hk).1
    change ((α d : ℝ) + (Judgement.duration P ⟨k.1,hk⟩ : ℝ)) <[Marker.conj b q]
      ((α c : ℝ) + (Judgement.duration P ⟨k.1,hk⟩ : ℝ))
    rcases hh with hh | ⟨hh,hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith,hm⟩
  · exact deferred_past σ P α _ k hn c b a φ rfl (hi hk).2 (hc hn)

theorem upper_defer_preserves [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .eventually a φ))
    (hc : DeferCondition σ P α k c b a φ)
    (hs : Node.holds σ P α k (upperEventuallyDefer c d b m a φ)) :
    EvaluatedInvariant σ P α k (upperEventuallyDefer c d b m a φ) := by
  simp only [upperEventuallyDefer, EvaluatedInvariant, and_true]
  intro hk hn
  let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩)
  let β := (ClockResetSet.singleton d 0).apply γ
  have hβc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
  have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
  have hs' := hs
  simp only [upperEventuallyDefer, Node.holds, dif_pos hk, dif_pos hn] at hs'
  have hm : (P.interval ⟨k.1 + 1,hn⟩).leftBoundary = m := hs'.2
  have hright : (P.interval ⟨k.1,hk⟩).rightBoundary = ¬ₘ m :=
    (P.adjacent_rightBoundary_eq_complement_leftBoundary ⟨k.1,hk⟩ hn).trans
      (congrArg Marker.complement hm)
  constructor
  · have hh := (hi hk).1
    change (β d : ℝ) <[Marker.conj b (¬ₘ m)] (β c : ℝ)
    rw [hβc,hβd,NNReal.coe_zero]
    change (0 : ℝ) <[Marker.conj b (¬ₘ m)]
      ((α c : ℝ) + ((P.interval ⟨k.1,hk⟩).right - (P.interval ⟨k.1,hk⟩).left))
    simpa only [hright, add_sub_assoc] using hh
  · exact deferred_past σ P α β k hn c b a φ hβc (hi hk).2 (hc hn)

theorem eventually_checks_preserve [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) :
    ((0 : ℝ) < (a : ℝ) → Node.holds σ P α k (upperEventuallyCheck c d b m a φ) →
      EvaluatedInvariant σ P α k (upperEventuallyCheck c d b m a φ)) ∧
    (Node.holds σ P α k (boundedEventuallyCheck c d b q m a φ) →
      EvaluatedInvariant σ P α k (boundedEventuallyCheck c d b q m a φ)) := by
  constructor
  · intro hpos hs
    simp only [upperEventuallyCheck, EvaluatedInvariant, evaluated_gt,
      and_true, true_and]
    intro hk hn
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩)
    let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ
    have hβc : β c = a := by
      simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
    have hβd : β d = 0 := by
      change ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ d = 0
      rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [hcd.symm])]
      exact ClockResetSet.apply_singleton_self d 0 γ
    simp only [upperEventuallyCheck, Node.holds, dif_pos hk, dif_pos hn] at hs
    constructor
    · change (β d : ℝ) <[Marker.conj m (¬ₘ m)] (β c : ℝ)
      rw [hβd,hβc,NNReal.coe_zero]
      exact Or.inl hpos
    · exact reset_lower_past σ P β _ hn c m a φ hβc hs.2.2.2
  · intro hs
    simp only [boundedEventuallyCheck, EvaluatedInvariant, evaluated_gt, evaluated_lt,
      and_true, true_and]
    intro hk hn
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩)
    let β := (ClockResetSet.singleton c a).apply γ
    have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
    have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
    simp only [boundedEventuallyCheck, Node.holds, dif_pos hk, dif_pos hn] at hs
    constructor
    · change (β d : ℝ) <[Marker.conj m q] (β c : ℝ)
      rw [hβd,hβc]
      have hg := (Node.holds_lt σ P γ ⟨k.1 + 1,by omega⟩ d (Marker.conj q m) a).1 hs.2.2.1
      have he : Marker.conj q m = Marker.conj m q := by cases q <;> cases m <;> rfl
      simpa only [he] using hg
    · exact reset_lower_past σ P β _ hn c m a φ hβc hs.2.2.2.2

/-- A certified branch is one single branch satisfying both the judgement
and every predicate invariant under the recursive reset/next interpretation. -/
def CertifiedBranchSatisfied (branches : List (Node Clock Var)) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P) : Prop :=
  ∃ B ∈ branches, Node.holds σ P α k B ∧ EvaluatedInvariant σ P α k B

theorem upperAlways_complete_preserving [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .always a φ))) :
    CertifiedBranchSatisfied (upperAlwaysBranches c d b a φ) σ P α k := by
  obtain ⟨B,hB,h⟩ := upperAlways_complete σ P α k c d b a φ hcd hst hs
  exact ⟨B,hB,h,always_branches_preserve σ P α k c d b ○ a φ hcd B (Or.inl hB) h⟩

theorem boundedAlways_complete_preserving [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .always a φ))) :
    CertifiedBranchSatisfied (boundedAlwaysBranches c d b q a φ) σ P α k := by
  obtain ⟨B,hB,h⟩ := boundedAlways_complete σ P α k c d b q a φ hcd hst hs
  exact ⟨B,hB,h,always_branches_preserve σ P α k c d b q a φ hcd B (Or.inr hB) h⟩

private theorem upper_certified_of_deferCondition [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hc : DeferCondition σ P α k c b a φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .eventually a φ))) :
    CertifiedBranchSatisfied (upperEventuallyBranches c d b a φ) σ P α k := by
  classical
  obtain ⟨B,hB,h⟩ := upperEventually_complete σ P α k c d b a φ hcd hi hst hs
  refine ⟨B,hB,h,?_⟩
  by_cases ha : a = 0
  · simp only [upperEventuallyBranches, if_pos ha, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl
    · exact upper_defer_preserves σ P α k c d b ○ a φ hcd hi hc h
    · exact upper_defer_preserves σ P α k c d b ● a φ hcd hi hc h
    · trivial
  · have hp : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ha)
    simp only [upperEventuallyBranches, if_neg ha, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · exact upper_defer_preserves σ P α k c d b ○ a φ hcd hi hc h
    · exact upper_defer_preserves σ P α k c d b ● a φ hcd hi hc h
    · exact (eventually_checks_preserve σ P α k c d b ○ ○ a φ hcd).1 hp h
    · exact (eventually_checks_preserve σ P α k c d b ○ ● a φ hcd).1 hp h

private theorem bounded_certified_of_deferCondition [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hc : DeferCondition σ P α k c b a φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .eventually a φ))) :
    CertifiedBranchSatisfied (boundedEventuallyBranches c d b q a φ) σ P α k := by
  obtain ⟨B,hB,h⟩ := boundedEventually_complete σ P α k c d b q a φ hi hst hs
  refine ⟨B,hB,h,?_⟩
  simp only [boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact bounded_defer_preserves σ P α k c d b q ○ a φ hi hc
  · exact bounded_defer_preserves σ P α k c d b q ● a φ hi hc
  · simp [boundedEventuallyFinish, EvaluatedInvariant, evaluated_gt]
  · simp [boundedEventuallyFinish, EvaluatedInvariant, evaluated_gt]
  · exact (eventually_checks_preserve σ P α k c d b q ○ a φ hcd).2 h
  · exact (eventually_checks_preserve σ P α k c d b q ● a φ hcd).2 h

/-- Literal `↑` `◇` completeness with the full unified invariant.
The preferred-defer condition is decided inside the proof, not assumed. -/
theorem upperEventually_complete_preserving [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.upper c b .eventually a φ))) :
    CertifiedBranchSatisfied (upperEventuallyBranches c d b a φ) σ P α k := by
  classical
  by_cases hc : DeferCondition σ P α k c b a φ
  · exact upper_certified_of_deferCondition σ P α k c d b a φ hcd hi hst hc hs
  · simp only [DeferCondition, not_forall, not_or, not_not] at hc
    obtain ⟨hn,hφ,hng⟩ := hc
    have hk : k.1 < P.size := by omega
    let m := (P.interval ⟨k.1 + 1,hn⟩).leftBoundary
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩)
    by_cases ha : a = 0
    · exact ⟨.plain φ, by simp [upperEventuallyBranches, ha], hφ, trivial⟩
    · have hp : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ha)
      have hg : (a : ℝ) <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
        by_contra hnot
        exact hng ((Judgement.upperAlways_guard_complement _ _ _ _).2 hnot)
      have hb := upper_check_witness σ P α k hn c d b a φ hcd hg hφ hs
      refine ⟨upperEventuallyCheck c d b m a φ, ?_, hb, ?_⟩
      · cases m <;> simp [upperEventuallyBranches, ha]
      · exact (eventually_checks_preserve σ P α k c d b ○ m a φ hcd).1 hp hb

/-- Literal `↑↓` `◇` completeness selects finish/check whenever
blind deferral would lose the invariant for no past satisfaction. -/
theorem boundedEventually_complete_preserving [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .eventually a φ))
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : Node.holds σ P α k (.predicate (.bounded c d b q .eventually a φ))) :
    CertifiedBranchSatisfied (boundedEventuallyBranches c d b q a φ) σ P α k := by
  classical
  by_cases hc : DeferCondition σ P α k c b a φ
  · exact bounded_certified_of_deferCondition σ P α k c d b q a φ hcd hi hst hc hs
  · simp only [DeferCondition, not_forall, not_or, not_not] at hc
    obtain ⟨hn,hφ,hng⟩ := hc
    have hk : k.1 < P.size := by omega
    let m := (P.interval ⟨k.1 + 1,hn⟩).leftBoundary
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩)
    by_cases hf : (a : ℝ) <[Marker.notConj q m] (γ d : ℝ)
    · have hb : Node.holds σ P α k (boundedEventuallyFinish d q m a φ) := by
        simp only [boundedEventuallyFinish, Node.holds, dif_pos hk, dif_pos hn]
        refine ⟨?_, (Node.holds_gt σ P γ _ d (Marker.notConj q m) a).2 hf, rfl⟩
        simpa only [Node.holds, dif_pos hk] using hφ
      refine ⟨boundedEventuallyFinish d q m a φ, ?_, hb, ?_⟩
      · cases m <;> simp [boundedEventuallyBranches]
      · simp [boundedEventuallyFinish, EvaluatedInvariant, evaluated_gt]
    · have hdg : (γ d : ℝ) <[Marker.conj q m] (a : ℝ) :=
        (Judgement.boundedAlways_right_guard_complement _ _ _ _).2 hf
      have hg : (a : ℝ) <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
        by_contra hnot
        exact hng ((Judgement.upperAlways_guard_complement _ _ _ _).2 hnot)
      have hb := bounded_check_witness σ P α k hn c d b q a φ hcd hg hdg hφ hs
      refine ⟨boundedEventuallyCheck c d b q m a φ, ?_, hb, ?_⟩
      · cases m <;> simp [boundedEventuallyBranches]
      · exact (eventually_checks_preserve σ P α k c d b q m a φ hcd).2 hb

end STLTableau.UnboundedClocked
