import STLTableaux.Rules.Finite.Preservation
import STLTableaux.Rules.Unbounded.UnboundedCorrectness

/-! Branch guards preserve the non-past clauses for the forward trace-invariant
induction. They also preserve the nonnegative scope origins established
when clocks are introduced. No branch predicate satisfaction is assumed. -/
namespace STLTableau
open scoped STL
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

set_option maxHeartbeats 2000000 in
theorem branch_alwaysSafe_of_nonPredicate [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (Ψ : Judgement Clock Var) (hmem : Ψ ∈ R.branches)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : Judgement.NonPredicateSatisfies σ P α k Ψ) : AlwaysSafeAt σ P α k Ψ := by
  cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease,
      openEventually, openAlways, upperAlways, boundedAlways,
      upperEventually, boundedEventually, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hmem <;>
    (try split_ifs at hmem) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem) <;>
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    by_cases hk : k.1 < P.size <;>
    by_cases hn : k.1 + 1 < P.size <;>
    simp_all [AlwaysSafeAt, AlwaysSafe, upperAlways_defer, upperAlways_check,
      boundedAlways_defer, boundedAlways_check, boundedAlways_finish,
      upperEventually_defer, upperEventually_check,
      boundedEventually_defer, boundedEventually_check, boundedEventually_finish,
      Judgement.NonPredicateSatisfies,
      ClockRelation.Holds, Marker.imp, Marker.conj, Marker.notConj, Marker.complement,
      BoundedTimeInterval.lower_nonnegative, ClockResetSet.apply,
      ClockResetSet.union, ClockResetSet.singleton] <;> aesop


/-- Each branch satisfies the numeric and always-start clauses in its reset
and next scopes. The eventuality past-cover bounds are handled separately. -/
theorem branch_nonpast_parts [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (Ψ : Judgement Clock Var) (hmem : Ψ ∈ R.branches)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1,hk⟩) α p)
    (hs : Judgement.NonPredicateSatisfies σ P α k Ψ) :
    Judgement.EvaluatedInvariant σ P α k Ψ ∧ AlwaysSafeAt σ P α k Ψ :=
  ⟨hr.preservesEvaluatedInvariant hmem σ P α k hi hs,
    branch_alwaysSafe_of_nonPredicate hr Ψ hmem σ P α k hs⟩


/-- Each clock used as a scope endpoint was set no further back than time zero. -/
def OriginBound (J : MarkedInterval) (α : ClockValuation Clock) :
    IntervalPredicate Clock Var → Prop
  | .plain _ => True
  | .upper c _ _ _ _ => (α c : ℝ) ≤ J.left
  | .bounded c d _ _ _ _ _ => (α c : ℝ) ≤ J.left ∧ (α d : ℝ) ≤ J.left

/-- Transport the bound through the next and reset operators of a judgement. -/
def OriginBoundAt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, OriginBound (P.interval ⟨k.1, hk⟩) α p
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      OriginBoundAt σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩))
        ⟨k.1 + 1, by omega⟩ Ψ
  | k, .reset R Ψ => OriginBoundAt σ P (R.apply α) k Ψ
  | k, .conj Ψ Ξ => OriginBoundAt σ P α k Ψ ∧ OriginBoundAt σ P α k Ξ
  | _, _ => True

theorem generated_upper_scope_subset_domain (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker) (hne : J.carrier.Nonempty)
    (hJ : J.carrier ⊆ σ.domain) (hclock : (α c : ℝ) ≤ J.left) :
    (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier ⊆ σ.domain := by
  intro t ht
  change MarkedInterval.Mem ⟨J.left - α c, J.right, b, J.rightBoundary⟩ t at ht
  refine FiniteSignal.mem_domain.mpr ⟨(sub_nonneg.mpr hclock).trans
    (MarkedInterval.left_le_of_mem ht), ?_⟩
  by_cases hl : t ≤ J.left
  · obtain ⟨u, hu⟩ := hne
    exact lt_of_le_of_lt (hl.trans (MarkedInterval.left_le_of_mem hu))
      (FiniteSignal.mem_domain.mp (hJ hu)).2
  · exact (FiniteSignal.mem_domain.mp (hJ ⟨Or.inl (lt_of_not_ge hl), ht.2⟩)).2

theorem generated_bounded_scope_subset_domain (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain)
    (hclock : (α c : ℝ) ≤ J.left) :
    (⟨b, J.left - α c, J.left - α d, q⟩ : Scope).carrier ⊆ σ.domain :=
  (IntervalPredicate.boundedScope_subset_upperScope J α c d b q hne).trans
    (generated_upper_scope_subset_domain σ J α c b hne hJ hclock)

private theorem left_nonneg (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) : 0 ≤ (P.interval i).left := by
  let D : MarkedInterval := ⟨0, σ.horizon, ●, ○⟩
  have hD : D.carrier = σ.domain := MarkedInterval.carrier_eq D
  have hsub : (P.interval i).carrier ⊆ D.carrier := by
    rw [hD]
    exact fun _ ht => P.covers.subset (Set.mem_iUnion.2 ⟨i, ht⟩)
  rcases ((MarkedInterval.subset_iff (P.nonempty i)).1 hsub).1 with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

private theorem next_bound (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (i : Fin P.size) (hi : i.val + 1 < P.size) (c : Clock)
    (hc : (α c : ℝ) ≤ (P.interval i).left) :
    (ClockResetSet.elapse α (Judgement.duration P i) c : ℝ) ≤
      (P.interval ⟨i.val + 1, hi⟩).left := by
  have he := Judgement.next_left_sub_elapse_eq (L := 0) (R := σ.horizon) P α i hi c
  exact sub_nonneg.mp (he.symm ▸ sub_nonneg.mpr hc)

private theorem right_reset [DecidableEq Clock] (α : ClockValuation Clock)
    (c d : Clock) (a : NNReal) (hcd : c ≠ d) :
    ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply α d = 0 := by
  rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ α (by simp [hcd.symm])]
  exact ClockResetSet.apply_singleton_self d 0 α

private theorem left_reset [DecidableEq Clock] (α : ClockValuation Clock)
    (c d : Clock) (a : NNReal) :
    ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply α c = a := by
  rw [ClockResetSet.apply_union_eq_left_of_mem _ _ α (by simp)]
  exact ClockResetSet.apply_singleton_self c a α

private theorem origin_bound_lt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) : OriginBoundAt σ P α k (c <ᶜ[m] a) := by
  cases m <;> trivial

private theorem origin_bound_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) : OriginBoundAt σ P α k (c >ᶜ[m] a) := by
  cases m <;> trivial

private theorem age_of_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) (h : Judgement.NonPredicateSatisfies σ P α k (c >ᶜ[m] a)) :
    (a : ℝ) ≤ α c := by
  cases m
  · exact (show a < α c from h).le
  · exact h

set_option maxHeartbeats 5000000 in
-- The proof enumerates the concrete branches, including both marker variants.
set_option linter.unusedSimpArgs false in
/-- Clock initialization and guarded resets preserve the scope-origin bound. -/
theorem branch_origin_bound [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (Ψ : Judgement Clock Var) (hmem : Ψ ∈ R.branches)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : OriginBoundAt σ P α k (.predicate p))
    (hs : Judgement.NonPredicateSatisfies σ P α k Ψ) :
    OriginBoundAt σ P α k Ψ := by
  classical
  cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease,
      openEventually, openAlways, upperAlways, boundedAlways,
      upperEventually, boundedEventually, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hmem <;>
    (try split_ifs at hmem) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem) <;>
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [OriginBoundAt, OriginBound, upperAlways_defer, upperAlways_check,
      boundedAlways_defer, boundedAlways_check, boundedAlways_finish,
      upperEventually_defer, upperEventually_check, boundedEventually_defer,
      boundedEventually_check, boundedEventually_finish, true_and, and_true,
      ClockResetSet.apply_singleton_self, origin_bound_lt, origin_bound_gt,
      NNReal.coe_zero, implies_true] at hi ⊢
  all_goals first | trivial | (intro hk; exact left_nonneg σ P _) | skip
  all_goals
    intro hk hn
    have h0 := left_nonneg σ P ⟨k.1 + 1, hn⟩
    have hOrigin := hi hk
    have hLeft : ∀ c, (α c : ℝ) ≤ (P.interval ⟨k.1, hk⟩).left →
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩) c : ℝ) ≤
          (P.interval ⟨k.1 + 1, hn⟩).left := next_bound σ P α ⟨k.1, hk⟩ hn
    try simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [left_reset, right_reset, ClockResetSet.apply_singleton_of_ne, NNReal.coe_zero]
    first
    | exact ⟨hLeft _ hOrigin, h0⟩
    | exact ⟨hLeft _ hOrigin.1, hLeft _ hOrigin.2⟩
    | simp only [upperAlways_check, upperEventually_check, boundedAlways_check,
        boundedEventually_check, Judgement.NonPredicateSatisfies, dif_pos hk, dif_pos hn] at hs
      have hg := age_of_gt _ _ _ _ _ _ _ hs.2.1
      first
      | exact ⟨hg.trans (hLeft _ hOrigin), h0⟩
      | exact ⟨hg.trans (hLeft _ hOrigin.1), hLeft _ hOrigin.2⟩

/-- The bound gives the domain side condition of C.9 and C.10. -/
theorem OriginBound.scope_subset_domain (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (p : IntervalPredicate Clock Var)
    (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain)
    (h : OriginBound J α p) : (IntervalPredicate.scope J α p).carrier ⊆ σ.domain := by
  cases p with
  | plain => exact hJ
  | upper c b _ _ _ => exact generated_upper_scope_subset_domain σ J α c b hne hJ h
  | bounded c d b q _ _ _ => exact generated_bounded_scope_subset_domain σ J α c d b q hne hJ h.1

end STLTableau

namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

def Node.nonPredicateHolds (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Node Clock Var → Prop
  | _, .plain _ | _, .predicate _ => True
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .marker m => if h : k.1 < P.size then
      (P.interval ⟨k.1,h⟩).leftBoundary = m else m = ●
  | k, .next Ψ => if h : k.1 < P.size then
      Node.nonPredicateHolds σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1,h⟩))
        ⟨k.1 + 1,by omega⟩ Ψ else False
  | k, .reset Λ Ψ => Node.nonPredicateHolds σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => Node.nonPredicateHolds σ P α k Φ ∧ Node.nonPredicateHolds σ P α k Ψ

/-- The unified infinite-bound invariant with only the clause for no past satisfaction
omitted; this evaluator follows actual reset and next scopes. -/
def EvaluatedNonpast (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Node Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size,
      let J := P.interval ⟨k.1,hk⟩
      match p with
      | .upper c b .always a _ | .bounded c _ b _ .always a _ =>
          (α c : ℝ) <[Marker.imp b J.leftBoundary] (a : ℝ)
      | .upper c b .eventually _ _ =>
          (0 : ℝ) <[Marker.conj b J.rightBoundary] ((α c : ℝ) + J.right - J.left)
      | .bounded c d b q .eventually _ _ =>
          (α d : ℝ) <[Marker.conj b q] (α c : ℝ)
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      EvaluatedNonpast σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1,hk⟩))
        ⟨k.1 + 1,by omega⟩ Ψ
  | k, .reset Λ Ψ => EvaluatedNonpast σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedNonpast σ P α k Φ ∧ EvaluatedNonpast σ P α k Ψ
  | _, _ => True

private theorem duration_coe {D : Set ℝ} (P : IntervalPartition D) (i : Fin P.size) :
    (Judgement.duration P i : ℝ) = (P.interval i).right - (P.interval i).left := rfl

private theorem reset_union_left [DecidableEq Clock] (c d : Clock) (a z : NNReal)
    (α : ClockValuation Clock) :
    ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d z)).apply α c = a := by
  rw [ClockResetSet.apply_union_eq_left_of_mem _ _ α (by simp)]
  exact ClockResetSet.apply_singleton_self c a α

private theorem reset_union_right [DecidableEq Clock] (c d : Clock) (a z : NNReal)
    (α : ClockValuation Clock) (hcd : c ≠ d) :
    ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d z)).apply α d = z := by
  rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ α (by simp [hcd.symm])]
  exact ClockResetSet.apply_singleton_self d z α

set_option maxHeartbeats 4000000 in
/-- Every unbounded rule branch preserves the non-past clauses
using only source numeric clauses and the branch's non-predicate guards. -/
theorem branch_nonpast_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (B : Node Clock Var) (hB : B ∈ Bs)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : EvaluatedNonpast σ P α k (.predicate p))
    (hs : Node.nonPredicateHolds σ P α k B) : EvaluatedNonpast σ P α k B := by
  cases hr
  all_goals
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hB
    try split_ifs at hB
  all_goals
    try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals casesm* Marker
  all_goals by_cases hk : k.1 < P.size
  all_goals by_cases hn : k.1 + 1 < P.size
  all_goals try have hadj := P.adjacent_rightBoundary_eq_complement_leftBoundary ⟨k.1, by omega⟩ hn
  all_goals
    simp_all [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
      boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
      upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
      boundedEventuallyFinish, EvaluatedNonpast, Node.nonPredicateHolds,
      Node.lt, Node.gt, ClockRelation.Holds, reset_union_left, reset_union_right,
      ClockResetSet.apply_singleton_self, ClockResetSet.apply_singleton_of_ne,
      ClockResetSet.elapse, ne_comm, duration_coe,
      Marker.imp, Marker.conj, Marker.notConj, Marker.complement]
  all_goals first | positivity | omega | linarith | aesop

/-- Opening also establishes all numeric clauses from the marker guard
alone; no truth of its generated temporal predicate is needed. -/
theorem opening_nonpast_preserves [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hs : Node.nonPredicateHolds σ P α k (opening c m kind a φ)) :
    EvaluatedNonpast σ P α k (opening c m kind a φ) := by
  change (∀ hk : k.1 < P.size, _) ∧ True
  refine ⟨?_, trivial⟩
  intro hk
  have hm : (P.interval ⟨k.1,hk⟩).leftBoundary = m := by
    simpa only [opening, Node.nonPredicateHolds, dif_pos hk] using hs.2
  have hc : (ClockResetSet.singleton c 0).apply α c = 0 :=
    ClockResetSet.apply_singleton_self c 0 α
  cases kind with
  | always =>
      change (_ : ℝ) <[Marker.imp m (P.interval ⟨k.1,hk⟩).leftBoundary] (a : ℝ)
      rw [hc, hm]
      rcases a.coe_nonneg.eq_or_lt with hz | hp
      · exact Or.inr ⟨hz, (Marker.includes_imp _ _).2 id⟩
      · exact Or.inl hp
  | eventually =>
      change (0 : ℝ) <[Marker.conj m (P.interval ⟨k.1,hk⟩).rightBoundary]
        (((ClockResetSet.singleton c 0).apply α c : ℝ) + (P.interval ⟨k.1,hk⟩).right - (P.interval ⟨k.1,hk⟩).left)
      rw [hc]
      simp only [NNReal.coe_zero, zero_add]
      rw [← hm]
      have hne := (MarkedInterval.nonempty_iff _).1 (P.nonempty ⟨k.1,hk⟩)
      rcases hne with hlt | ⟨heq, hm⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, hm⟩


/-- Scope origins for unbounded rule judgements use the same clock bound. -/
def OriginBoundAt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Node Clock Var → Prop
  | k, .predicate (.upper c _ _ _ _) => ∀ hk : k.1 < P.size,
      (α c : ℝ) ≤ (P.interval ⟨k.1, hk⟩).left
  | k, .predicate (.bounded c d _ _ _ _ _) => ∀ hk : k.1 < P.size,
      (α c : ℝ) ≤ (P.interval ⟨k.1, hk⟩).left ∧ (α d : ℝ) ≤ (P.interval ⟨k.1, hk⟩).left
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      OriginBoundAt σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩))
        ⟨k.1 + 1, by omega⟩ Ψ
  | k, .reset R Ψ => OriginBoundAt σ P (R.apply α) k Ψ
  | k, .conj Ψ Ξ => OriginBoundAt σ P α k Ψ ∧ OriginBoundAt σ P α k Ξ
  | _, _ => True

private theorem origin_bound_lt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) : OriginBoundAt σ P α k (Node.lt c m a) := by
  cases m <;> trivial

private theorem origin_bound_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) : OriginBoundAt σ P α k (Node.gt c m a) := by
  cases m <;> trivial

private theorem age_of_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker)
    (a : NNReal) (h : Node.nonPredicateHolds σ P α k (Node.gt c m a)) :
    (a : ℝ) ≤ α c := by
  cases m
  · exact (show a < α c from h).le
  · exact h

set_option maxHeartbeats 5000000 in
-- As in the finite case, elaboration checks all literal branches at once.
set_option linter.unusedSimpArgs false in
/-- The unbounded check branches also test the elapsed clock before resetting it. -/
theorem branch_origin_bound [DecidableEq Clock]
    {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (B : Node Clock Var) (hB : B ∈ Bs)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : OriginBoundAt σ P α k (.predicate p))
    (hs : Node.nonPredicateHolds σ P α k B) : OriginBoundAt σ P α k B := by
  cases hr
  all_goals
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hB
    try split_ifs at hB
  all_goals
    try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
      boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
      upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
      boundedEventuallyFinish, OriginBoundAt, true_and, and_true,
      ClockResetSet.apply_singleton_self, origin_bound_lt, origin_bound_gt,
      NNReal.coe_zero, implies_true] at hi ⊢
  all_goals
    intro hk hn
    have h0 := left_nonneg σ P ⟨k.1 + 1, hn⟩
    have hOrigin := hi hk
    have hLeft : ∀ c, (α c : ℝ) ≤ (P.interval ⟨k.1, hk⟩).left →
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩) c : ℝ) ≤
          (P.interval ⟨k.1 + 1, hn⟩).left := next_bound σ P α ⟨k.1, hk⟩ hn
    try simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [left_reset, right_reset, ClockResetSet.apply_singleton_of_ne, NNReal.coe_zero]
    first
    | exact ⟨hLeft _ hOrigin, h0⟩
    | exact ⟨hLeft _ hOrigin.1, hLeft _ hOrigin.2⟩
    | simp only [upperAlwaysCheck, upperEventuallyCheck, boundedAlwaysCheck,
        boundedEventuallyCheck, Node.nonPredicateHolds, dif_pos hk, dif_pos hn] at hs
      have hg := age_of_gt _ _ _ _ _ _ _ hs.2.1
      first
      | exact ⟨hg.trans (hLeft _ hOrigin), h0⟩
      | exact ⟨hg.trans (hLeft _ hOrigin.1), hLeft _ hOrigin.2⟩

theorem opening_origin_bound [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    OriginBoundAt σ P α k (opening c m kind a φ) := by
  change (∀ hk : k.1 < P.size, _) ∧ True
  refine ⟨?_, trivial⟩
  intro hk
  rw [ClockResetSet.apply_singleton_self, NNReal.coe_zero]
  exact left_nonneg σ P _

/-- For unbounded timing, the real scope is the same marked interval. -/
theorem scope_subset_domain_of_origin_bound (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (hk : k.1 < P.size) (p : Predicate Clock Var)
    (h : OriginBoundAt σ P α k (.predicate p)) :
    (scope (P.interval ⟨k.1, hk⟩) α p).carrier ⊆ σ.domain := by
  let i : Fin P.size := ⟨k.1, hk⟩
  have hD : (P.interval i).carrier ⊆ σ.domain :=
    fun _ ht => P.covers.subset (Set.mem_iUnion.2 ⟨i, ht⟩)
  cases p with
  | upper c b _ _ _ =>
      exact generated_upper_scope_subset_domain σ _ α c b (P.nonempty i) hD (h hk)
  | bounded c d b q _ _ _ =>
      exact generated_bounded_scope_subset_domain σ _ α c d b q (P.nonempty i) hD (h hk).1

end STLTableau.UnboundedClocked
