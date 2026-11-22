import STLTableaux.Rules.Finite.Correctness
import STLTableaux.Rules.Finite.SelectedBranches

namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

/-- A left endpoint at or after the current piece cannot overlap any past
cover. Equality is handled using disjointness of actual partition pieces. -/
theorem pastSeparated_of_lower (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] I.lower) :
    PastSeparated σ P α k hk c b I φ := by
  intro j hj _
  have hjk : j < (⟨k.1, hk⟩ : Fin P.size) := (mem_pastTrue σ P k φ j).1 hj |>.1
  have hord := P.ordered hjk
  rcases h with h | ⟨h, hm⟩
  · left; linarith
  · by_cases hlt : (P.interval j).right < (P.interval ⟨k.1, hk⟩).left
    · left; linarith
    · have heq := le_antisymm hord (le_of_not_gt hlt)
      right
      refine ⟨by linarith, (Marker.includes_imp _ _).2 ?_⟩
      intro hb
      apply (Marker.includes_complement _).2
      intro hjr
      have hkl := (Marker.includes_imp _ _).1 hm hb
      have hwj := MarkedInterval.right_mem (P.interval j) (P.nonempty j) hjr
      have hwk := MarkedInterval.left_mem (P.interval ⟨k.1, hk⟩) (P.nonempty _) hkl
      exact (P.pairwiseDisjoint hjk.ne).notMem_of_mem_left hwj (heq.symm ▸ hwk)

/-- If the current operand is not uniformly true, it contributes no new past
cover on advancing one piece; the old bound transports by clock elapse. -/
theorem pastSeparated_next_of_not_plain (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (P.interval ⟨k.1 + 1, hn⟩).left - (β c : ℝ) =
      (P.interval ⟨k.1, by omega⟩).left - (α c : ℝ))
    (hp : PastSeparated σ P α k (by omega) c b I φ)
    (hnot : ¬ satisfies σ P α k (.predicate (.plain φ))) :
    PastSeparated σ P β ⟨k.1 + 1, by omega⟩ hn c b I φ := by
  have hk : k.1 < P.size := by omega
  have he : pastTrue σ P (⟨k.1 + 1, by omega⟩ : Judgement.Position P) φ =
      pastTrue σ P k φ := by
    ext j
    simp only [mem_pastTrue]
    constructor
    · rintro ⟨hj, hφ⟩
      have hne : j.1 ≠ k.1 := by
        intro heq
        have hjEq : j = ⟨k.1, hk⟩ := Fin.ext heq
        apply hnot
        simp only [satisfies, dif_pos hk]
        exact hjEq ▸ hφ
      exact ⟨by omega, hφ⟩
    · rintro ⟨hj, hφ⟩
      exact ⟨by omega, hφ⟩
  intro j hj hm
  rw [he] at hj hm
  have hb := hp j hj hm
  rcases hb with hb | ⟨hb, hm⟩
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨by linarith, hm⟩

/-- The invariant is evaluated under each reset and elapsed valuation;
terminal positions carry no interval-predicate invariant. -/
def EvaluatedInvariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, Invariant σ P α k hk p
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      EvaluatedInvariant σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩))
        ⟨k.1 + 1, by omega⟩ Ψ
  | k, .reset Λ Ψ => EvaluatedInvariant σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedInvariant σ P α k Φ ∧ EvaluatedInvariant σ P α k Ψ
  | _, _ => True

def PredicatePast (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size) :
    IntervalPredicate Clock Var → Prop
  | .upper c b .eventually I φ | .bounded c _ b _ .eventually I φ =>
      PastSeparated σ P α k hk c b I φ
  | _ => True

def PastAt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, PredicatePast σ P α k hk p
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      PastAt σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩))
        ⟨k.1 + 1, by omega⟩ Ψ
  | k, .reset Λ Ψ => PastAt σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => PastAt σ P α k Φ ∧ PastAt σ P α k Ψ
  | _, _ => True

@[simp] theorem pastAt_markedLT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    PastAt σ P α k (Judgement.markedLT c m a) := by cases m <;> trivial
@[simp] theorem pastAt_markedGT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    PastAt σ P α k (Judgement.markedGT c m a) := by cases m <;> trivial

private theorem invariant_of_parts (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (p : IntervalPredicate Clock Var)
    (ho : IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p)
    (ha : AlwaysSafe (P.interval ⟨k.1, hk⟩) α p) (hp : PredicatePast σ P α k hk p) :
    Invariant σ P α k hk p := by
  cases p with
  | plain φ => trivial
  | upper c b kind I φ =>
      cases kind with
      | always => exact ha
      | eventually => exact ⟨ho.1, ho.2, hp⟩
  | bounded c d b q kind I φ =>
      cases kind with
      | always => exact ⟨ha, ho.1⟩
      | eventually => exact ⟨ho.1, ho.2, hp⟩

private theorem evaluatedInvariant_of_parts
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (Ψ : Judgement Clock Var)
    (ho : Judgement.EvaluatedInvariant σ P α k Ψ) (ha : AlwaysSafeAt σ P α k Ψ)
    (hp : PastAt σ P α k Ψ) : EvaluatedInvariant σ P α k Ψ := by
  induction Ψ generalizing α k with
  | predicate p =>
      intro hk
      have ho' : IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p := by
        simpa only [Judgement.EvaluatedInvariant, dif_pos hk] using ho
      exact invariant_of_parts σ P α k hk p ho' (ha hk) (hp hk)
  | next Ψ ih =>
      intro hk
      have ho' := ho
      simp only [Judgement.EvaluatedInvariant, dif_pos hk] at ho'
      exact ih _ _ ho' (ha hk) (hp hk)
  | reset Λ Ψ ih => exact ih _ _ ho ha hp
  | conj Φ Ψ ihΦ ihΨ => exact ⟨ihΦ _ _ ho.1 ha.1 hp.1, ihΨ _ _ ho.2 ha.2 hp.2⟩
  | terminal => trivial
  | clock c r a => trivial
  | leftMarker m => trivial

/-- An already satisfied residual branch becomes a satisfied interval-semantics branch
with the predicate invariant once the condition for no past satisfaction has been checked. -/
theorem certified_branch [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (Ψ : Judgement Clock Var) (hm : Ψ ∈ R.branches)
    (hs : Judgement.Satisfies σ P α k Ψ) (hp : PastAt σ P α k Ψ) :
    satisfies σ P α k Ψ ∧ EvaluatedInvariant σ P α k Ψ := by
  have ha := branch_alwaysSafe hr Ψ hm σ P α k hs
  exact ⟨satisfies_of_residual σ P α k Ψ ha hs,
    evaluatedInvariant_of_parts σ P α k Ψ
      (hr.preservesEvaluatedInvariant hm σ P α k
        (fun hk => invariant_implies_residual σ P α k hk p (hi hk))
        (Judgement.nonPredicateSatisfies_of_satisfies hs)) ha hp⟩

/-- A deferred eventuality is preferred when the current piece contributes
no true cover, or when its earliest possible witness is already beyond it. -/
def DeferCondition (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    IntervalPredicate Clock Var → Prop
  | .upper c b .eventually I φ | .bounded c _ b _ .eventually I φ =>
      ∀ hn : k.1 + 1 < P.size,
        ¬ satisfies σ P α k (.predicate (.plain φ)) ∨
        (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
          <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower
  | _ => True

private theorem deferred_past (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : β c = ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c)
    (hp : PastSeparated σ P α k (by omega) c b I φ)
    (hcond : ¬ satisfies σ P α k (.predicate (.plain φ)) ∨
      (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, by omega⟩) c : ℝ)
        <[Marker.imp b (P.interval ⟨k.1 + 1, hn⟩).leftBoundary] I.lower) :
    PastSeparated σ P β ⟨k.1 + 1, by omega⟩ hn c b I φ := by
  rcases hcond with hnot | hlo
  · apply pastSeparated_next_of_not_plain σ P α β k hn c b I φ ?_ hp hnot
    rw [hc]
    exact Judgement.next_left_sub_elapse_eq P α ⟨k.1, by omega⟩ hn c
  · apply pastSeparated_of_lower σ P β ⟨k.1 + 1, by omega⟩ hn c b I φ
    simpa only [hc] using hlo

private theorem bounded_defer_past (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .eventually I φ))
    (hc : DeferCondition σ P α k (.bounded c d b q .eventually I φ)) :
    PastAt σ P α k (boundedEventually_defer c d b q m I φ) := by
  simp only [boundedEventually_defer, PastAt, pastAt_markedLT, PredicatePast, true_and]
  intro hk hn
  exact deferred_past σ P α _ k hn c b I φ rfl (hi hk).2.2 (hc hn)

private theorem upper_defer_past [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .eventually I φ))
    (hc : DeferCondition σ P α k (.upper c b .eventually I φ)) :
    PastAt σ P α k (upperEventually_defer c d b m I φ) := by
  simp only [upperEventually_defer, PastAt, pastAt_markedLT, PredicatePast, and_true, true_and, implies_true]
  intro hk hn
  exact deferred_past σ P α _ k hn c b I φ
    (ClockResetSet.apply_singleton_of_ne 0 _ hcd) (hi hk).2.2 (hc hn)

private theorem reset_lower_past (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = I.lower) (hm : (P.interval ⟨k.1, hk⟩).leftBoundary = m) :
    PastSeparated σ P α k hk c m I φ := by
  apply pastSeparated_of_lower σ P α k hk c m I φ
  rw [hc, hm]
  exact Or.inr ⟨rfl, (Marker.includes_imp _ _).2 id⟩

private theorem upper_check_past [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hs : Judgement.Satisfies σ P α k (upperEventually_check c d b m I φ)) :
    PastAt σ P α k (upperEventually_check c d b m I φ) := by
  simp only [upperEventually_check, PastAt, pastAt_markedGT, PredicatePast,
    and_true, true_and, implies_true]
  intro hk hn
  simp only [upperEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hs
  apply reset_lower_past σ P _ _ hn c m I φ ?_ hs.2.2.2
  simp [ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton] <;> rfl

private theorem bounded_check_past [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hs : Judgement.Satisfies σ P α k (boundedEventually_check c d b q m I φ)) :
    PastAt σ P α k (boundedEventually_check c d b q m I φ) := by
  simp only [boundedEventually_check, PastAt, pastAt_markedGT, pastAt_markedLT,
    PredicatePast, and_true, true_and, implies_true]
  intro hk hn
  simp only [boundedEventually_check, Judgement.Satisfies, dif_pos hk, dif_pos hn] at hs
  apply reset_lower_past σ P _ _ hn c m I φ ?_ hs.2.2.2.2
  simp <;> rfl

private theorem opening_past [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hs : Judgement.Satisfies σ P α k
      (⟦c ↦ᶜ 0⟧ ·ⱼ (.predicate (.upper c m .eventually I φ) ∧ⱼ lty[m]))) :
    PastAt σ P α k
      (⟦c ↦ᶜ 0⟧ ·ⱼ (.predicate (.upper c m .eventually I φ) ∧ⱼ lty[m])) := by
  simp only [PastAt, PredicatePast, and_true]
  intro hk
  simp only [Judgement.Satisfies, dif_pos hk] at hs
  apply pastSeparated_of_lower σ P _ k hk c m I φ
  simp only [ClockResetSet.apply_singleton_self, NNReal.coe_zero, hs.2]
  rcases I.lower_nonnegative.eq_or_lt with hz | hp
  · exact Or.inr ⟨hz, (Marker.includes_imp _ _).2 id⟩
  · exact Or.inl hp

/-- Every branch preserves past-cover separation under the preferred defer
condition. Reset/check branches establish separation from geometry alone. -/
theorem branch_past [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hc : DeferCondition σ P α k p)
    (Ψ : Judgement Clock Var) (hmem : Ψ ∈ R.branches)
    (hs : Judgement.Satisfies σ P α k Ψ) : PastAt σ P α k Ψ := by
  cases hr
  case openEventually c I φ =>
    simp only [openEventually, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact opening_past σ P α k c _ I φ hs
  case upperEventually c d b I φ hcd =>
    classical
    by_cases hz : I.lower = 0
    · simp only [upperEventually, if_pos hz, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact upper_defer_past σ P α k c d b ○ I φ hcd hi hc
      · exact upper_defer_past σ P α k c d b ● I φ hcd hi hc
      · simp [PastAt, PredicatePast]
    · simp only [upperEventually, if_neg hz, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact upper_defer_past σ P α k c d b ○ I φ hcd hi hc
      · exact upper_defer_past σ P α k c d b ● I φ hcd hi hc
      · exact upper_check_past σ P α k c d b ○ I φ hs
      · exact upper_check_past σ P α k c d b ● I φ hs
  case boundedEventually c d b q I φ hcd =>
    simp only [boundedEventually, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bounded_defer_past σ P α k c d b q ○ I φ hi hc
    · exact bounded_defer_past σ P α k c d b q ● I φ hi hc
    · simp [boundedEventually_finish, PastAt, PredicatePast]
    · simp [boundedEventually_finish, PastAt, PredicatePast]
    · exact bounded_check_past σ P α k c d b q ○ I φ hs
    · exact bounded_check_past σ P α k c d b q ● I φ hs
  all_goals
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openAlways, upperAlways,
      boundedAlways, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [PastAt, PredicatePast, upperAlways_defer, upperAlways_check,
        boundedAlways_defer, boundedAlways_check, boundedAlways_finish]

def CertifiedBranchSatisfied (R : ExpansionRule Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P) : Prop :=
  ∃ Ψ ∈ R.branches, satisfies σ P α k Ψ ∧ EvaluatedInvariant σ P α k Ψ

private theorem certified_of_residual [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hc : DeferCondition σ P α k p) (hs : R.BranchSatisfied σ P α k) :
    CertifiedBranchSatisfied R σ P α k := by
  obtain ⟨Ψ, hmem, hΨ⟩ := hs
  exact ⟨Ψ, hmem, certified_branch hr σ P α k hi Ψ hmem hΨ
    (branch_past hr σ P α k hi hc Ψ hmem hΨ)⟩

private theorem residual_source [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (p : IntervalPredicate Clock Var)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : satisfies σ P α k (.predicate p)) :
    Judgement.Satisfies σ P α k (.predicate p) := by
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk] at hs
    simp only [Judgement.Satisfies, dif_pos hk]
    exact (predicate_iff_residual σ P α k hk p (hi hk) hst).1 hs
  · simp [satisfies, hk] at hs

/-- Preferred deferral already suffices for a satisfied invariant-preserving
branch. The final theorem below also handles the cases requiring check/reset. -/
theorem certified_complete_of_deferCondition [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) (hc : DeferCondition σ P α k p)
    (hs : satisfies σ P α k (.predicate p)) : CertifiedBranchSatisfied R σ P α k :=
  certified_of_residual hr σ P α k hi hc
    (hr.branch_complete σ P α k
      (fun hk => invariant_implies_residual σ P α k hk p (hi hk)) hst
      (residual_source σ P α k p hi hst hs))

/-- Proposition 3.14 (invariant preservation). Select a satisfied branch
whose predicate invariants hold under the enclosing resets and next operators.
The predicate invariant includes the condition for no past satisfaction. -/
theorem rule_complete_preserving [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : satisfies σ P α k (.predicate p)) : CertifiedBranchSatisfied R σ P α k := by
  classical
  by_cases hc : DeferCondition σ P α k p
  · exact certified_complete_of_deferCondition hr σ P α k hi hst hc hs
  cases hr
  case upperEventually c d b I φ hcd =>
    simp only [DeferCondition, not_forall, not_or, not_not] at hc
    obtain ⟨hn, hφ, hng⟩ := hc
    have hk : k.1 < P.size := by omega
    let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
    have hφold : Judgement.Satisfies σ P α k (.predicate (.plain φ)) := hφ
    have hold := residual_source σ P α k (.upper c b .eventually I φ) hi hst hs
    by_cases hz : I.lower = 0
    · refine ⟨.predicate (.plain φ), by simp [upperEventually, hz], ?_⟩
      exact certified_branch (.upperEventually c d b I φ hcd) σ P α k hi _
        (by simp [upperEventually, hz]) hφold (by simp [PastAt, PredicatePast])
    · have hpos : 0 < I.lower := lt_of_le_of_ne I.lower_nonnegative (Ne.symm hz)
      have hg : I.lower <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
        by_contra hnot
        exact hng ((Judgement.upperAlways_guard_complement _ _ _ _).2 hnot)
      have hb := upper_check_witness c d b I φ hcd hpos σ P α k hn hg hφold hold
      have hm : upperEventually_check c d b m I φ ∈ (upperEventually c d b I φ).branches := by
        cases m <;> simp [upperEventually, hz]
      exact ⟨_, hm, certified_branch (.upperEventually c d b I φ hcd) σ P α k hi _ hm hb
        (upper_check_past σ P α k c d b m I φ hb)⟩
  case boundedEventually c d b q I φ hcd =>
    simp only [DeferCondition, not_forall, not_or, not_not] at hc
    obtain ⟨hn, hφ, hng⟩ := hc
    have hk : k.1 < P.size := by omega
    let m := (P.interval ⟨k.1 + 1, hn⟩).leftBoundary
    let γ := ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩)
    have hφold : Judgement.Satisfies σ P α k (.predicate (.plain φ)) := hφ
    have hold := residual_source σ P α k (.bounded c d b q .eventually I φ) hi hst hs
    by_cases hf : I.lower <[Marker.notConj q m] (γ d : ℝ)
    · have hb : Judgement.Satisfies σ P α k (boundedEventually_finish d q m I φ) := by
        simp only [boundedEventually_finish, Judgement.Satisfies, dif_pos hk, dif_pos hn]
        refine ⟨?_, (Judgement.satisfies_markedGT σ P γ _ d (Marker.notConj q m)
          ⟨I.lower, I.lower_nonnegative⟩).2 hf, by trivial⟩
        simpa only [Judgement.Satisfies, dif_pos hk] using hφold
      have hm : boundedEventually_finish d q m I φ ∈ (boundedEventually c d b q I φ).branches := by
        cases m <;> simp [boundedEventually]
      exact ⟨_, hm, certified_branch (.boundedEventually c d b q I φ hcd) σ P α k hi _ hm hb
        (by simp [boundedEventually_finish, PastAt, PredicatePast])⟩
    · have hdg : (γ d : ℝ) <[Marker.conj q m] I.lower :=
        (Judgement.boundedAlways_right_guard_complement _ _ _ _).2 hf
      have hg : I.lower <[Marker.conj b (¬ₘ m)] (γ c : ℝ) := by
        by_contra hnot
        exact hng ((Judgement.upperAlways_guard_complement _ _ _ _).2 hnot)
      have hb := bounded_check_witness c d b q I φ hcd σ P α k hn hg hdg hφold hold
      have hm : boundedEventually_check c d b q m I φ ∈ (boundedEventually c d b q I φ).branches := by
        cases m <;> simp [boundedEventually]
      exact ⟨_, hm, certified_branch (.boundedEventually c d b q I φ hcd) σ P α k hi _ hm hb
        (bounded_check_past σ P α k c d b q m I φ hb)⟩
  all_goals simp [DeferCondition] at hc

/-- Theorem 3.13 and Proposition 3.14 combined. Satisfaction of the source
is equivalent to satisfaction of a branch with its predicate invariants. -/
theorem rule_correct_preserving [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) :
    satisfies σ P α k (.predicate p) ↔ CertifiedBranchSatisfied R σ P α k := by
  constructor
  · exact rule_complete_preserving hr σ P α k hi hst
  · rintro ⟨Ψ, hmem, hΨ, _⟩
    exact rule_sound hr σ P α k hi ⟨Ψ, hmem, hΨ⟩

end STLTableau
