import STLTableaux.Semantics.Invariants.Invariants

namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

/-- Only always predicates need a start-position condition when forgetting the
residual interpretation; eventuality witnesses can simply retain their values. -/
def AlwaysSafe (J : MarkedInterval) (α : ClockValuation Clock) :
    IntervalPredicate Clock Var → Prop
  | .upper c b .always I _ | .bounded c _ b _ .always I _ =>
      (α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower
  | _ => True

def AlwaysSafeAt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, AlwaysSafe (P.interval ⟨k.1, hk⟩) α p
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      AlwaysSafeAt σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1, hk⟩))
        ⟨k.1 + 1, by omega⟩ Ψ
  | k, .reset Λ Ψ => AlwaysSafeAt σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => AlwaysSafeAt σ P α k Φ ∧ AlwaysSafeAt σ P α k Ψ
  | _, _ => True

@[simp] theorem alwaysSafe_markedLT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    AlwaysSafeAt σ P α k (Judgement.markedLT c m a) := by cases m <;> trivial

@[simp] theorem alwaysSafe_markedGT (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    AlwaysSafeAt σ P α k (Judgement.markedGT c m a) := by cases m <;> trivial

theorem predicate_of_residual (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (p : IntervalPredicate Clock Var)
    (hi : AlwaysSafe J α p) (hs : IntervalPredicate.Satisfies σ J α p) :
    predicateSatisfies σ J α p := by
  cases p with
  | plain φ => exact hs
  | upper c b kind I φ =>
      cases kind with
      | always => exact fun t ht => hs t ht (always_safe J α c b I hi rfl rfl ht)
      | eventually =>
          intro t ht
          obtain ⟨w, hw, _, hwφ⟩ := hs t ht
          exact ⟨w, hw, hwφ⟩
  | bounded c d b q kind I φ =>
      cases kind with
      | always => exact fun t ht => hs t ht (always_safe J α c b I hi rfl rfl ht)
      | eventually =>
          intro t ht
          obtain ⟨w, hw, _, hwφ⟩ := hs t ht
          exact ⟨w, hw, hwφ⟩

theorem satisfies_of_residual (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (Ψ : Judgement Clock Var)
    (hi : AlwaysSafeAt σ P α k Ψ) (hs : Judgement.Satisfies σ P α k Ψ) :
    satisfies σ P α k Ψ := by
  induction Ψ generalizing α k with
  | terminal => exact hs
  | clock c r a => exact hs
  | leftMarker m => exact hs
  | predicate p =>
      by_cases hk : k.1 < P.size
      · simp only [satisfies, Judgement.Satisfies, dif_pos hk] at hs ⊢
        exact predicate_of_residual σ _ α p (hi hk) hs
      · simpa only [satisfies, Judgement.Satisfies, dif_neg hk] using hs
  | next Ψ ih =>
      by_cases hk : k.1 < P.size
      · simp only [satisfies, Judgement.Satisfies, dif_pos hk] at hs ⊢
        exact ih _ _ (hi hk) hs
      · simpa only [satisfies, Judgement.Satisfies, dif_neg hk] using hs
  | reset Λ Ψ ih => exact ih _ _ hi hs
  | conj Φ Ψ ihΦ ihΨ => exact ⟨ihΦ _ _ hi.1 hs.1, ihΨ _ _ hi.2 hs.2⟩

/-- The predicate invariant implies the residual invariant used by the rule catalogue. -/
theorem invariant_implies_residual (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (p : IntervalPredicate Clock Var) (h : Invariant σ P α k hk p) :
    IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p := by
  cases p with
  | plain φ => trivial
  | upper c b kind I φ =>
      cases kind with
      | always => trivial
      | eventually => exact ⟨h.1, h.2.1⟩
  | bounded c d b q kind I φ =>
      cases kind with
      | eventually => exact ⟨h.1, h.2.1⟩
      | always =>
          refine ⟨h.2, ?_⟩
          rcases h.1 with hc | ⟨hc, hbc⟩
          · left
            rcases h.2 with hd | ⟨hd, _⟩ <;> linarith
          · rcases h.2 with hd | ⟨hd, hbq⟩
            · left; linarith
            · right
              exact ⟨by linarith, (Marker.includes_conj _ _).2
                ⟨(Marker.includes_imp _ _).1 hbc ((Marker.includes_conj _ _).1 hbq).1,
                 ((Marker.includes_conj _ _).1 hbq).2⟩⟩

set_option maxHeartbeats 2000000 in
-- Enumerating the ten finite rule families and their marker alternatives needs extra elaboration steps.
/-- Guards in every clocked-always branch ensure that its target always
predicate starts at or after the interval on which it is evaluated. -/
theorem branch_alwaysSafe [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (Ψ : Judgement Clock Var) (hmem : Ψ ∈ R.branches)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hs : Judgement.Satisfies σ P α k Ψ) : AlwaysSafeAt σ P α k Ψ := by
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
      Judgement.Satisfies,
      ClockRelation.Holds, Marker.imp, Marker.conj, Marker.notConj, Marker.complement,
      BoundedTimeInterval.lower_nonnegative, ClockResetSet.apply,
      ClockResetSet.union, ClockResetSet.singleton] <;> aesop

/-- Section 3 rule completeness for the interval semantics and invariant.
The hypothesis for no past satisfaction is used only through the proved semantic bridge. -/
theorem rule_complete [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : satisfies σ P α k (.predicate p)) : branchSatisfied R σ P α k := by
  by_cases hk : k.1 < P.size
  · have hlegacy : Judgement.Satisfies σ P α k (.predicate p) := by
      simp only [satisfies, dif_pos hk] at hs
      simp only [Judgement.Satisfies, dif_pos hk]
      exact (predicate_iff_residual σ P α k hk p (hi hk) hst).1 hs
    obtain ⟨Ψ, hmem, hΨ⟩ := hr.branch_complete σ P α k
      (fun hk => invariant_implies_residual σ P α k hk p (hi hk)) hst hlegacy
    exact ⟨Ψ, hmem, satisfies_of_residual σ P α k Ψ
      (branch_alwaysSafe hr Ψ hmem σ P α k hΨ) hΨ⟩
  · simp [satisfies, hk] at hs

end STLTableau
