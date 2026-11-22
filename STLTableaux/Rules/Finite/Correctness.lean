import STLTableaux.Rules.Finite.ClockedSoundness

namespace STLTableau
open scoped STL
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

/-- Syntactic condition used only in transferring always-rule soundness.
An unclocked predicate may contain arbitrary STL temporal operators. -/
def NoClockedEventually : Judgement Clock Var → Prop
  | .predicate (.upper _ _ .eventually _ _) => False
  | .predicate (.bounded _ _ _ _ .eventually _ _) => False
  | .next Ψ | .reset _ Ψ => NoClockedEventually Ψ
  | .conj Φ Ψ => NoClockedEventually Φ ∧ NoClockedEventually Ψ
  | _ => True

@[simp] theorem noEventually_markedLT (c : Clock) (m : Marker) (a : NNReal) :
    NoClockedEventually (Judgement.markedLT (Var := Var) c m a) := by cases m <;> trivial
@[simp] theorem noEventually_markedGT (c : Clock) (m : Marker) (a : NNReal) :
    NoClockedEventually (Judgement.markedGT (Var := Var) c m a) := by cases m <;> trivial

private theorem residual_of_interval_satisfaction
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (Ψ : Judgement Clock Var)
    (hn : NoClockedEventually Ψ) (hs : satisfies σ P α k Ψ) :
    Judgement.Satisfies σ P α k Ψ := by
  induction Ψ generalizing α k with
  | terminal => exact hs
  | clock c r a => exact hs
  | leftMarker m => exact hs
  | predicate p =>
      by_cases hk : k.1 < P.size
      · simp only [satisfies, dif_pos hk] at hs
        simp only [Judgement.Satisfies, dif_pos hk]
        cases p with
        | plain φ => exact hs
        | upper c b kind I φ =>
            cases kind with
            | always => exact fun t ht _ => hs t ht
            | eventually => exact hn.elim
        | bounded c d b q kind I φ =>
            cases kind with
            | always => exact fun t ht _ => hs t ht
            | eventually => exact hn.elim
      · simp [satisfies, hk] at hs
  | next Ψ ih =>
      by_cases hk : k.1 < P.size
      · simp only [satisfies, dif_pos hk] at hs
        simp only [Judgement.Satisfies, dif_pos hk]
        exact ih _ _ hn hs
      · simp [satisfies, hk] at hs
  | reset Λ Ψ ih => exact ih _ _ hn hs
  | conj Φ Ψ ihΦ ihΨ => exact ⟨ihΦ _ _ hn.1 hs.1, ihΨ _ _ hn.2 hs.2⟩

private theorem upperAlways_no_eventually [DecidableEq Clock]
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (Ψ : Judgement Clock Var) (hmem : Ψ ∈ (upperAlways c d b I φ).branches) :
    NoClockedEventually Ψ := by
  simp only [upperAlways, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [upperAlways_defer, upperAlways_check, NoClockedEventually]

private theorem boundedAlways_no_eventually [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (Ψ : Judgement Clock Var) (hmem : Ψ ∈ (boundedAlways c d b q I φ).branches) :
    NoClockedEventually Ψ := by
  simp only [boundedAlways, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [boundedAlways_defer, boundedAlways_check, boundedAlways_finish, NoClockedEventually]

private theorem sound_from_residual [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p)
    (ha : ∀ hk : k.1 < P.size, AlwaysSafe (P.interval ⟨k.1, hk⟩) α p)
    (hn : ∀ Ψ ∈ R.branches, NoClockedEventually Ψ)
    (hs : branchSatisfied R σ P α k) : satisfies σ P α k (.predicate p) := by
  obtain ⟨Ψ, hmem, hΨ⟩ := hs
  have hlegacy := hr.branch_sound σ P α k hi
    ⟨Ψ, hmem, residual_of_interval_satisfaction σ P α k Ψ (hn Ψ hmem) hΨ⟩
  exact satisfies_of_residual σ P α k (.predicate p) ha hlegacy

/-- Soundness does not require the conjuncts for no past satisfaction. The hypothesis below
is the invariant with only those conjuncts omitted, written out rather
than introducing a second named invariant. No stability is assumed. -/
theorem rule_sound_without_past [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size,
      let J := P.interval ⟨k.1, hk⟩
      match p with
      | .plain _ => True
      | .upper c b .always I _ =>
          (α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower
      | .bounded c d b q .always I _ =>
          ((α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower) ∧
          ((α d : ℝ) <[Marker.conj b q] ((α c : ℝ) + (I.upper - I.lower)))
      | .upper c b .eventually I _ =>
          ((α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper) ∧
          ((0 : ℝ) <[Marker.conj b J.rightBoundary]
            ((α c : ℝ) + (J.right - J.left)))
      | .bounded c d b q .eventually I _ =>
          ((α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper) ∧
          ((α d : ℝ) <[Marker.conj b q] (α c : ℝ)))
    (hs : branchSatisfied R σ P α k) : satisfies σ P α k (.predicate p) := by
  cases hr with
  | plainAnd φ ψ => exact (plainAnd_correct_at φ ψ σ P α k).2 hs
  | plainOr φ ψ => exact plainOr_sound_at φ ψ σ P α k hs
  | plainUntil φ ψ => exact plainUntil_sound_at φ ψ σ P α k hs
  | plainRelease φ ψ => exact plainRelease_sound_at φ ψ σ P α k hs
  | openEventually c I φ => exact (openEventually_correct_at c I φ σ P α k).2 hs
  | openAlways c I φ => exact (openAlways_correct_at c I φ σ P α k).2 hs
  | upperAlways c d b I φ hcd =>
      exact sound_from_residual (.upperAlways c d b I φ hcd) σ P α k
        (fun hk => invariant_implies_residual σ P α k hk _ (hi hk)) hi
        (upperAlways_no_eventually c d b I φ) hs
  | boundedAlways c d b q I φ hcd =>
      exact sound_from_residual (.boundedAlways c d b q I φ hcd) σ P α k
        (fun hk => invariant_implies_residual σ P α k hk _ (hi hk))
        (fun hk => (hi hk).1) (boundedAlways_no_eventually c d b q I φ) hs
  | upperEventually c d b I φ hcd =>
      exact upperEventually_sound_at c d b I φ hcd σ P α k
        hi hs
  | boundedEventually c d b q I φ hcd =>
      exact boundedEventually_sound_at c d b q I φ hcd σ P α k
        hi hs

/-- Soundness in Theorem 3.13 under the source predicate invariant. -/
theorem rule_sound [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hs : branchSatisfied R σ P α k) : satisfies σ P α k (.predicate p) := by
  apply rule_sound_without_past hr σ P α k ?_ hs
  intro hk
  cases p with
  | plain φ => trivial
  | upper c b kind I φ =>
      cases kind with
      | always => exact hi hk
      | eventually => exact ⟨(hi hk).1, (hi hk).2.1⟩
  | bounded c d b q kind I φ =>
      cases kind with
      | always => exact hi hk
      | eventually => exact ⟨(hi hk).1, (hi hk).2.1⟩

/-- Theorem 3.13 (expansion-rule correctness) for the finite rule families.
The partition is fully stable for the source formula. -/
theorem rule_correct [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) :
    satisfies σ P α k (.predicate p) ↔ branchSatisfied R σ P α k :=
  ⟨rule_complete hr σ P α k hi hst, rule_sound hr σ P α k hi⟩

end STLTableau
