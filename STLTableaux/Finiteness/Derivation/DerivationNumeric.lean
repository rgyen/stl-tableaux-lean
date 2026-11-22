import STLTableaux.Finiteness.Derivation.Branches.RawBranchNumeric
import STLTableaux.Finiteness.Derivation.BoundaryInvariant

/-! Forward propagation from the actual input numeric invariant and erased
non-predicate leaves. No per-node numeric assumption is used as admission. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

theorem ACIdem.numeric_iff {J K : MixedJ Clock Var} (h : ACIdem J K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Judgement.EvaluatedNumeric σ P α k J ↔ Judgement.EvaluatedNumeric σ P α k K := by
  induction h generalizing α with
  | refl => rfl
  | symm h ih => exact (ih α).symm
  | trans h g ih ig => exact (ih α).trans (ig α)
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr (ih α) (ig α)
  | reset R h ih => exact ih (R.apply α)
  | resetDistrib R J K => rfl
  | resetUnused R J hd =>
      exact Judgement.numeric_congr J σ P _ α k (reset_apply_agrees_on_free R J hd α)
  | resetNested R S J =>
      simp only [Judgement.EvaluatedNumeric,ClockResetSet.apply_union_eq_comp]

theorem numeric_unused_singleton_reset [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (d : Clock) (v : NNReal) (J : MixedJ Clock Var) (hd : d ∉ J.freeClocks) :
    Judgement.EvaluatedNumeric σ P α k (.reset (ClockResetSet.singleton d v) J) ↔
    Judgement.EvaluatedNumeric σ P α k J := by
  change Judgement.EvaluatedNumeric σ P ((ClockResetSet.singleton d v).apply α) k J ↔ _
  apply Judgement.numeric_congr
  intro c hc
  exact ClockResetSet.apply_singleton_of_ne v α (by intro h; subst c; exact hd hc)

theorem withBoundaryGuard_numeric (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    Judgement.EvaluatedNumeric σ P α k (withBoundaryGuard c b Γ) ↔
      Judgement.EvaluatedNumeric σ P α k Γ := by
  cases b <;> simp [withBoundaryGuard, Judgement.EvaluatedNumeric]

/-- All ordinary source numeric obligations, evaluated under their actual
reset ancestors. Boundary comparisons are supplied by actual child guards. -/
def Resolve.NumericOccurrences [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop :=
  match D with
  | .leaf _ => True
  | .conj D E => D.NumericOccurrences σ P α k ∧ E.NumericOccurrences σ P α k
  | .reset R D => D.NumericOccurrences σ P (R.apply α) k
  | .structural _ D => D.NumericOccurrences σ P α k
  | @Resolve.expandCtx _ _ _ p _ _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α) ∧
        D.NumericOccurrences σ P α k
  | @Resolve.expandSolo _ _ _ p _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α) ∧
        D.NumericOccurrences σ P α k
  | .boundaryRequired _ _ D => D.NumericOccurrences σ P α k
  | .boundaryOptional _ _ D => D.NumericOccurrences σ P α k
  | .unusedReset _ _ _ _ D => D.NumericOccurrences σ P α k

private theorem boundary_child_numeric [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Γ : MixedJ Clock Var) (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks)
    (hp : Judgement.EvaluatedNumeric σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)))
    (hΓ : Judgement.EvaluatedNumeric σ P ((ClockResetSet.singleton d 0).apply α) k Γ) :
    Judgement.EvaluatedNumeric σ P α k (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) := by
  have hupper : Judgement.EvaluatedNumeric σ P ((ClockResetSet.singleton d 0).apply α) k
      (.predicate (.upper c m kind I φ)) := by
    intro hk
    exact BoundaryInvariant.numeric_bounded_to_upper _ _ c d m (¬ₘ ℓ) kind I φ
      (P.nonempty _) (hp hk)
  have hupper' : Judgement.EvaluatedNumeric σ P α k
      (.predicate (.upper c m kind I φ)) :=
    (numeric_unused_singleton_reset σ P α k d 0 _ (by
      simp only [Section3.Judgement.freeClocks, Set.mem_singleton_iff]
      exact Ne.symm hcd)).1 hupper
  exact ⟨hupper',trivial,(withBoundaryGuard_numeric σ P α k _ _ _).2
    ((numeric_unused_singleton_reset σ P α k d 0 Γ hdΓ).1 hΓ)⟩

/-- Input numeric information and satisfied non-predicate leaves derive all
ordinary occurrence obligations and both outputs' numeric invariants. -/
theorem Resolve.numeric_occurrences_and_outputs [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Resolve J H A) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : Judgement.EvaluatedNumeric σ P α k J)
    (hs : Judgement.nonPredicateHolds σ P α k A) :
    D.NumericOccurrences σ P α k ∧ Judgement.EvaluatedNumeric σ P α k H ∧
      Judgement.EvaluatedNumeric σ P α k A := by
  induction D generalizing α with
  | leaf h => exact ⟨trivial,hi,hi⟩
  | conj D E ih ig =>
      obtain ⟨hD,hH,hA⟩ := ih α hi.1 hs.1
      obtain ⟨hE,hG,hB⟩ := ig α hi.2 hs.2
      exact ⟨⟨hD,hE⟩,⟨hH,hG⟩,⟨hA,hB⟩⟩
  | reset R D ih => exact ih (R.apply α) hi hs
  | structural h D ih => exact ih α ((h.numeric_iff σ P α k).1 hi) hs
  | expandCtx hb hn hf D ih =>
      have hchild := (D.nonPredicate_recover σ P α k hs).1
      have hB := hb.numeric_preserves σ P α k hi.1 hchild.1
      obtain ⟨hD,hH,hA⟩ := ih α ⟨hB,hi.2⟩ hs
      exact ⟨⟨hi.1,hD⟩,⟨hi.1,hH⟩,hA⟩
  | expandSolo hb hn hf D ih =>
      have hchild := (D.nonPredicate_recover σ P α k hs).1
      have hB := hb.numeric_preserves σ P α k hi hchild
      obtain ⟨hD,hH,hA⟩ := ih α hB hs
      exact ⟨⟨hi,hD⟩,⟨hi,hH⟩,hA⟩
  | boundaryRequired frozen hdΓ D ih =>
      exact ih α (boundary_child_numeric σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hi.1.1 hi.2.2) hs
  | boundaryOptional frozen hdΓ D ih =>
      exact ih α (boundary_child_numeric σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hi.1 hi.2.2) hs
  | unusedReset d v hdJ hdH D ih =>
      exact ih α ((numeric_unused_singleton_reset σ P α k d v _ hdJ).1 hi) hs

/-- Temporal truth is unnecessary for the non-predicate projection. -/
theorem holds_implies_nonPredicate {J : MixedJ Clock Var}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.holds σ P α k J) : Judgement.nonPredicateHolds σ P α k J := by
  induction J generalizing α k with
  | terminal => exact hs
  | marker => exact hs
  | clock => exact hs
  | predicate => trivial
  | conj J K ih ig => exact ⟨ih α k hs.1,ig α k hs.2⟩
  | reset R J ih => exact ih (R.apply α) k hs
  | next J ih =>
      simp only [Judgement.holds,Judgement.nonPredicateHolds] at hs ⊢
      split at hs
      · split
        · exact ih _ _ hs
        · contradiction
      · contradiction

/-- Numeric-only occurrence recovery, kept separate from its forward derivation. -/
theorem Resolve.recover_of_numericOccurrences [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : D.NumericOccurrences σ P α k) (hs : Judgement.holds σ P α k A) :
    Judgement.holds σ P α k J ∧ Judgement.holds σ P α k H := by
  induction D generalizing α with
  | leaf h => exact ⟨hs,hs⟩
  | conj D E ih ig =>
      obtain ⟨hJ,hH⟩ := ih α hi.1 hs.1
      obtain ⟨hK,hG⟩ := ig α hi.2 hs.2
      exact ⟨⟨hJ,hK⟩,⟨hH,hG⟩⟩
  | reset R D ih => exact ih (R.apply α) hi hs
  | structural h D ih =>
      obtain ⟨hK,hH⟩ := ih α hi hs
      exact ⟨(h.holds_iff σ P α k).2 hK,hH⟩
  | expandCtx hb hn hf D ih =>
      obtain ⟨hBG,hH⟩ := ih α hi.2 hs
      have hp := hb.numeric_sound σ P α k hi.1 hBG.1
      exact ⟨⟨hp,hBG.2⟩,⟨hp,hH⟩⟩
  | expandSolo hb hn hf D ih =>
      obtain ⟨hB,hH⟩ := ih α hi.2 hs
      have hp := hb.numeric_sound σ P α k hi.1 hB
      exact ⟨hp,⟨hp,hH⟩⟩
  | boundaryRequired frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      exact ⟨recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩,hH⟩
  | boundaryOptional frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      have hraw := recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩
      exact ⟨⟨hraw.1.1,hraw.2⟩,hH⟩
  | unusedReset d v hdJ hdH D ih =>
      obtain ⟨hJ,hH⟩ := ih α hi hs
      exact ⟨(unused_singleton_reset σ P α k d v _ hdJ).2 hJ,hH⟩

/-- The local soundness conclusion uses only the INPUT numeric invariant.
All internal numeric obligations are derived by forward propagation from the
input and non-predicate leaves; no all-node assumption remains. -/
theorem Resolve.recover_from_input_numeric [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Resolve J H A) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : Judgement.EvaluatedNumeric σ P α k J)
    (hs : Judgement.holds σ P α k A) :
    Judgement.holds σ P α k J ∧ Judgement.holds σ P α k H := by
  have hocc := (D.numeric_occurrences_and_outputs σ P α k hi
    (holds_implies_nonPredicate σ P α k hs)).1
  exact D.recover_of_numericOccurrences σ P α k hocc hs

end STLTableau.Section4.Finiteness
