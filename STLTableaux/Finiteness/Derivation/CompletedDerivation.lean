/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Derivation.DerivationNumeric
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Finiteness.Correctness.JudgementTableauSoundness
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCompleteness
import STLTableaux.Closure.Correctness.FaithfulClosureSoundness

/-! The completed constructions, defined independently of the selected
resolution relation. A leaf at Next retains the complete, unexpanded input
to the next frame. A merge is local syntax, not a claim of provenance.
The structural relation uses scoped conjunction/reset laws only. Nested
reset compaction is the ordered update: assignments overwritten by the
inner reset are dead in its scope, and the remaining assignments merge
without conflict. -/
namespace STLTableau.Section4.Finiteness.CompletedDerivation

open Section3
open scoped STL
variable {Clock Var : Type*}

/-- The residual comparison after substituting the two zero resets.
If the surviving left clock is reset too, check its actual constant.
Otherwise emit the strict guard; a non-strict zero comparison is automatic. -/
inductive MergeGuard (R : ClockResetSet Clock) (c : Clock) :
    Marker → MixedJ Clock Var → MixedJ Clock Var → Prop
  | closed (Γ) : MergeGuard R c .closed Γ Γ
  | fixed (Γ) (v : NNReal) : R.value c = some v → 0 < v → MergeGuard R c .open Γ Γ
  | free (Γ) : R.value c = none → MergeGuard R c .open Γ (withBoundaryGuard c .open Γ)

/-- An opening branch for the unclocked predicate supplies the `↑` form for the
merge. It resets a fresh clock to zero. -/
def Opening [DecidableEq Clock] (c d : Clock) (ℓ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (Γ : MixedJ Clock Var) : Prop :=
  ∃ e : Clock, e ≠ c ∧ e ≠ d ∧ e ∉ syntaxClocks Γ ∧
    RawBranch (.plain (timedFormula kind I φ)) (.reset (ClockResetSet.singleton e 0)
      (.conj (.predicate (.upper e ℓ kind I φ)) (.marker ℓ)))

theorem opening_exists [DecidableEq Clock] [Infinite Clock]
    (c d : Clock) (ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Γ : MixedJ Clock Var) : Opening c d ℓ kind I φ Γ := by
  have hf : ({c, d} ∪ syntaxClocks Γ : Set Clock).Finite :=
    (Set.finite_singleton d).insert c |>.union (syntaxClocks_finite Γ)
  obtain ⟨e, he⟩ := hf.exists_notMem
  have hs : e ≠ c ∧ e ≠ d ∧ e ∉ syntaxClocks Γ := by simpa [and_assoc] using he
  refine ⟨e, hs.1, hs.2.1, hs.2.2, ?_⟩
  cases I with
  | bounded I =>
      cases kind with
      | always =>
          refine RawBranch.finite (.openAlways e I φ)
            (B := .reset (ClockResetSet.singleton e 0)
              (.conj (.predicate (.upper e ℓ .always I φ)) (lty[ℓ]))) ?_
          cases ℓ <;> simp [STLTableau.ExpansionRule.openAlways]
      | eventually =>
          refine RawBranch.finite (.openEventually e I φ)
            (B := .reset (ClockResetSet.singleton e 0)
              (.conj (.predicate (.upper e ℓ .eventually I φ)) (lty[ℓ]))) ?_
          cases ℓ <;> simp [STLTableau.ExpansionRule.openEventually]
  | unbounded a =>
      cases kind
      · exact RawBranch.opening e ℓ .always a φ
      · exact RawBranch.opening e ℓ .eventually a φ

inductive Tree [DecidableEq Clock] :
    MixedJ Clock Var → MixedJ Clock Var → MixedJ Clock Var → Type _
  | leaf {J} : ResolutionLeaf J → Tree J J J
  | conj {J K H G A B} : Tree J H A → Tree K G B →
      Tree (.conj J K) (.conj H G) (.conj A B)
  | reset (R) {J H A} : Tree J H A → Tree (.reset R J) (.reset R H) (.reset R A)
  | structural {J K H A} : ACIdem J K → Tree K H A → Tree J H A
  | expandCtx {p B Γ H A} : RawBranch p B → (¬ p.IsAtomic) → FreshFor p B Γ →
      Tree (.conj B Γ) H A → Tree (.conj (.predicate p) Γ) (.conj (.predicate p) H) A
  | expandSolo {p B H A} : RawBranch p B → (¬ p.IsAtomic) → FreshWithoutContext p B →
      Tree B H A → Tree (.predicate p) (.conj (.predicate p) H) A
  /-- Both touching endpoints are reset to zero. Either marker may close
  their boundary, and the old left endpoint must be no later than zero
  with the marker comparison from the interval-merge lemma. -/
  | merge {R c d e m b ℓ kind I φ Γ K H A} :
      R.value d = some 0 → R.value e = some 0 → Marker.disj b ℓ = .closed →
      MergeGuard R c (Marker.imp ℓ m) Γ K →
      Tree (.reset R (.conj (.predicate (.upper c m kind I φ)) K)) H A →
      Tree (.reset R (.conj (.conj (.predicate (.bounded c d m b kind I φ))
        (.predicate (.upper e ℓ kind I φ))) Γ)) H A
  /-- General insertion-and-merge under the existing reset map. Keeping
  that map also permits the old right clock to occur elsewhere in `Γ`. -/
  | mergeOptional {R c d m b ℓ kind I φ Γ K H A} :
      R.value d = some 0 → Marker.disj b ℓ = .closed →
      Opening c d ℓ kind I φ (.reset R Γ) →
      MergeGuard R c (Marker.imp ℓ m) Γ K →
      Tree (.reset R (.conj (.predicate (.upper c m kind I φ))
        (.conj (.marker ℓ) K))) H A →
      Tree (.reset R (.conj (.predicate (.bounded c d m b kind I φ))
        (.conj (.marker ℓ) Γ))) H A
  /-- Optional insertion of an unclocked predicate is inseparable from its
  adjoining merge. The current marker witnesses its zero upper endpoint. -/
  | boundaryRequired {c d m ℓ kind I φ Γ H A} : c ≠ d → Opening c d ℓ kind I φ Γ →
      (d ∉ Γ.freeClocks) →
      Tree (.conj (.predicate (.upper c m kind I φ))
        (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A →
      Tree (.reset (ClockResetSet.singleton d 0)
        (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
          (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))) H A
  | boundaryOptional {c d m ℓ kind I φ Γ H A} : c ≠ d → Opening c d ℓ kind I φ Γ →
      (d ∉ Γ.freeClocks) →
      Tree (.conj (.predicate (.upper c m kind I φ))
        (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A →
      Tree (.reset (ClockResetSet.singleton d 0)
        (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.conj (.marker ℓ) Γ))) H A
  | unusedReset {J H A} (d : Clock) (v : NNReal) : (d ∉ J.freeClocks) →
      (d ∉ H.freeClocks) → Tree J H A → Tree (.reset (ClockResetSet.singleton d v) J) H A

inductive Member [DecidableEq Clock] :
    Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop
  | original {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var} :
      ConcreteContextual.catalogue.IsClosure (.ofState N) F →
      N.Ready → Member N F
  | completed {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
      {J H A} : Tree J H A →
      SafeNormalization J (.ofState N) → SafeNormalization H F →
      SafeNormalization A F.atomicProjection → Member N F


theorem MergeGuard.holds {R : ClockResetSet Clock} {c : Clock}
    {b : Marker} {Γ K : MixedJ Clock Var} (h : MergeGuard R c b Γ K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.holds σ P (R.apply α) k K) :
    (0 : ℝ) <[b] ((R.apply α c : NNReal) : ℝ) ∧
      Judgement.holds σ P (R.apply α) k Γ := by
  cases h with
  | closed Γ => exact ⟨by simpa only [markedLT_closed] using (R.apply α c).coe_nonneg, hs⟩
  | fixed Γ v hv hpos =>
      refine ⟨?_, hs⟩
      simpa [ClockResetSet.apply, hv, MarkedLT, Marker.Includes] using hpos
  | free Γ hfree => exact (withBoundaryGuard_holds σ P (R.apply α) k c .open Γ).1 hs

theorem MergeGuard.nonPredicate {R : ClockResetSet Clock} {c : Clock}
    {b : Marker} {Γ K : MixedJ Clock Var} (h : MergeGuard R c b Γ K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.nonPredicateHolds σ P (R.apply α) k K) :
    Judgement.nonPredicateHolds σ P (R.apply α) k Γ := by
  cases h with
  | closed | fixed => exact hs
  | free Γ hfree =>
      exact ((withBoundaryGuard_nonPredicate σ P (R.apply α) k c .open Γ).1 hs).2

theorem MergeGuard.numeric {R : ClockResetSet Clock} {c : Clock}
    {b : Marker} {Γ K : MixedJ Clock Var} (h : MergeGuard R c b Γ K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : Judgement.EvaluatedNumeric σ P (R.apply α) k Γ) :
    Judgement.EvaluatedNumeric σ P (R.apply α) k K := by
  cases h with
  | closed | fixed => exact hi
  | free Γ hfree => exact (withBoundaryGuard_numeric σ P (R.apply α) k c .open Γ).2 hi

private theorem merge_recover {R : ClockResetSet Clock} {c d e : Clock}
    {m b ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {Γ K : MixedJ Clock Var} (hd : R.value d = some 0) (he : R.value e = some 0)
    (hj : Marker.disj b ℓ = .closed) (hg : MergeGuard R c (Marker.imp ℓ m) Γ K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.holds σ P α k (.reset R (.conj (.predicate (.upper c m kind I φ)) K))) :
    Judgement.holds σ P α k (.reset R (.conj (.conj (.predicate (.bounded c d m b kind I φ))
      (.predicate (.upper e ℓ kind I φ))) Γ)) := by
  obtain ⟨hc, hΓ⟩ := hg.holds σ P α k hs.2
  have hd0 : ((R.apply α d : NNReal) : ℝ) = 0 := by simp [ClockResetSet.apply, hd]
  have he0 : ((R.apply α e : NNReal) : ℝ) = 0 := by simp [ClockResetSet.apply, he]
  have hj' : ((R.apply α d : NNReal) : ℝ) <[Marker.disj b ℓ] ((R.apply α e : NNReal) : ℝ) := by
    rw [hd0, he0, hj, markedLT_closed]
  exact ⟨(Judgement.predicate_merge_connected σ P (R.apply α) k c d e m b ℓ kind I φ
    hj' (he0 ▸ hc)).2 hs.1, hΓ⟩

private theorem merge_optional_recover {R : ClockResetSet Clock} {c d : Clock}
    {m b ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {Γ K : MixedJ Clock Var} (hd : R.value d = some 0)
    (hj : Marker.disj b ℓ = .closed) (hg : MergeGuard R c (Marker.imp ℓ m) Γ K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.holds σ P α k (.reset R (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) K)))) :
    Judgement.holds σ P α k (.reset R (.conj (.predicate (.bounded c d m b kind I φ))
      (.conj (.marker ℓ) Γ))) := by
  have hm := hs.2.1
  have hh := merge_recover hd hd hj hg σ P α k
    (show Judgement.holds σ P α k
      (.reset R (.conj (.predicate (.upper c m kind I φ)) K)) from ⟨hs.1, hs.2.2⟩)
  exact ⟨hh.1.1, hm, hh.2⟩

/-- All ordinary source numeric obligations, evaluated under their actual
reset ancestors. Boundary comparisons are supplied by actual child guards. -/
def Tree.NumericOccurrences [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Tree J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop :=
  match D with
  | .leaf _ => True
  | .conj D E => D.NumericOccurrences σ P α k ∧ E.NumericOccurrences σ P α k
  | .reset R D => D.NumericOccurrences σ P (R.apply α) k
  | .structural _ D => D.NumericOccurrences σ P α k
  | @Tree.expandCtx _ _ _ p _ _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α) ∧
        D.NumericOccurrences σ P α k
  | @Tree.expandSolo _ _ _ p _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α) ∧
        D.NumericOccurrences σ P α k
  | .merge _ _ _ _ D => D.NumericOccurrences σ P α k
  | .mergeOptional _ _ _ _ D => D.NumericOccurrences σ P α k
  | .boundaryRequired _ _ _ D => D.NumericOccurrences σ P α k
  | .boundaryOptional _ _ _ D => D.NumericOccurrences σ P α k
  | .unusedReset _ _ _ _ D => D.NumericOccurrences σ P α k
/-- Unconditional backward recovery of guards, resets, markers and next
non-predicate requirements. It needs no rule invariant, temporal truth or
assumed boundary comparison. This is the first independent ingredient for
future initial-path numeric propagation. -/
theorem Tree.nonPredicate_recover [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Tree J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.nonPredicateHolds σ P α k A) :
    Judgement.nonPredicateHolds σ P α k J ∧ Judgement.nonPredicateHolds σ P α k H := by
  induction D generalizing α with
  | leaf h => exact ⟨hs,hs⟩
  | conj D E ih ig =>
      obtain ⟨hJ,hH⟩ := ih α hs.1
      obtain ⟨hK,hG⟩ := ig α hs.2
      exact ⟨⟨hJ,hK⟩,⟨hH,hG⟩⟩
  | reset R D ih => exact ih (R.apply α) hs
  | structural h D ih =>
      obtain ⟨hK,hH⟩ := ih α hs
      exact ⟨(h.nonPredicate_iff σ P α k).2 hK,hH⟩
  | expandCtx hb hn hf D ih =>
      obtain ⟨hBG,hH⟩ := ih α hs
      exact ⟨⟨trivial,hBG.2⟩,⟨trivial,hH⟩⟩
  | expandSolo hb hn hf D ih =>
      obtain ⟨_,hH⟩ := ih α hs
      exact ⟨trivial,⟨trivial,hH⟩⟩
  | merge hd he hj hg D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      exact ⟨⟨⟨trivial,trivial⟩,hg.nonPredicate σ P α k hU.2⟩,hH⟩
  | mergeOptional hd hj ho hg D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      exact ⟨⟨trivial,hU.2.1,hg.nonPredicate σ P α k hU.2.2⟩,hH⟩
  | @boundaryRequired c d m ℓ kind I φ Γ H A hcd _ hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      obtain ⟨_,hΓ⟩ := (withBoundaryGuard_nonPredicate σ P α k _ _ _).1 hU.2.2
      have hreset := (nonPredicate_unused_singleton_reset σ P α k d 0 Γ hdΓ).2 hΓ
      exact ⟨⟨⟨trivial,trivial⟩,hU.2.1,hreset⟩,hH⟩
  | @boundaryOptional c d m ℓ kind I φ Γ H A hcd _ hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      obtain ⟨_,hΓ⟩ := (withBoundaryGuard_nonPredicate σ P α k _ _ _).1 hU.2.2
      have hreset := (nonPredicate_unused_singleton_reset σ P α k d 0 Γ hdΓ).2 hΓ
      exact ⟨⟨trivial,hU.2.1,hreset⟩,hH⟩
  | unusedReset d v hdJ hdH D ih =>
      obtain ⟨hJ,hH⟩ := ih α hs
      exact ⟨(nonPredicate_unused_singleton_reset σ P α k d v _ hdJ).2 hJ,hH⟩
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
theorem Tree.numeric_occurrences_and_outputs [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Tree J H A) (σ : FiniteSignal Var)
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
  | merge hd he hj hg D ih =>
      exact ih α ⟨(fun hk => BoundaryInvariant.numeric_bounded_to_upper _ _ _ _ _ _ _ _ _
        (P.nonempty _) (hi.1.1 hk)), hg.numeric σ P α k hi.2⟩ hs
  | mergeOptional hd hj ho hg D ih =>
      exact ih α ⟨(fun hk => BoundaryInvariant.numeric_bounded_to_upper _ _ _ _ _ _ _ _ _
        (P.nonempty _) (hi.1 hk)), trivial, hg.numeric σ P α k hi.2.2⟩ hs
  | boundaryRequired hcd _ hdΓ D ih =>
      exact ih α (boundary_child_numeric σ P α k _ _ _ _ _ _ _ _
        hcd hdΓ hi.1.1 hi.2.2) hs
  | boundaryOptional hcd _ hdΓ D ih =>
      exact ih α (boundary_child_numeric σ P α k _ _ _ _ _ _ _ _
        hcd hdΓ hi.1 hi.2.2) hs
  | unusedReset d v hdJ hdH D ih =>
      exact ih α ((numeric_unused_singleton_reset σ P α k d v _ hdJ).1 hi) hs
/-- Numeric-only occurrence recovery, kept separate from its forward derivation. -/
theorem Tree.recover_of_numericOccurrences [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Tree J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
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
  | merge hd he hj hg D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      exact ⟨merge_recover hd he hj hg σ P α k hU,hH⟩
  | mergeOptional hd hj ho hg D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      exact ⟨merge_optional_recover hd hj hg σ P α k hU,hH⟩
  | boundaryRequired hcd _ hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      exact ⟨recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        hcd hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩,hH⟩
  | boundaryOptional hcd _ hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      have hraw := recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        hcd hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩
      exact ⟨⟨hraw.1.1,hraw.2⟩,hH⟩
  | unusedReset d v hdJ hdH D ih =>
      obtain ⟨hJ,hH⟩ := ih α hi hs
      exact ⟨(unused_singleton_reset σ P α k d v _ hdJ).2 hJ,hH⟩

/-- The local soundness conclusion uses only the INPUT numeric invariant.
All internal numeric obligations are derived by forward propagation from the
input and non-predicate leaves; no all-node assumption remains. -/
theorem Tree.recover_from_input_numeric [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (D : Tree J H A) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : Judgement.EvaluatedNumeric σ P α k J)
    (hs : Judgement.holds σ P α k A) :
    Judgement.holds σ P α k J ∧ Judgement.holds σ P α k H := by
  have hocc := (D.numeric_occurrences_and_outputs σ P α k hi
    (holds_implies_nonPredicate σ P α k hs)).1
  exact D.recover_of_numericOccurrences σ P α k hocc hs

private theorem atomicProjection_nonPredicate_iff (F : Section3.TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    F.atomicProjection.nonPredicateHolds σ P α k ↔ F.nonPredicateHolds σ P α k := by
  constructor
  · intro h
    refine ⟨⟨h.1.1, ?_⟩, h.2⟩
    intro l hl
    cases l with
    | terminal => exact h.1.2 .terminal ⟨hl,trivial⟩
    | marker m => exact h.1.2 (.marker m) ⟨hl,trivial⟩
    | predicate p => trivial
  · intro h
    exact ⟨⟨h.1.1, fun l hl => h.1.2 l hl.1⟩, h.2⟩

theorem member_localLaws [DecidableEq Clock] [Nontrivial Clock] :
    JudgementTableau.LocalLaws (Member (Clock := Clock) (Var := Var)) := by
  constructor
  · intro N F h σ P α k hs
    cases h with
    | original hc hr => exact (hc.extension.nonPredicateHolds σ P α k hs).1
    | completed D hJ hH hA =>
      have ha := (hA.nonPredicate σ P α k).1 ((atomicProjection_nonPredicate_iff F σ P α k).2 hs)
      exact ((hJ.nonPredicate σ P α k).2 (D.nonPredicate_recover σ P α k ha).1).1
  · intro N F h σ P α k hi hs
    have hin : (Section3.TransitionForm.ofState N).EvaluatedNumeric σ P α k :=
      ⟨hi,by intro M hm; cases hm⟩
    cases h with
    | original hc hr => exact ConcreteContextual.minimal_closure_numeric hc σ P α k hin hs
    | completed D hJ hH hA =>
      have ha := (hA.nonPredicate σ P α k).1 ((atomicProjection_nonPredicate_iff F σ P α k).2 hs)
      exact (hH.numeric σ P α k).2
        (D.numeric_occurrences_and_outputs σ P α k ((hJ.numeric σ P α k).1 hin) ha).2.1
  · intro N F h σ P α k hi hs
    have hin : (Section3.TransitionForm.ofState N).EvaluatedNumeric σ P α k :=
      ⟨hi,by intro M hm; cases hm⟩
    cases h with
    | original hc hr =>
      have hready := ConcreteContextual.closure_ready hc
        ((Section3.TransitionForm.ready_ofState N).2 hr)
      have hf := ConcreteContextual.minimal_closure_holds_of_atomicProjection hc
        (fun p hp => (hready.1 (.predicate p) hp).admitted) σ P α k hin hs
      exact ⟨hf,(hc.extension.sound σ P α k hf).1⟩
    | completed D hJ hH hA =>
      have hh := D.recover_from_input_numeric σ P α k ((hJ.numeric σ P α k).1 hin)
        ((hA.holds σ P α k).1 hs)
      exact ⟨(hH.holds σ P α k).2 hh.2, ((hJ.holds σ P α k).2 hh.1).1⟩

run_elab do
  for name in #[``opening_exists, ``member_localLaws] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "closure calculus: unexpected axiom {ax}"

end STLTableau.Section4.Finiteness.CompletedDerivation
