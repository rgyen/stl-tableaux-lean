/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Derivation.SimplifiedClosure
import STLTableaux.Finiteness.Derivation.ResolveFreeSupport
import STLTableaux.Closure.Support.ClosureFreeSupport

/-! Free clock support for the C(M) constructors. -/
namespace STLTableau.Section4.Finiteness.CompletedDerivation

open Section3 ResetTrimming
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem MergeGuard.free_subset {R : ClockResetSet Clock} {c : Clock}
    {b : Marker} {Γ K : MixedJ Clock Var} (h : MergeGuard R c b Γ K) :
    K.freeClocks ⊆ {c} ∪ Γ.freeClocks := by
  cases h with
  | closed | fixed => exact Set.subset_union_right
  | free => simp [withBoundaryGuard, Section3.Judgement.freeClocks]

omit [DecidableEq Clock] in
private theorem merge_free {R : ClockResetSet Clock} {c d e : Clock}
    {m b ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {Γ K : MixedJ Clock Var} (hg : MergeGuard R c (Marker.imp ℓ m) Γ K) :
    (.reset R (.conj (.predicate (.upper c m kind I φ)) K) : MixedJ Clock Var).freeClocks ⊆
    (.reset R (.conj (.conj (.predicate (.bounded c d m b kind I φ))
      (.predicate (.upper e ℓ kind I φ))) Γ) : MixedJ Clock Var).freeClocks := by
  rintro x ⟨hx, hn⟩
  have hx' : x ∈ ({c} : Set Clock) ∪ Γ.freeClocks := by
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact hg.free_subset hx
  refine ⟨?_, hn⟩
  rcases hx' with hx' | hx'
  · exact Or.inl (Or.inl (Or.inl hx'))
  · exact Or.inr hx'

private theorem boundary_free {c d : Clock} {m ℓ : Marker} {kind : TemporalKind}
    {I : TimeInterval} {φ : Formula Var} {Γ : MixedJ Clock Var}
    (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks) :
    (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ)) : MixedJ Clock Var).freeClocks ⊆
    (.reset (ClockResetSet.singleton d 0) (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.conj (.marker ℓ) Γ)) : MixedJ Clock Var).freeClocks := by
  cases hb : Marker.imp ℓ m <;>
    simp [withBoundaryGuard, Section3.Judgement.freeClocks, ClockResetSet.clocks_singleton,
      Set.subset_def] <;> aesop

omit [DecidableEq Clock] in
private theorem merge_optional_free {R : ClockResetSet Clock} {c d : Clock}
    {m b ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {Γ K : MixedJ Clock Var} (hg : MergeGuard R c (Marker.imp ℓ m) Γ K) :
    (.reset R (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) K)) : MixedJ Clock Var).freeClocks ⊆
    (.reset R (.conj (.predicate (.bounded c d m b kind I φ))
      (.conj (.marker ℓ) Γ)) : MixedJ Clock Var).freeClocks := by
  rintro x ⟨hx, hn⟩
  have hx' : x ∈ ({c} : Set Clock) ∪ Γ.freeClocks := by
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · cases hx
    · exact hg.free_subset hx
  refine ⟨?_, hn⟩
  rcases hx' with hx' | hx'
  · exact Or.inl (Or.inl hx')
  · exact Or.inr (Or.inr hx')

/-- Neither the retained output nor its erased leaves introduce a free clock. -/
theorem Tree.freeClocks_outputs {J H A : MixedJ Clock Var} (D : Tree J H A) :
    H.freeClocks ⊆ J.freeClocks ∧ A.freeClocks ⊆ J.freeClocks := by
  induction D with
  | leaf => exact ⟨Set.Subset.refl _, Set.Subset.refl _⟩
  | conj D E ih ig => exact ⟨Set.union_subset_union ih.1 ig.1, Set.union_subset_union ih.2 ig.2⟩
  | reset R D ih =>
    exact ⟨fun _ hc => ⟨ih.1 hc.1, hc.2⟩, fun _ hc => ⟨ih.2 hc.1, hc.2⟩⟩
  | structural h D ih => rw [h.freeClocks_eq]; exact ih
  | @expandCtx p B Γ H A raw hp fresh D ih =>
    have hs := Set.union_subset_union raw.freeClocks_subset (Set.Subset.refl Γ.freeClocks)
    exact ⟨Set.union_subset Set.subset_union_left (ih.1.trans hs), ih.2.trans hs⟩
  | expandSolo raw hp fresh D ih =>
    exact ⟨Set.union_subset (Set.Subset.refl _) (ih.1.trans raw.freeClocks_subset),
      ih.2.trans raw.freeClocks_subset⟩
  | merge hd he hj hg D ih =>
    exact ⟨ih.1.trans (merge_free hg), ih.2.trans (merge_free hg)⟩
  | mergeOptional hd hj ho hg D ih =>
    exact ⟨ih.1.trans (merge_optional_free hg), ih.2.trans (merge_optional_free hg)⟩
  | @boundaryRequired c d m ℓ kind I φ Γ H A hcd _ hdΓ D ih =>
    have hs := boundary_free (m := m) (ℓ := ℓ) (kind := kind) (I := I) (φ := φ) hcd hdΓ
    have hfull := ih.1.trans hs
    have hat := ih.2.trans hs
    simpa only [Section3.Judgement.freeClocks, Set.union_empty] using And.intro hfull hat
  | boundaryOptional hcd _ hdΓ D ih =>
    exact ⟨ih.1.trans (boundary_free hcd hdΓ), ih.2.trans (boundary_free hcd hdΓ)⟩
  | unusedReset d v hdJ hdH D ih =>
    refine ⟨fun c hc => ⟨ih.1 hc, ?_⟩, fun c hc => ⟨ih.2 hc, ?_⟩⟩
    · intro h
      rw [ClockResetSet.clocks_singleton, Set.mem_singleton_iff] at h
      exact hdJ (h ▸ ih.1 hc)
    · intro h
      rw [ClockResetSet.clocks_singleton, Set.mem_singleton_iff] at h
      exact hdJ (h ▸ ih.2 hc)

theorem Tree.free_subset {J H A : MixedJ Clock Var} (D : Tree J H A) :
    H.freeClocks ⊆ J.freeClocks := D.freeClocks_outputs.1

/-- A full C(M) output cannot read any fresh free name. -/
theorem Member.free_subset {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var}
    (h : Member N F) : F.freeClocks ⊆ N.freeClocks := by
  have hs : F.freeClocks ⊆ (Section3.TransitionForm.ofState N).freeClocks := by
    cases h with
    | original hc _ => exact ConcreteContextual.closure_freeClocks_subset hc
    | completed D hJ hH _ => rw [hH.freeClocks_eq, hJ.freeClocks_eq]; exact D.free_subset
  simpa only [Section3.TransitionForm.ofState, Section3.TransitionForm.freeClocks,
    Section3.TransitionForm.bodyFreeClocks, Set.union_empty, Section3.StateForm.freeClocks] using hs

/-- Replaying and trimming unused resets preserves the same free-clock bound. -/
theorem Admitted.free_subset {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : Admitted N F) :
    F.freeClocks ⊆ N.freeClocks := by
  cases h with
  | original hc hr => exact (Member.original hc hr).free_subset
  | replayed he hm ht =>
    rw [← ht]
    have hfree := congrArg Section3.StateForm.freeClocks he
    simp only [trimState_freeClocks] at hfree
    simpa only [trim_freeClocks, hfree] using hm.free_subset

end STLTableau.Section4.Finiteness.CompletedDerivation
