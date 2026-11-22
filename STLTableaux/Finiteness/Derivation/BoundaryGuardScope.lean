import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Finiteness.Derivation.ResetScopeMerge
import STLTableaux.Finiteness.Inventory.LocalResetSupport

/-! The actual defer/check reasons that a boundary guard is not captured by an
inherited reset. Defer leaves c unreset; check uses the same two markers and
adds no strict guard. No claim that all generated reset values are zero is made.
The wrappers do not establish branch/path provenance of an arbitrary inherited
map; their stated map decomposition and absence premises remain explicit. -/
namespace STLTableau.Section4.Finiteness.BoundaryGuardScope
open Section3
variable {Clock Var : Type*}

/-- Any literal copy whose reset domain is a subset preserves clock absence. -/
theorem absent_of_subset (R S : ClockResetSet Clock) (c : Clock)
    (hsub : S.clocks ⊆ R.clocks) (hc : c ∉ R.clocks) : c ∉ S.clocks :=
  fun hs => hc (hsub hs)

theorem absent_restrict (R : ClockResetSet Clock) (A : Set Clock) (c : Clock)
    (hc : c ∉ R.clocks) : c ∉ (Finiteness.LocalResetSupport.restrictResets R A).clocks := by
  rw [Finiteness.LocalResetSupport.restrictResets_clocks]
  exact fun h => hc h.1

theorem absent_union (R S : ClockResetSet Clock) (c : Clock)
    (hR : c ∉ R.clocks) (hS : c ∉ S.clocks) : c ∉ (R.union S).clocks := by
  rw [ClockResetSet.clocks_union]
  exact fun h => h.elim hR hS

theorem absent_singleton_union [DecidableEq Clock] (S : ClockResetSet Clock)
    (c d : Clock) (v : NNReal) (hcd : c ≠ d) (hS : c ∉ S.clocks) :
    c ∉ ((ClockResetSet.singleton d v).union S).clocks :=
  absent_union _ S c (by simpa only [ClockResetSet.clocks_singleton,Set.mem_singleton_iff] using hcd) hS

theorem absent_union_singleton [DecidableEq Clock] (S : ClockResetSet Clock)
    (c d : Clock) (v : NNReal) (hcd : c ≠ d) (hS : c ∉ S.clocks) :
    c ∉ (S.union (ClockResetSet.singleton d v)).clocks :=
  absent_union S _ c hS (by simpa only [ClockResetSet.clocks_singleton,Set.mem_singleton_iff] using hcd)

/-- The actual defer map changes d but cannot change the guarded left c. -/
theorem defer_guard_absent [DecidableEq Clock] (S : ClockResetSet Clock)
    (c d : Clock) (hcd : c ≠ d) (hS : c ∉ S.clocks) :
    c ∉ ((ClockResetSet.singleton d 0).union S).clocks :=
  absent_singleton_union S c d 0 hcd hS

@[simp] theorem check_imp_self (ℓ : Marker) : Marker.imp ℓ ℓ = Marker.closed := by cases ℓ <;> rfl

/-- Check uses m=ℓ, so it adds no guard, even if the left clock was reset to a>0. -/
@[simp] theorem check_guard_eq (c : Clock) (ℓ : Marker) (Γ : MixedJ Clock Var) :
    withBoundaryGuard c (Marker.imp ℓ ℓ) Γ = Γ := by
  rw [check_imp_self]
  rfl

/-- Exact normal form of withBoundaryGuard: the strict case adds a current
unary guard before the existing reset scope of F. -/
def boundaryNormal (c : Clock) (b : Marker) (F : Section3.TransitionForm Clock Var) :
    Section3.TransitionForm Clock Var :=
  match b with
  | .closed => F
  | .open => (Section3.TransitionForm.ofState (Section3.StateForm.ofGuard ⟨c,.gt,0⟩)).union F

private theorem pure_guard_compatible (c : Clock) (F : Section3.TransitionForm Clock Var) :
    (Section3.TransitionForm.ofState (Section3.StateForm.ofGuard ⟨c,.gt,0⟩)).UnionCompatible F := by
  apply Section3.TransitionForm.unionCompatible_of_captureFree
  · intro x a b ha
    cases ha
  · simp [Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,
      Section3.TransitionForm.bodyFreeClocks,Section3.StateForm.localClocks]
  · apply Set.disjoint_left.2
    rintro x ⟨v,hv⟩ _
    cases hv
  · intro N M hn; cases hn
  · intro N M hn; cases hn
  · intro N M hn; cases hn

theorem safe_boundary_guard {Γ : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization Γ F) (c : Clock) (b : Marker) :
    SafeNormalization (withBoundaryGuard c b Γ) (boundaryNormal c b F) := by
  cases b with
  | closed => exact h
  | «open» => exact .conj (.clock c .gt 0) h (pure_guard_compatible c F)

/-- Precise scope condition: only the open marker needs the new clock absent
from R; already existing current guards have their own explicit support test. -/
theorem safe_boundary_guard_under_reset
    {Γ : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization Γ F) (R : ClockResetSet Clock) (c : Clock) (b : Marker)
    (hd : Disjoint R.clocks F.current.guardClocks)
    (hc : b = Marker.open → c ∉ R.clocks) :
    SafeNormalization (.reset R (withBoundaryGuard c b Γ)) ((boundaryNormal c b F).underReset R) := by
  apply SafeNormalization.reset R (safe_boundary_guard h c b)
  cases b with
  | closed => exact hd
  | «open» =>
    apply Set.disjoint_left.2
    intro x hx hguard
    obtain ⟨g,hg,hgx⟩ := hguard
    change g ∈ ({⟨c,.gt,0⟩} : Set (Guard Clock)) ∪ F.current.guards at hg
    rcases hg with hg | hg
    · have he : g = ⟨c,.gt,0⟩ := hg
      subst g
      have hcx : c = x := hgx
      exact hc rfl (hcx.symm ▸ hx)
    · exact Set.disjoint_left.1 hd hx ⟨g,hg,hgx⟩

/-- Actual defer conditions discharge the strict-clock noncapture premise;
the exact inside-reset raw syntax is retained in the certificate. -/
theorem safe_defer_guard_under_reset [DecidableEq Clock]
    {Γ : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization Γ F) (S : ClockResetSet Clock) (c d : Clock)
    (m ℓ : Marker) (hcd : c ≠ d) (hS : c ∉ S.clocks)
    (hd : Disjoint ((ClockResetSet.singleton d 0).union S).clocks F.current.guardClocks) :
    SafeNormalization (.reset ((ClockResetSet.singleton d 0).union S)
      (withBoundaryGuard c (Marker.imp ℓ m) Γ))
      ((boundaryNormal c (Marker.imp ℓ m) F).underReset ((ClockResetSet.singleton d 0).union S)) :=
  safe_boundary_guard_under_reset h _ c _ hd (fun _ => defer_guard_absent S c d hcd hS)

/-- Check adds no new guard, so no condition excludes c from R. R may record
its actual c:=lowerEndpoint assignment, including a positive value. -/
theorem safe_check_guard_under_reset
    {Γ : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization Γ F) (R : ClockResetSet Clock) (c : Clock) (ℓ : Marker)
    (hd : Disjoint R.clocks F.current.guardClocks) :
    SafeNormalization (.reset R (withBoundaryGuard c (Marker.imp ℓ ℓ) Γ)) (F.underReset R) := by
  rw [check_guard_eq]
  exact .reset R h hd

/-- Exact structural extraction when the strict guard is unreset. The closed
case is identity, and does not demand any clock-freshness condition. -/
theorem extract_boundary_guard (R : ClockResetSet Clock) (c : Clock) (b : Marker)
    (Γ : MixedJ Clock Var) (hc : b = Marker.open → c ∉ R.clocks) :
    StructuralEq (.reset R (withBoundaryGuard c b Γ)) (withBoundaryGuard c b (.reset R Γ)) := by
  cases b with
  | closed => exact .refl _
  | «open» => exact extract_unreset_guard R c .gt 0 Γ (hc rfl)

end STLTableau.Section4.Finiteness.BoundaryGuardScope
