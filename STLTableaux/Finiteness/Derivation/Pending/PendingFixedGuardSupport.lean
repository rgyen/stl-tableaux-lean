import STLTableaux.Finiteness.Derivation.Pending.PendingStep
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCurrentShape

/-! Preservation of a fixed allowed guard-clock set. It may meet active source
support; no protectedActive hypothesis is imposed on this fixed set. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Actual branch canonical reset provenance removes all source names from its
support, leaving only the selected fresh name. -/
theorem canonical_reset_subset_fresh
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (Rb : ClockResetSet Clock)
    (x : Clock)
    (hsource : Disjoint Rb.clocks (syntaxClocks (.predicate p)))
    (hreset : Rb.clocks ⊆ resetNames B)
    (hB : syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x}) :
    Rb.clocks ⊆ {x} := by
  intro c hc
  rcases hB (reset_subset_syntax B (hreset hc)) with hs | hx
  · exact False.elim (Set.disjoint_left.1 hsource hc hs)
  · exact hx

/-- The actual ordinary child reset avoids every fixed U inside the old finite
history that the inherited map already avoids. U need not avoid active sources. -/
theorem ordinary_child_reset_avoids_fixed_set
    {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (R Rb : ClockResetSet Clock) (remaining : List (Local Clock Var))
    (W U : Set Clock) (x : Clock) (hx : x ∉ W) (hU : U ⊆ W)
    (hR : Disjoint R.clocks U)
    (hsource : Disjoint Rb.clocks (syntaxClocks (.predicate p)))
    (hreset : Rb.clocks ⊆ resetNames B)
    (hB : syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x}) :
    Disjoint (Rb.union (copyActiveResets R remaining)).clocks U := by
  have hRb : Disjoint Rb.clocks U := by
    apply Set.disjoint_left.2
    intro c hc hcU
    have he : c = x := canonical_reset_subset_fresh Rb x hsource hreset hB hc
    subst c
    exact hx (hU hcU)
  rw [ClockResetSet.clocks_union]
  apply hRb.union_left
  rw [copyActiveResets_clocks]
  exact hR.mono_left Set.inter_subset_left

/-- Every current predicate in the `↑↓` form in the assembled child
comes from the unexpanded part of the input. -/
theorem RawBranch.bounded_current_iff_residual [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hB : RawBranch p B)
    (Γ : MixedJ Clock Var) (S : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Predicate.bounded c d m ℓ kind I φ ∈
      (Section3.Judgement.conj B (.reset S Γ)).currentPredicates ↔
    Predicate.bounded c d m ℓ kind I φ ∈ Γ.currentPredicates := by
  change (_ ∈ B.currentPredicates ∨ _ ∈ Γ.currentPredicates) ↔ _
  exact or_iff_right (hB.no_current_bounded c d m ℓ kind I φ)

/-- The same origin fact for a singleton child with no residual context. -/
theorem RawBranch.no_bounded_current_under_reset [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hB : RawBranch p B)
    (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Predicate.bounded c d m ℓ kind I φ ∉ (Section3.Judgement.reset R B).currentPredicates :=
  hB.no_current_bounded c d m ℓ kind I φ

end STLTableau.Section4.Finiteness
