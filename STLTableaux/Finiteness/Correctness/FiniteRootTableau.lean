import STLTableaux.Finiteness.Inventory.RootSlotPalette
import STLTableaux.Finiteness.Correctness.SparseDerivesTableau
import STLTableaux.Finiteness.Inventory.ClockSupport

/-! Finiteness and recognition soundness for the restriction of the
derivation tableau to the fixed clock set of the root formula. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- The root formula fixes the permitted subformulas, clock names, and slots. -/
noncomputable def finiteRootTableau (X : Set Var) (root : Formula Var) :=
  sparseDerivesTableau X ((FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root)) : Set Clock)
    root (Finiteness.rootPlainFormulas root) (rootSlotTriples root)

theorem finiteRootTableau_states_finite (X : Set Var) (root : Formula Var) :
    (finiteRootTableau (Clock := Clock) X root).states.Finite :=
  sparseDerivesTableau_states_finite X _ root _ _

theorem finiteRootTableau_state_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(finiteRootTableau (Clock := Clock) X root).states ≤
      2^(5634*literalFormulaSize root*Finiteness.formulaResolution root+7) := by
  have hc := sparseDerivesTableau_state_card_le X
    ((FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root)) : Set Clock) root
    (Finiteness.rootPlainFormulas root) (rootSlotTriples (Clock := Clock) root)
  exact hc.trans (Nat.pow_le_pow_right (by omega) (rootSlot_sparse_exponent_le_resolution root))

theorem finiteRootTableau_clocks_finite (X : Set Var) (root : Formula Var) :
    (finiteRootTableau (Clock := Clock) X root).clocks.Finite := Finset.finite_toSet _

theorem finiteRootTableau_clock_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(finiteRootTableau (Clock := Clock) X root).clocks ≤
      132*literalFormulaSize root*Finiteness.formulaResolution root := by
  change Nat.card ↥((FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root) : Finset Clock) : Set Clock) ≤ _
  rw [Nat.card_coe_set_eq,Set.ncard_coe_finset]
  exact rootSlot_clocks_card_le_resolution root

/-- Every clock occurring in a retained transition form belongs to the
tableau's fixed clock set. -/
theorem finiteRootTableau_state_clock_support
    (X : Set Var) (root : Formula Var) (F : Section3.TransitionForm Clock Var)
    (hF : F∈(finiteRootTableau (Clock := Clock) X root).states) :
    F.allClocks ⊆ (finiteRootTableau (Clock := Clock) X root).clocks :=
  FiniteInventory.transition_allClocks_subset (Finiteness.rootPlainFormulas root)
    (rootSlotTriples (Clock := Clock) root) hF.2

theorem finiteRootTableau_state_clock_card_le
    (X : Set Var) (root : Formula Var) (F : Section3.TransitionForm Clock Var)
    (hF : F∈(finiteRootTableau (Clock := Clock) X root).states) :
    F.allClocks_finite.toFinset.card ≤
      132*literalFormulaSize root*Finiteness.formulaResolution root := by
  have hc := FiniteInventory.transition_allClocks_card_le (Finiteness.rootPlainFormulas root)
    (rootSlotTriples (Clock := Clock) root) hF.2
  have hs := rootSlot_card_le_size_resolution root
  nlinarith

/-- Recognition by the finite restriction implies satisfaction of the root
formula at time zero. -/
theorem finiteRootTableau_sound
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (hs : (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P) :
    σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  sparseDerivesTableau_sound X _ root _ _ σ P hs
end STLTableau.Section4.Finiteness
