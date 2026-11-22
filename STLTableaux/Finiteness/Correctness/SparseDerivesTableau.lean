import STLTableaux.Finiteness.Inventory.Subgraph
import STLTableaux.Finiteness.Derivation.DerivationRelation

/-! Actual finite sparse restrictions of the revised derivation tableau.
Soundness is unconditional; no representative-path completeness is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var Slot : Type*} [DecidableEq Clock] [Fintype Slot]

noncomputable def sparseDerivesTableau
    (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (P : Finset (Formula Var)) (t : Slot→FiniteInventory.Triple Clock Var) :=
  Subgraph.restrict (JudgementTableau.tableau X Q
    (Section3.StateForm.ofLocal (.predicate (.plain root))) Derives)
    {F | FiniteInventory.TransitionWithin (FiniteInventory.locals P t)
      (FiniteInventory.guards t) (FiniteInventory.resets t) F}

theorem sparseDerivesTableau_states_finite
    (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (P : Finset (Formula Var)) (t : Slot→FiniteInventory.Triple Clock Var) :
    (sparseDerivesTableau X Q root P t).states.Finite :=
  Subgraph.sparse_restriction_states_finite _ P t

theorem sparseDerivesTableau_state_card_le
    (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (P : Finset (Formula Var)) (t : Slot→FiniteInventory.Triple Clock Var) :
    Nat.card ↥(sparseDerivesTableau X Q root P t).states≤
      2^(2*(P.card+3+64*Fintype.card Slot)+1) :=
  Subgraph.sparse_restriction_state_card_le _ P t

/-- Every recognized signal satisfies the actual root formula. -/
theorem sparseDerivesTableau_sound [Nontrivial Clock]
    (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (P : Finset (Formula Var)) (t : Slot→FiniteInventory.Triple Clock Var)
    (σ : FiniteSignal Var) (partition : IntervalPartition σ.domain)
    (hs : (sparseDerivesTableau X Q root P t).recognizes
      JudgementTableau.labels_finite σ partition) :
    σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  derives_formula_of_recognizes X Q root σ partition
    (Subgraph.recognizes_lift _ _ JudgementTableau.labels_finite σ partition hs)
end STLTableau.Section4.Finiteness
