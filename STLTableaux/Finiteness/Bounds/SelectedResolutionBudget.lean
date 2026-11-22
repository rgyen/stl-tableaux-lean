import STLTableaux.Finiteness.Bounds.SelectedRootBudget
import STLTableaux.Finiteness.Bounds.ResolutionClockBudget

/-! Bounds the number of tracked truth intervals in terms of formula resolution.
For bounded timing the count uses `2 ⌊sup I / (sup I − inf I)⌋ + 7`. For
unbounded timing it uses one. Used in the proof of Lemma 4.36. -/
namespace STLTableau.Section4.Finiteness
open scoped BigOperators
variable {Var : Type*}

/-- Counts constructor occurrences in the formula syntax, with truth and atoms of size one. -/
def literalFormulaSize : Formula Var → ℕ
  | .truth | .atom _ => 1
  | .neg φ => literalFormulaSize φ+1
  | .and φ ψ | .until _ φ ψ => literalFormulaSize φ+literalFormulaSize ψ+1

theorem root_inventory_card_le_literal_size (root : Formula Var) :
    (Finiteness.rootPlainFormulas root).card≤literalFormulaSize root := by
  classical
  induction root with
  | truth | atom => simp [Finiteness.rootPlainFormulas,literalFormulaSize]
  | neg φ ih =>
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
  | and φ ψ ih ik =>
    have hc := Finset.card_union_le (Finiteness.rootPlainFormulas φ) (Finiteness.rootPlainFormulas ψ)
    have hi := Finset.card_insert_le (.and φ ψ) (Finiteness.rootPlainFormulas φ∪Finiteness.rootPlainFormulas ψ)
    change (insert (.and φ ψ) (Finiteness.rootPlainFormulas φ∪Finiteness.rootPlainFormulas ψ)).card≤literalFormulaSize φ+literalFormulaSize ψ+1
    omega
  | «until» I φ ψ ih ik =>
    have hc := Finset.card_union_le (Finiteness.rootPlainFormulas φ) (Finiteness.rootPlainFormulas ψ)
    have hi := Finset.card_insert_le (.until I φ ψ) (Finiteness.rootPlainFormulas φ∪Finiteness.rootPlainFormulas ψ)
    change (insert (.until I φ ψ) (Finiteness.rootPlainFormulas φ∪Finiteness.rootPlainFormulas ψ)).card≤literalFormulaSize φ+literalFormulaSize ψ+1
    omega

theorem temporal_origin_cap_le_nine_resolution (I : TimeInterval) :
    temporalOriginCap I≤9*Finiteness.intervalResolution I := by
  have hp := Finiteness.interval_resolution_pos I
  cases I with
  | unbounded a => simp [temporalOriginCap,Finiteness.intervalResolution]
  | bounded I =>
    have hf := Nat.floor_le_ceil (I.upper/(I.upper-I.lower))
    simp only [temporalOriginCap,Finiteness.intervalResolution] at *
    omega

theorem root_origin_budget_le_nine_inventory_resolution (root : Formula Var) :
    rootOriginBudget root≤9*(Finiteness.rootPlainFormulas root).card*Finiteness.formulaResolution root := by
  classical
  have hs : rootOriginBudget root≤
      (Finiteness.rootTemporalSignatures root).card*(9*Finiteness.formulaResolution root) := by
    unfold rootOriginBudget
    calc
      _ ≤ ∑ _s ∈ Finiteness.rootTemporalSignatures root, 9*Finiteness.formulaResolution root := by
        apply Finset.sum_le_sum
        intro s hs
        exact (temporal_origin_cap_le_nine_resolution s.2.1).trans
          (Nat.mul_le_mul_left 9 (Finiteness.signature_resolution_le root s hs))
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ (Finiteness.rootPlainFormulas root).card*(9*Finiteness.formulaResolution root) :=
      hs.trans (Nat.mul_le_mul_right _ (Finiteness.root_temporal_signatures_card_le_plain root))
    _ = _ := by ring

theorem root_step_budget_le_eleven_inventory_resolution (root : Formula Var) :
    rootStepBudget root≤11*(Finiteness.rootPlainFormulas root).card*Finiteness.formulaResolution root := by
  have hb := root_origin_budget_le_nine_inventory_resolution root
  have hp := Finiteness.formula_resolution_pos root
  have hn := Nat.mul_le_mul_left (2*(Finiteness.rootPlainFormulas root).card) hp
  unfold rootStepBudget
  nlinarith

theorem root_origin_budget_le_nine_size_resolution (root : Formula Var) :
    rootOriginBudget root≤9*literalFormulaSize root*Finiteness.formulaResolution root :=
  (root_origin_budget_le_nine_inventory_resolution root).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 9 (root_inventory_card_le_literal_size root)))

theorem root_step_budget_le_eleven_size_resolution (root : Formula Var) :
    rootStepBudget root≤11*literalFormulaSize root*Finiteness.formulaResolution root :=
  (root_step_budget_le_eleven_inventory_resolution root).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (root_inventory_card_le_literal_size root)))

end STLTableau.Section4.Finiteness
