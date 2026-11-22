import STLTableaux.Finiteness.Bounds.RootTemporalBudgetCore
import STLTableaux.Finiteness.Inventory.RootFormulaInventory

/-! Bounds the number of label clocks using formula resolution and the number
of syntactic subformulas. Used in the proof of Theorem 4.37. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Var : Type*}

noncomputable def intervalResolution : TimeInterval → ℕ
  | .bounded I => ⌈I.upper / (I.upper - I.lower)⌉₊
  | .unbounded _ => 1

noncomputable def formulaResolution : Formula Var → ℕ
  | .truth | .atom _ => 1
  | .neg φ => formulaResolution φ
  | .and φ ψ => max (formulaResolution φ) (formulaResolution ψ)
  | .until I φ ψ => max (max (formulaResolution φ) (formulaResolution ψ)) (intervalResolution I)

theorem formula_resolution_pos (φ : Formula Var) : 1 ≤ formulaResolution φ := by
  induction φ with
  | truth | atom => exact le_rfl
  | neg φ ih => exact ih
  | and φ ψ ih _ => exact ih.trans (le_max_left _ _)
  | «until» I φ ψ ih _ => exact ih.trans ((le_max_left _ _).trans (le_max_left _ _))

theorem subformula_resolution_le {φ root : Formula Var} (h : φ ≼ root) :
    formulaResolution φ ≤ formulaResolution root := by
  induction h with
  | refl => exact le_rfl
  | neg _ ih => exact ih
  | and_left _ ih => exact ih.trans (le_max_left _ _)
  | and_right _ ih => exact ih.trans (le_max_right _ _)
  | until_left _ ih => exact ih.trans ((le_max_left _ _).trans (le_max_left _ _))
  | until_right _ ih => exact ih.trans ((le_max_right _ _).trans (le_max_left _ _))

theorem signature_resolution_le (root : Formula Var)
    (s : TemporalKind × TimeInterval × Formula Var) (hs : s ∈ rootTemporalSignatures root) :
    intervalResolution s.2.1 ≤ formulaResolution root := by
  have hsub := (mem_rootTemporalSignatures_iff root s.1 s.2.1 s.2.2).mp hs
  apply le_trans _ (subformula_resolution_le hsub)
  rcases s with ⟨kind,I,φ⟩
  cases kind <;> exact le_max_right _ _

theorem root_clock_budget_le_signatures_resolution (root : Formula Var) :
    rootLocalClockBudget root ≤
      (rootTemporalSignatures root).card * (2 * formulaResolution root + 5) := by
  classical
  unfold rootLocalClockBudget
  calc
    _ ≤ ∑ _s ∈ rootTemporalSignatures root, (2 * formulaResolution root + 5) := by
      apply Finset.sum_le_sum
      intro s hs
      have hr := signature_resolution_le root s hs
      rcases s with ⟨kind,I,φ⟩
      cases kind <;> cases I <;> simp only [boundedTemporalCap,intervalResolution] at hr ⊢ <;> omega
    _ = _ := by simp [Nat.mul_comm]

theorem root_temporal_signatures_card_le_plain (root : Formula Var) :
    (rootTemporalSignatures root).card ≤ (rootPlainFormulas root).card := by
  classical
  let f : TemporalKind × TimeInterval × Formula Var → Formula Var :=
    fun s => temporalSignatureFormula s.1 s.2.1 s.2.2
  have hf : Function.Injective f := by
    rintro ⟨k,I,φ⟩ ⟨l,J,ψ⟩ h
    cases k <;> cases l <;>
      simp only [f,temporalSignatureFormula,Formula.eventually,Formula.always,
        Formula.neg.injEq,Formula.until.injEq,reduceCtorEq,true_and] at h
    all_goals rcases h with ⟨rfl,rfl⟩; rfl
  have hsub : (rootTemporalSignatures root).image f ⊆ rootPlainFormulas root := by
    intro φ hφ
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hφ
    exact subformula_mem_rootPlainFormulas
      ((mem_rootTemporalSignatures_iff root s.1 s.2.1 s.2.2).mp hs)
  rw [← Finset.card_image_of_injective _ hf]
  exact Finset.card_le_card hsub

theorem root_clock_budget_le_formula_inventory (root : Formula Var) :
    rootLocalClockBudget root ≤
      (rootPlainFormulas root).card * (2 * formulaResolution root + 5) :=
  (root_clock_budget_le_signatures_resolution root).trans
    (Nat.mul_le_mul_right _ (root_temporal_signatures_card_le_plain root))

theorem interval_resolution_pos (I : TimeInterval) : 1 ≤ intervalResolution I := by
  cases I with
  | unbounded => exact le_rfl
  | bounded I =>
    apply Nat.one_le_ceil_iff.mpr
    exact div_pos (lt_of_le_of_lt I.lower_nonnegative I.nonSingular)
      (sub_pos.mpr I.nonSingular)

/-- Linear resolution bound, including untimed formulas with resolution one. -/
theorem root_clock_budget_le_seven_size_resolution (root : Formula Var) :
    rootLocalClockBudget root ≤ 7 * (rootPlainFormulas root).card * formulaResolution root := by
  classical
  have hsum : rootLocalClockBudget root ≤
      (rootTemporalSignatures root).card * (7 * formulaResolution root) := by
    unfold rootLocalClockBudget
    calc
      _ ≤ ∑ _s ∈ rootTemporalSignatures root, (7 * formulaResolution root) := by
        apply Finset.sum_le_sum
        intro s hs
        have hr := signature_resolution_le root s hs
        have hpos := (interval_resolution_pos s.2.1).trans hr
        rcases s with ⟨kind,I,φ⟩
        cases kind <;> cases I <;>
          simp only [boundedTemporalCap,intervalResolution] at hr ⊢ <;> omega
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ (rootTemporalSignatures root).card * (7 * formulaResolution root) := hsum
    _ ≤ (rootPlainFormulas root).card * (7 * formulaResolution root) :=
      Nat.mul_le_mul_right _ (root_temporal_signatures_card_le_plain root)
    _ = _ := by ring

end STLTableau.Section4.Finiteness
