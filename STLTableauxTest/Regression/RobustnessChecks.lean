import STLTableaux.ModelChecking.Preprocessing.NonStrictAtoms
import STLTableaux.Semantics.Robustness.RobustnessShift

namespace RobustnessChecks
open STLTableau
open scoped STL

noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩
def t0 : σ.Time := ⟨0, le_rfl, by norm_num [σ]⟩
def ge : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def gt : AtomicProposition Unit := {ge with relation := .gt}

theorem truth_top : σ.Robustness .truth t0 = ⊤ := rfl
theorem falsity_bot : σ.Robustness Formula.falsity t0 = ⊥ := rfl

theorem ge_boundary : σ.Satisfies (.atom ge) t0 ∧
    σ.Robustness (.atom ge) t0 = 0 := ⟨le_rfl, rfl⟩
theorem gt_boundary : ¬ σ.Satisfies (.atom gt) t0 ∧
    σ.Robustness (.atom gt) t0 = 0 := by
  constructor
  · exact lt_irrefl _
  · rfl

theorem closure_changes_boolean_not_robustness :
    σ.Satisfies (Formula.atom gt).closeNonStrictAtoms t0 ∧
      ¬ σ.Satisfies (.atom gt) t0 ∧
      σ.Robustness (Formula.atom gt).closeNonStrictAtoms t0 =
        σ.Robustness (.atom gt) t0 :=
  ⟨le_rfl, gt_boundary.1, σ.robustness_closeNonStrictAtoms _ _⟩

theorem strengthening_negative_one :
    σ.Robustness ((Formula.atom ge)⁺[(1 : ℝ)]) t0 = (-1 : EReal) := by
  change (((0 : ℝ) - 1 : ℝ) : EReal) = -1
  norm_num
theorem weakening_positive_one :
    σ.Robustness ((Formula.atom ge)⁻[(1 : ℝ)]) t0 = (1 : EReal) := by
  change (((0 : ℝ) - -1 : ℝ) : EReal) = 1
  norm_num
theorem negation_polarity :
    (Formula.neg (.atom ge))⁺[(1 : ℝ)] =
      Formula.neg ((Formula.atom ge)⁻[(1 : ℝ)]) := rfl
theorem negation_strengthening_margin :
    σ.Robustness ((Formula.neg (.atom ge))⁺[(1 : ℝ)]) t0 = (-1 : EReal) := by
  change -(((0 : ℝ) - -1 : ℝ) : EReal) = -1
  norm_num

theorem shifted_infinities :
    σ.Robustness ((Formula.truth : Formula Unit)⁺[(3 : ℝ)]) t0 = ⊤ ∧
      σ.Robustness ((Formula.falsity : Formula Unit)⁻[(3 : ℝ)]) t0 = ⊥ :=
  ⟨rfl, rfl⟩

def absent : Formula Unit := Formula.eventually (.unbounded 2) .truth
theorem absent_witness_bot (t : σ.Time) : σ.Robustness absent t = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro u
  apply iSup_le
  intro inside
  have lower : (2 : ℝ) ≤ u.val - t.val := inside
  have upper : u.val < 1 := u.property.2
  exact (by linarith [t.property.1] : False).elim

theorem absent_shift_bot : σ.Robustness (absent⁺[(5 : ℝ)]) t0 = ⊥ := by
  have noAtoms : ∀ a, Formula.IsSubformula (.atom a) absent → a.relation = .ge := by
    intro a sub
    cases sub with
    | until_left h => cases h
    | until_right h => cases h
  rw [σ.robustness_thresholdShift absent noAtoms, absent_witness_bot]
  simp

theorem inclusive_until_zero :
    σ.Robustness (.until (.unbounded 0) (.atom ge) .truth) t0 = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro u
    apply iSup_le
    intro inside
    apply (min_le_right _ _).trans
    exact iInf_le_of_le t0 (iInf_le_of_le le_rfl
      (iInf_le_of_le (TimeInterval.le_of_mem_translate inside) le_rfl))
  · apply σ.robustness_nonneg_of_satisfies
    exact ⟨t0, by change (0 : ℝ) ≤ 0 - 0; norm_num,
      trivial, fun _ _ _ => le_rfl⟩

/-- Inclusive until tests its left operand at the witness itself, even
when the delay is zero. Nonnegative robustness alone is not satisfaction. -/
theorem inclusive_strict_until_false :
    ¬ σ.Satisfies (.until (.unbounded 0) (.atom gt) .truth) t0 := by
  rintro ⟨u, inside, _, left⟩
  have impossible := left t0 le_rfl (TimeInterval.le_of_mem_translate inside)
  exact (lt_irrefl (0 : ℝ)) impossible

theorem actual_positive_bridge :
    σ.Satisfies ((Formula.atom ge)⁻[(1 : ℝ)]) t0 := by
  apply σ.satisfies_of_robustness_pos
  rw [weakening_positive_one]
  exact EReal.coe_pos.mpr (by norm_num)

run_elab do
  for name in #[``truth_top, ``falsity_bot, ``ge_boundary, ``gt_boundary,
      ``closure_changes_boolean_not_robustness, ``strengthening_negative_one,
      ``weakening_positive_one, ``negation_polarity, ``negation_strengthening_margin,
      ``shifted_infinities, ``absent_witness_bot, ``absent_shift_bot,
      ``inclusive_until_zero, ``inclusive_strict_until_false, ``actual_positive_bridge] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end RobustnessChecks
