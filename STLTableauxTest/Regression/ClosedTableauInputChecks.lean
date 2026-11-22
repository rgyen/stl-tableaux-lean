import STLTableaux.ModelChecking.Preprocessing.ClosedTableauInput

namespace ClosedTableauInputChecks
open STLTableau

noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩
def zeroAtom : AtomicProposition Unit := ⟨0, Fin.elim0, fun _ => 0, .ge⟩
def zeroTime : σ.Time := ⟨0, le_rfl, by norm_num [σ]⟩

private theorem closed_of_normalized_ready (φ : Formula Unit)
    (ready : φ.normalizeForTableau.NormalizedReady) :
    (Formula.closedTableauInput φ).val = φ.normalizeForTableau.closeNonStrictAtoms := by
  change (Formula.eliminateFalsity φ.normalizeForTableau _).val.closeNonStrictAtoms = _
  rw [Formula.eliminateFalsity_eq_of_normalizedReady _ _ ready]

theorem input_atom_elimination_fixed :
    (Formula.eliminateFalsity (Formula.atom zeroAtom).normalizeForTableau
      (Formula.mixedReady_normalizeForTableau _)).val = .atom zeroAtom :=
  Formula.eliminateFalsity_eq_of_normalizedReady _ _ (.atom zeroAtom)

def truthBranch : Formula Unit := Formula.or .truth Formula.falsity

theorem truth_branch_closed_satisfies :
    σ.Satisfies (Formula.closedTableauInput truthBranch).val zeroTime := by
  apply Formula.satisfies_closedTableauInput_of_satisfies
  exact (σ.satisfies_or _ _ _).2 (Or.inl trivial)

private theorem false_elimination :
    (Formula.eliminateFalsity (Formula.falsity : Formula Unit) .falsity).val =
      .atom Formula.falseAtom := by
  generalize output :
    (Formula.eliminateFalsity (Formula.falsity : Formula Unit) .falsity).val = ψ
  have h := Formula.eliminateFalsity_spec (Formula.falsity : Formula Unit) .falsity
  rw [output] at h
  cases h
  rfl

theorem closed_falsity_not_satisfies :
    ¬ σ.Satisfies (Formula.closedTableauInput (Formula.falsity : Formula Unit)).val
      zeroTime := by
  change ¬ σ.Satisfies
    ((Formula.eliminateFalsity (Formula.falsity : Formula Unit) _).val.closeNonStrictAtoms) _
  rw [false_elimination]
  change ¬ ((-1 : ℝ) ≥ 0)
  norm_num

/-- At zero the exact raw negation is false, but its actual closed input
is true. This is deliberate one-way closure, not Boolean equivalence. -/
theorem closed_negated_boundary :
    ¬ σ.Satisfies (.neg (.atom zeroAtom)) zeroTime ∧
      σ.Satisfies (Formula.closedTableauInput (.neg (.atom zeroAtom))).val zeroTime := by
  constructor
  · change ¬ ¬ ((0 : ℝ) ≥ 0)
    norm_num
  · rw [closed_of_normalized_ready (.neg (.atom zeroAtom))
      (.atom {zeroAtom with relation := .lt})]
    change -(0 : ℝ) ≥ 0
    norm_num

theorem actual_input_metadata :
    (Formula.closedTableauInput (.atom zeroAtom)).val.NormalizedReady ∧
      (∀ a, Formula.IsSubformula (.atom a)
        (Formula.closedTableauInput (.atom zeroAtom)).val → a.relation = .ge) ∧
      (∀ a, Formula.IsSubformula (.atom a)
        (Formula.closedTableauInput (.atom zeroAtom)).val → Continuous a.function) := by
  refine ⟨(Formula.closedTableauInput _).property,
    Formula.closedTableauInput_atoms_ge _, ?_⟩
  apply Formula.closedTableauInput_functions_continuous
  · intro a sub; cases sub; rfl
  · intro a sub; cases sub; exact continuous_const

theorem boundary_robustness_upper :
    σ.Robustness (.atom zeroAtom) zeroTime ≤ (0 : EReal) :=
  Formula.robustness_le_of_satisfies_robustCounterInput (.atom zeroAtom) 0
    (by intro a sub; cases sub; rfl) σ zeroTime (by
      change σ.Satisfies
        (Formula.closedTableauInput (.neg ((Formula.atom zeroAtom).thresholdShift 0))).val zeroTime
      have ready : Formula.NormalizedReady
          ((Formula.neg ((Formula.atom zeroAtom).thresholdShift 0)).normalizeForTableau) :=
        .atom _
      rw [closed_of_normalized_ready _ ready]
      change -((0 : ℝ) - 0) ≥ 0
      norm_num)

theorem boundary_robustness_equality :
    σ.Robustness (.atom zeroAtom) zeroTime = (0 : EReal) := rfl

def lateBounded : TimeInterval := .bounded ⟨2, 3, by norm_num, by norm_num⟩
def boundedUntil : Formula Unit := .until lateBounded (.atom zeroAtom) (.atom zeroAtom)
def unboundedUntil : Formula Unit := .until (.unbounded 2) (.atom zeroAtom) (.atom zeroAtom)

private theorem until_atoms_ge (I : TimeInterval) :
    ∀ a, Formula.IsSubformula (.atom a) (.until I (.atom zeroAtom) (.atom zeroAtom)) →
      a.relation = .ge := by
  intro a sub
  cases sub with
  | until_left h => cases h; rfl
  | until_right h => cases h; rfl

theorem bounded_until_normalization_exact :
    σ.Robustness boundedUntil.normalizeForTableau zeroTime =
      σ.Robustness boundedUntil zeroTime :=
  σ.robustness_normalizeForTableau boundedUntil (until_atoms_ge _) zeroTime

theorem unbounded_until_elimination_exact :
    σ.Robustness unboundedUntil.eliminateTimedUntil zeroTime =
      σ.Robustness unboundedUntil zeroTime :=
  σ.robustness_eliminateTimedUntil unboundedUntil (until_atoms_ge _) zeroTime

private theorem no_late_time (u : σ.Time) : ¬ (2 : ℝ) ≤ u.val := by
  have upper : u.val < 1 := u.property.2
  linarith

theorem bounded_empty_robustness : σ.Robustness boundedUntil zeroTime = ⊥ := by
  apply iSup_eq_bot.mpr
  intro u
  apply iSup_eq_bot.mpr
  intro inside
  have lower : (2 : ℝ) ≤ u.val := by simpa [zeroTime] using inside.1
  exact (no_late_time u lower).elim

theorem unbounded_empty_robustness : σ.Robustness unboundedUntil zeroTime = ⊥ := by
  apply iSup_eq_bot.mpr
  intro u
  apply iSup_eq_bot.mpr
  intro inside
  have lower : (2 : ℝ) ≤ u.val := by
    simpa [TimeInterval.translate, zeroTime] using inside
  exact (no_late_time u lower).elim

theorem empty_until_shift_stays_bottom :
    σ.Robustness (unboundedUntil.thresholdShift 7) zeroTime = ⊥ := by
  rw [σ.robustness_thresholdShift unboundedUntil (until_atoms_ge _) 7 zeroTime,
    unbounded_empty_robustness]
  simp

theorem empty_always_robustness :
    σ.Robustness (Formula.always (.unbounded 2) (.atom zeroAtom)) zeroTime = ⊤ := by
  rw [σ.robustness_always]
  apply eq_top_iff.mpr
  apply le_iInf
  intro u
  apply le_iInf
  intro inside
  have lower : (2 : ℝ) ≤ u.val := by
    simpa [TimeInterval.translate, zeroTime] using inside
  exact (no_late_time u lower).elim

theorem truth_shift_stays_top :
    σ.Robustness (Formula.truth.thresholdShift (-7)) zeroTime = ⊤ := by
  rw [σ.robustness_thresholdShift .truth (by intro a sub; cases sub) (-7) zeroTime]
  simp [FiniteSignal.Robustness]

theorem empty_always_shift_stays_top :
    σ.Robustness
      ((Formula.always (.unbounded 2) (.atom zeroAtom)).thresholdShift 7) zeroTime = ⊤ := by
  have nonStrict : ∀ a, Formula.IsSubformula (.atom a)
      (Formula.always (.unbounded 2) (.atom zeroAtom)) → a.relation = .ge := by
    intro a sub
    cases sub with
    | neg hs => cases hs with
      | until_left hs => cases hs
      | until_right hs => cases hs with
        | neg hs => cases hs; rfl
  rw [σ.robustness_thresholdShift _ nonStrict 7 zeroTime, empty_always_robustness]
  simp

run_elab do
  for name in #[``input_atom_elimination_fixed, ``truth_branch_closed_satisfies,
      ``closed_falsity_not_satisfies, ``closed_negated_boundary, ``actual_input_metadata,
      ``boundary_robustness_upper, ``boundary_robustness_equality,
      ``bounded_until_normalization_exact, ``unbounded_until_elimination_exact,
      ``bounded_empty_robustness, ``unbounded_empty_robustness,
      ``empty_until_shift_stays_bottom, ``empty_always_robustness, ``truth_shift_stays_top,
      ``empty_always_shift_stays_top] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end ClosedTableauInputChecks
