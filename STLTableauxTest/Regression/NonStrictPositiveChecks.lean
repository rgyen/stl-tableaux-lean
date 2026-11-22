import STLTableaux.ModelChecking.Preprocessing.NonStrictPositive

namespace NonStrictPositiveChecks
open STLTableau

noncomputable def σ : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩
def positiveAtom : AtomicProposition Unit := ⟨1, fun _ => (), fun _ => 2, .gt⟩
def zeroAtom : AtomicProposition Unit := ⟨1, fun _ => (), fun _ => 0, .gt⟩
def negativeAtom : AtomicProposition Unit := ⟨1, fun _ => (), fun _ => -2, .ge⟩

def positiveComposite : Formula Unit := Formula.and
  (Formula.or (.atom positiveAtom) (.atom zeroAtom))
  (Formula.and (Formula.eventually (.unbounded 0) (.atom positiveAtom))
    (Formula.always (.unbounded 0) (.atom positiveAtom)))

theorem composite_ready : positiveComposite.NormalizedReady :=
  .and (.or (.atom _) (.atom _))
    (.and (.eventually _ (.atom _)) (.always _ (.atom _)))

theorem positive_atom_true (t : σ.Time) : σ.Satisfies (.atom positiveAtom) t := by
  change (2 : ℝ) > 0
  norm_num

theorem composite_true (t : σ.Time) : σ.Satisfies positiveComposite t := by
  refine ⟨(σ.satisfies_or _ _ _).2 (Or.inl (positive_atom_true t)), ?_, ?_⟩
  · apply (σ.satisfies_eventually_iff _ _ _).2
    exact ⟨t, by simp [TimeInterval.translate], positive_atom_true t⟩
  · apply (σ.satisfies_always_iff _ _ _).2
    exact fun u _ => positive_atom_true u

/-- The production positive-syntax lemma is consumed on and/or/F/G,
including a strict atom that is false at its boundary. -/
theorem composite_closed_true (t : σ.Time) :
    σ.Satisfies positiveComposite.closeNonStrictAtoms t :=
  composite_ready.satisfies_closeNonStrictAtoms σ t (composite_true t)

def negatedZero : Formula Unit := .neg (.atom zeroAtom)

theorem negated_strict_zero_breaks_closure (t : σ.Time) :
    σ.Satisfies negatedZero t ∧ ¬ σ.Satisfies negatedZero.closeNonStrictAtoms t := by
  constructor <;>
    norm_num [negatedZero, Formula.closeNonStrictAtoms, AtomicProposition.closeNonStrict,
      FiniteSignal.Satisfies, AtomicProposition.Holds, zeroAtom, RealRelation.Holds]

theorem unrestricted_source_to_closed_is_false :
    ¬ (∀ (φ : Formula Unit) (t : σ.Time),
      σ.Satisfies φ t → σ.Satisfies φ.closeNonStrictAtoms t) := by
  intro all
  let t : σ.Time := ⟨0, le_rfl, by norm_num [σ]⟩
  have boundary := negated_strict_zero_breaks_closure t
  exact boundary.2 (all negatedZero t boundary.1)

def numeric : Formula Unit := .neg (.atom negativeAtom)

theorem numeric_closed_strengthening (t : σ.Time) :
    σ.Satisfies (numeric.closeNonStrictAtoms.thresholdShift 1) t := by
  norm_num [numeric, Formula.closeNonStrictAtoms, Formula.thresholdShift,
    AtomicProposition.closeNonStrict, FiniteSignal.Satisfies,
    AtomicProposition.Holds, negativeAtom, RealRelation.Holds]

theorem numeric_strengthening_implies_original (t : σ.Time) :
    σ.Satisfies numeric t :=
  σ.satisfies_of_closed_strengthening numeric 1 (by norm_num) t
    (numeric_closed_strengthening t)

theorem numeric_margin (t : σ.Time) : (1 : EReal) < σ.Robustness numeric t := by
  change (1 : EReal) < -((-2 : ℝ) : EReal)
  norm_cast

theorem numeric_margin_implies_closed_strengthening (t : σ.Time) :
    σ.Satisfies (numeric.closeNonStrictAtoms.thresholdShift 1) t :=
  σ.satisfies_closed_strengthening_of_robustness_gt numeric 1 t (numeric_margin t)

run_elab do
  for name in #[``composite_ready, ``composite_true, ``composite_closed_true,
      ``negated_strict_zero_breaks_closure, ``unrestricted_source_to_closed_is_false,
      ``numeric_closed_strengthening, ``numeric_strengthening_implies_original,
      ``numeric_margin, ``numeric_margin_implies_closed_strengthening] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end NonStrictPositiveChecks
