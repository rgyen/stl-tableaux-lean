import STLTableaux.ModelChecking.Preprocessing.NormalizedViolation

namespace ModelCheckingNegationChecks
open STLTableau

def geAtom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def ltAtom : AtomicProposition Unit := { geAtom with relation := .lt }
def raw : Formula Unit := .atom ltAtom

theorem normalized_violation_is_ge :
    (Formula.neg raw).normalizeForTableau = .atom geAtom := rfl

theorem normalized_violation_admitted :
    (Formula.neg raw).normalizeForTableau.NormalizedReady := .atom geAtom

theorem exact_boolean_violation (σ : FiniteSignal Unit) (t : σ.Time) :
    σ.Satisfies (Formula.neg raw).normalizeForTableau t ↔ ¬ σ.Satisfies raw t :=
  Formula.satisfies_normalizeViolation raw σ t

def temporalRaw : Formula Unit := Formula.always (.unbounded 0) raw

theorem temporal_violation_is_eventually_ge :
    (Formula.neg temporalRaw).normalizeForTableau =
      Formula.eventually (.unbounded 0) (.atom geAtom) := rfl

theorem temporal_violation_admitted :
    (Formula.neg temporalRaw).normalizeForTableau.NormalizedReady :=
  Formula.NormalizedReady.eventually _ (.atom geAtom)

def compound : Formula Unit := Formula.and
  (Formula.untimedUntil
    (Formula.always (.unbounded 0) (.atom geAtom))
    (Formula.eventually (.unbounded 0) (.atom geAtom)))
  (Formula.release (.unbounded 0) (.atom geAtom) (.atom geAtom))

theorem compound_ready : compound.NormalizedReady :=
  .and (.until (.always _ (.atom geAtom)) (.eventually _ (.atom geAtom)))
    (.release (.atom geAtom) (.atom geAtom))

theorem compound_normalization_fixed : compound.normalizeForTableau = compound :=
  compound_ready.normalizeForTableau_eq

theorem compound_double_negation_exact :
    (Formula.neg (Formula.neg compound)).normalizeForTableau = compound :=
  compound_ready.normalize_double_neg_eq

/-- Truth's exact negation is not silently admitted as a normalized input. -/
theorem truth_violation_not_admitted :
    ¬ (Formula.neg (Formula.truth : Formula Unit)).normalizeForTableau.NormalizedReady := by
  change ¬ (Formula.falsity : Formula Unit).NormalizedReady
  exact Formula.not_normalizedReady_falsity

/-- Exact Boolean complementation does not replace a strict atom by a
non-strict robustness surrogate. -/
theorem ge_violation_is_strict :
    (Formula.neg (.atom geAtom)).normalizeForTableau = .atom ltAtom := rfl

theorem ge_violation_not_nonStrict :
    ¬ (∀ a, Formula.IsSubformula (.atom a)
      (Formula.neg (.atom geAtom)).normalizeForTableau → a.relation = .ge) := by
  intro h
  have impossible := h ltAtom (.refl _)
  cases impossible

run_elab do
  for name in #[``normalized_violation_is_ge, ``normalized_violation_admitted,
      ``exact_boolean_violation, ``truth_violation_not_admitted,
      ``temporal_violation_is_eventually_ge, ``temporal_violation_admitted,
      ``compound_ready, ``compound_normalization_fixed, ``compound_double_negation_exact,
      ``ge_violation_is_strict, ``ge_violation_not_nonStrict] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end ModelCheckingNegationChecks
