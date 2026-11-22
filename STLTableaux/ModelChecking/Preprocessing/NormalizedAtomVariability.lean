import STLTableaux.ModelChecking.Preprocessing.NormalizedInput
import STLTableaux.ModelChecking.Preprocessing.ThresholdPreprocessingMetadata

/-! A partition stable for the input is stable for the non-strict atoms of
its normalized violation. The disequality branch splits into strict atoms,
so it does not need a stability claim about either of its disjuncts. -/

namespace STLTableau

namespace Formula

variable {Var : Type*}

private def atomProperties (P : AtomicProposition Var → Prop) : Formula Var → Prop
  | .truth => True
  | .atom a => P a
  | .neg φ => atomProperties P φ
  | .and φ ψ => atomProperties P φ ∧ atomProperties P ψ
  | .until _ φ ψ => atomProperties P φ ∧ atomProperties P ψ

private theorem atomProperties_iff (P : AtomicProposition Var → Prop) (φ : Formula Var) :
    atomProperties P φ ↔ ∀ a, IsSubformula (.atom a) φ → P a := by
  induction φ with
  | truth => constructor
             · intro _ a sub; cases sub
             · intro _; trivial
  | atom b =>
    constructor
    · intro h a sub; cases sub; exact h
    · intro h; exact h b (.refl _)
  | neg φ ih =>
    constructor
    · intro h a sub; cases sub with | neg sub => exact ih.mp h a sub
    · intro h; exact ih.mpr (fun a sub => h a (.neg sub))
  | and φ ψ ihφ ihψ =>
    constructor
    · intro h a sub
      cases sub with
      | and_left sub => exact ihφ.mp h.1 a sub
      | and_right sub => exact ihψ.mp h.2 a sub
    · intro h
      exact ⟨ihφ.mpr (fun a sub => h a (.and_left sub)),
        ihψ.mpr (fun a sub => h a (.and_right sub))⟩
  | «until» I φ ψ ihφ ihψ =>
    constructor
    · intro h a sub
      cases sub with
      | until_left sub => exact ihφ.mp h.1 a sub
      | until_right sub => exact ihψ.mp h.2 a sub
    · intro h
      exact ⟨ihφ.mpr (fun a sub => h a (.until_left sub)),
        ihψ.mpr (fun a sub => h a (.until_right sub))⟩

private theorem atomProperties_normalizeMixedNegation
    (P Q : AtomicProposition Var → Prop) (φ : Formula Var)
    (direct : ∀ a, P a → Q a)
    (complement : ∀ a, P a → atomProperties Q a.complementFormula)
    (all : atomProperties P φ) (negative : Bool) :
    atomProperties Q (φ.normalizeMixedNegation negative) := by
  induction φ generalizing negative with
  | truth => cases negative <;> trivial
  | atom a => cases negative
              · exact direct a all
              · exact complement a all
  | neg φ ih => exact ih all (!negative)
  | and φ ψ ihφ ihψ => cases negative <;> exact ⟨ihφ all.1 _, ihψ all.2 _⟩
  | «until» I φ ψ ihφ ihψ =>
    have left := ihφ all.1
    have right := ihψ all.2
    cases negative
    · exact ⟨left false, right false⟩
    · cases φ <;> exact ⟨left true, right true⟩

end Formula

namespace FiniteSignal

variable {Var : Type*}

theorem StablePartition.normalizeViolation_atom {σ : FiniteSignal Var} {φ : Formula Var}
    {P : IntervalPartition σ.domain} (stable : σ.StablePartition φ P)
    {a : AtomicProposition Var}
    (sub : Formula.IsSubformula (.atom a) (Formula.neg φ).normalizeForTableau)
    (nonStrict : a.relation = .ge) : σ.StablePartition (.atom a) P := by
  intro i b bsub
  cases bsub
  let A : AtomicProposition Var → Prop := fun b => σ.Stable (P.interval i) (.atom b)
  let B : AtomicProposition Var → Prop := fun b => b.relation = .ge → A b
  have original : Formula.atomProperties A (Formula.neg φ).eliminateTimedUntil :=
    (Formula.atomProperties_iff _ _).mpr (by
      intro b sub
      have sub := Formula.eliminateTimedUntil_atom_subformula sub
      cases sub with | neg h => exact stable i (.atom b) h)
  have complement (b : AtomicProposition Var) (h : A b) :
      Formula.atomProperties B b.complementFormula := by
    cases rel : b.relation <;>
      simp only [AtomicProposition.complementFormula, rel, Formula.or, Formula.atomProperties, B]
    case lt =>
      intro _ u v hu hv
      have equiv (t : σ.Time) :
          σ.Satisfies (.atom { b with relation := .ge }) t ↔ ¬ σ.Satisfies (.atom b) t := by
        simpa only [AtomicProposition.complementFormula, rel, satisfies_atom] using
          AtomicProposition.satisfies_complementFormula b σ t
      exact (equiv u).trans ((h u v hu hv).not.trans (equiv v).symm)
    case eq => constructor <;> (intro bad; cases bad)
    all_goals intro bad; cases bad
  have normalized := Formula.atomProperties_normalizeMixedNegation A B _
    (fun _ h _ => h) complement original false
  exact (Formula.atomProperties_iff _ _).mp normalized a sub nonStrict

theorem HasFiniteVariability.normalizeViolation_atom {σ : FiniteSignal Var} {φ : Formula Var}
    (fv : σ.HasFiniteVariability φ) {a : AtomicProposition Var}
    (sub : Formula.IsSubformula (.atom a) (Formula.neg φ).normalizeForTableau)
    (nonStrict : a.relation = .ge) : σ.HasFiniteVariability (.atom a) := by
  obtain ⟨P, stable⟩ := fv
  exact ⟨P, stable.normalizeViolation_atom sub nonStrict⟩

run_elab do
  for name in #[``StablePartition.normalizeViolation_atom,
      ``HasFiniteVariability.normalizeViolation_atom] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end FiniteSignal
end STLTableau
