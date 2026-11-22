import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Normalized tableau inputs use true, atomic propositions, conjunction,
disjunction, untimed until and release, and timed eventually and always.
Derived operators use the encodings of Section 2. -/
namespace STLTableau.Formula
variable {Var : Type*}

inductive NormalizedReady : Formula Var → Prop
  | truth : NormalizedReady .truth
  | atom (a : AtomicProposition Var) : NormalizedReady (.atom a)
  | and {φ ψ} : NormalizedReady φ → NormalizedReady ψ → NormalizedReady (.and φ ψ)
  | or {φ ψ} : NormalizedReady φ → NormalizedReady ψ → NormalizedReady (Formula.or φ ψ)
  | until {φ ψ} : NormalizedReady φ → NormalizedReady ψ → NormalizedReady (untimedUntil φ ψ)
  | release {φ ψ} : NormalizedReady φ → NormalizedReady ψ →
      NormalizedReady (Formula.release (.unbounded 0) φ ψ)
  | eventually (I : TimeInterval) {φ} : NormalizedReady φ → NormalizedReady (eventually I φ)
  | always (I : TimeInterval) {φ} : NormalizedReady φ → NormalizedReady (always I φ)

theorem NormalizedReady.mixedReady {φ : Formula Var} (h : φ.NormalizedReady) : φ.MixedReady := by
  induction h with
  | truth => exact .truth
  | atom a => exact .atom a
  | and _ _ ih ig => exact .and ih ig
  | or _ _ ih ig => exact .or ih ig
  | «until» _ _ ih ig => exact .until ih ig
  | release _ _ ih ig => exact .release ih ig
  | eventually I _ ih => exact .eventually I ih
  | always I _ ih => exact .always I ih

@[simp] theorem not_normalizedReady_falsity : ¬ (falsity : Formula Var).NormalizedReady := by
  intro h
  cases h

/-- Being ready for the broader internal calculus does not certify normalized input. -/
theorem mixedReady_not_sufficient_for_normalizedReady :
    ¬ (∀ φ : Formula Var, φ.MixedReady → φ.NormalizedReady) :=
  fun h => not_normalizedReady_falsity (h _ .falsity)

/-- An STL formula in the normalized input grammar. -/
abbrev NormalizedInput (Var : Type*) := {φ : Formula Var // φ.NormalizedReady}

@[simp] theorem normalizedReady_and {φ ψ : Formula Var} :
    (Formula.and φ ψ).NormalizedReady ↔ φ.NormalizedReady ∧ ψ.NormalizedReady := by
  constructor
  · intro h; cases h; exact ⟨by assumption, by assumption⟩
  · exact fun h => .and h.1 h.2

@[simp] theorem normalizedReady_or {φ ψ : Formula Var} :
    (Formula.or φ ψ).NormalizedReady ↔ φ.NormalizedReady ∧ ψ.NormalizedReady := by
  constructor
  · intro h; cases h; exact ⟨by assumption, by assumption⟩
  · exact fun h => .or h.1 h.2

@[simp] theorem normalizedReady_until {φ ψ : Formula Var} :
    (untimedUntil φ ψ).NormalizedReady ↔ φ.NormalizedReady ∧ ψ.NormalizedReady := by
  constructor
  · intro h; cases h
    · exact ⟨by assumption, by assumption⟩
    · exact ⟨.truth, by assumption⟩
  · exact fun h => .until h.1 h.2

@[simp] theorem normalizedReady_release {φ ψ : Formula Var} :
    (Formula.release (.unbounded 0) φ ψ).NormalizedReady ↔
      φ.NormalizedReady ∧ ψ.NormalizedReady := by
  constructor
  · intro h; cases h; exact ⟨by assumption, by assumption⟩
  · exact fun h => .release h.1 h.2

@[simp] theorem normalizedReady_eventually {I : TimeInterval} {φ : Formula Var} :
    (eventually I φ).NormalizedReady ↔ φ.NormalizedReady := by
  constructor
  · intro h; cases h <;> assumption
  · exact .eventually I

@[simp] theorem normalizedReady_always {I : TimeInterval} {φ : Formula Var} :
    (always I φ).NormalizedReady ↔ φ.NormalizedReady := by
  constructor
  · intro h; cases h; assumption
  · exact .always I

end STLTableau.Formula
