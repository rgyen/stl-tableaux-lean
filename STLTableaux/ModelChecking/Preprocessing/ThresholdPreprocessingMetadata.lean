import STLTableaux.Semantics.Robustness.RobustnessShift
import STLTableaux.ModelChecking.Preprocessing.Normalization

/-! Atom functions and comparisons after threshold shifts and temporal preprocessing. -/
namespace STLTableau.Formula
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
  | truth => constructor <;> intro h
             · intro a sub; cases sub
             · trivial
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

private theorem atomProperties_thresholdShift (P : AtomicProposition Var → Prop)
    (φ : Formula Var)
    (atoms : ∀ a, IsSubformula (.atom a) φ → ∀ ε : ℝ,
      P {a with function := fun v => a.function v - ε}) (ε : ℝ) :
    atomProperties P (φ.thresholdShift ε) := by
  induction φ generalizing ε with
  | truth => trivial
  | atom a => exact atoms a (.refl _) ε
  | neg φ ih => exact ih (fun a sub => atoms a (.neg sub)) (-ε)
  | and φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun a sub => atoms a (.and_left sub)) ε,
      ihψ (fun a sub => atoms a (.and_right sub)) ε⟩
  | «until» I φ ψ ihφ ihψ =>
    exact ⟨ihφ (fun a sub => atoms a (.until_left sub)) ε,
      ihψ (fun a sub => atoms a (.until_right sub)) ε⟩

theorem thresholdShift_atoms_ge (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (ε : ℝ) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (φ.thresholdShift ε)) : a.relation = .ge := by
  have all := atomProperties_thresholdShift (fun a => a.relation = .ge) φ
    (fun a ha _ => nonStrict a ha) ε
  exact (atomProperties_iff _ _).mp all a sub

theorem thresholdShift_functions_continuous (φ : Formula Var)
    (functions : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (ε : ℝ) (a : AtomicProposition Var)
    (sub : IsSubformula (.atom a) (φ.thresholdShift ε)) : Continuous a.function := by
  have all := atomProperties_thresholdShift (fun a => Continuous a.function) φ
    (fun a ha _ => (functions a ha).sub continuous_const) ε
  exact (atomProperties_iff _ _).mp all a sub

private theorem atomProperties_eliminateUntil (P : AtomicProposition Var → Prop)
    (I : TimeInterval) (φ ψ : Formula Var)
    (left : atomProperties P φ) (right : atomProperties P ψ) :
    atomProperties P (eliminateUntil I φ ψ) := by
  cases I with
  | bounded I =>
    simp only [eliminateUntil]
    split
    · exact ⟨⟨trivial, right⟩, trivial, left, right⟩
    · exact ⟨⟨trivial, right⟩, left, right⟩
  | unbounded a =>
    simp only [eliminateUntil]
    split
    · exact ⟨⟨trivial, trivial⟩, trivial, left, right⟩
    · exact ⟨left, right⟩

private theorem atomProperties_eliminateTimedUntil (P : AtomicProposition Var → Prop)
    (φ : Formula Var) (all : atomProperties P φ) :
    atomProperties P φ.eliminateTimedUntil := by
  induction φ with
  | truth => trivial
  | atom a => exact all
  | neg φ ih => exact ih all
  | and φ ψ ihφ ihψ => exact ⟨ihφ all.1, ihψ all.2⟩
  | «until» I φ ψ ihφ ihψ =>
    have left := ihφ all.1
    have right := ihψ all.2
    cases φ <;> first
      | exact ⟨trivial, right⟩
      | exact atomProperties_eliminateUntil P I _ _ left right

theorem eliminateTimedUntil_atoms_ge (φ : Formula Var)
    (nonStrict : ∀ a, IsSubformula (.atom a) φ → a.relation = .ge)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) φ.eliminateTimedUntil) :
    a.relation = .ge := by
  exact (atomProperties_iff _ _).mp
    (atomProperties_eliminateTimedUntil (fun a => a.relation = .ge) φ
      ((atomProperties_iff _ _).mpr nonStrict)) a sub

theorem eliminateTimedUntil_functions_continuous (φ : Formula Var)
    (functions : ∀ a, IsSubformula (.atom a) φ → Continuous a.function)
    (a : AtomicProposition Var) (sub : IsSubformula (.atom a) φ.eliminateTimedUntil) :
    Continuous a.function := by
  exact (atomProperties_iff _ _).mp
    (atomProperties_eliminateTimedUntil (fun a => Continuous a.function) φ
      ((atomProperties_iff _ _).mpr functions)) a sub

/-- Timed-until elimination introduces no new atomic propositions. -/
theorem eliminateTimedUntil_atom_subformula {φ : Formula Var} {a : AtomicProposition Var}
    (sub : IsSubformula (.atom a) φ.eliminateTimedUntil) : IsSubformula (.atom a) φ :=
  (atomProperties_iff _ _).mp
    (atomProperties_eliminateTimedUntil (fun b => IsSubformula (.atom b) φ) φ
      ((atomProperties_iff _ _).mpr (fun _ h => h))) a sub

run_elab do
  for name in #[``thresholdShift_atoms_ge, ``thresholdShift_functions_continuous,
      ``eliminateTimedUntil_atoms_ge, ``eliminateTimedUntil_functions_continuous,
      ``eliminateTimedUntil_atom_subformula] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Formula
