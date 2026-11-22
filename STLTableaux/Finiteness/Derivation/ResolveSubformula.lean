import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport
import STLTableaux.Finiteness.Derivation.BoundaryReplacementSemantics
import STLTableaux.Tableau.Stability.GeneratorStability
import STLTableaux.Finiteness.Inventory.ClosureFormulaConfinement
import STLTableaux.Finiteness.Inventory.Subgraph
import STLTableaux.Closure.Normalization.FaithfulAlphaStability

/-! Full current/next formula confinement of actual resolution and Derives.
No truth, path provenance or representative-bound assumption is required. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Every formula in an actual raw branch is a subformula of its actual source,
including formulas in literal future payloads. -/
theorem RawBranch.subformula {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) {ψ : Formula Var} (hψ : ψ ∈ B.underlyingFormulas) : ψ ≼ p.formula := by
  cases h with
  | finite hr hm =>
    simpa only [Predicate.formula_ofFinite] using GeneratorStability.finite_branch_subformula hr hm hψ
  | infinite hr hm =>
    simpa only [Predicate.formula_ofUnbounded] using GeneratorStability.infinite_branch_subformula hr hm hψ
  | opening c m kind a φ =>
    exact GeneratorStability.opening_branch_subformula c m kind a φ hψ

/-- Actual resolution preserves the subformula closure of its entire raw input
in BOTH full and erased outputs. The input's future part is included. -/
theorem Resolve.subformula_confinement {J H A : MixedJ Clock Var} (D : Resolve J H A)
    (φ : Formula Var) (h : ∀ ψ ∈ J.underlyingFormulas, ψ ≼ φ) :
    (∀ ψ ∈ H.underlyingFormulas, ψ ≼ φ) ∧ (∀ ψ ∈ A.underlyingFormulas, ψ ≼ φ) := by
  induction D with
  | leaf => exact ⟨h,h⟩
  | conj D E ih ik =>
    obtain ⟨hH,hA⟩ := ih (fun ψ hψ => h ψ (Or.inl hψ))
    obtain ⟨hG,hB⟩ := ik (fun ψ hψ => h ψ (Or.inr hψ))
    exact ⟨fun ψ hψ => hψ.elim (hH ψ) (hG ψ),fun ψ hψ => hψ.elim (hA ψ) (hB ψ)⟩
  | reset R D ih => exact ih h
  | structural he D ih =>
    rw [he.underlyingFormulas_eq] at h
    exact ih h
  | @expandCtx p B Γ H A raw hn fresh D ih =>
    have hp : p.formula ≼ φ := h _ (Or.inl rfl)
    have hc : ∀ ψ ∈ (.conj B Γ : MixedJ Clock Var).underlyingFormulas, ψ ≼ φ := by
      intro ψ hψ
      rcases hψ with hB | hΓ
      · exact (raw.subformula hB).trans hp
      · exact h ψ (Or.inr hΓ)
    obtain ⟨hH,hA⟩ := ih hc
    exact ⟨fun ψ hψ => hψ.elim (fun he => he ▸ hp) (hH ψ),hA⟩
  | @expandSolo p B H A raw hn fresh D ih =>
    have hp : p.formula ≼ φ := h _ rfl
    obtain ⟨hH,hA⟩ := ih (fun ψ hψ => (raw.subformula hψ).trans hp)
    exact ⟨fun ψ hψ => hψ.elim (fun he => he ▸ hp) (hH ψ),hA⟩
  | @boundaryRequired c d m ell kind I ψ Γ H A frozen hd D ih =>
    have he := boundaryReplacement_underlyingFormulas true c d m ell kind I ψ Γ
    have hc : ∀ χ ∈ (boundaryReplacementChild c m ell kind I ψ Γ).underlyingFormulas, χ ≼ φ := by
      intro χ hχ
      apply h χ
      rw [← he] at hχ
      exact hχ
    exact ih hc
  | @boundaryOptional c d m ell kind I ψ Γ H A frozen hd D ih =>
    have he := boundaryReplacement_underlyingFormulas false c d m ell kind I ψ Γ
    have hc : ∀ χ ∈ (boundaryReplacementChild c m ell kind I ψ Γ).underlyingFormulas, χ ≼ φ := by
      intro χ hχ
      apply h χ
      rw [← he] at hχ
      exact hχ
    exact ih hc
  | unusedReset d v hd hH D ih => exact ih h
omit [DecidableEq Clock] in
private theorem formulas_below_iff (φ : Formula Var) (F : Section3.TransitionForm Clock Var) :
    Finiteness.FormFormulasBelow φ F ↔ ∀ ψ ∈ F.underlyingFormulas, ψ ≼ φ := by
  constructor
  · intro h ψ hψ
    rcases hψ with ⟨p,hp,rfl⟩ | hψ
    · exact h.1 (.predicate p) hp
    · cases hn : F.nextPart with
      | none => rw [hn] at hψ; cases hψ
      | some M =>
        rw [hn] at hψ
        obtain ⟨p,hp,rfl⟩ := hψ
        exact h.2 M hn (.predicate p) hp
  · intro h
    constructor
    · intro l hl
      cases l with
      | terminal | marker => trivial
      | predicate p => exact h p.formula (Or.inl ⟨p,hl,rfl⟩)
    · intro M hn l hl
      cases l with
      | terminal | marker => trivial
      | predicate p =>
        apply h p.formula
        right
        simpa only [hn] using (show p.formula ∈ M.underlyingFormulas from ⟨p,hl,rfl⟩)

/-- Raw resolution confines the formulas of its normalized full result. -/
theorem Resolve.normalized_formulas_below {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (hJ : SafeNormalization J (.ofState N))
    (hH : SafeNormalization H F) (φ : Formula Var)
    (hN : Finiteness.StateFormulasBelow φ N) :
    Finiteness.FormFormulasBelow φ F := by
  have hInput : ∀ ψ ∈ J.underlyingFormulas, ψ ≼ φ := by
    intro ψ hψ
    rw [← Section3.TransitionForm.normalize_underlyingFormulas J hJ.normalizes] at hψ
    rw [Section3.TransitionForm.underlyingFormulas_ofState] at hψ
    obtain ⟨p,hp,rfl⟩ := hψ
    exact hN (.predicate p) hp
  apply (formulas_below_iff φ F).2
  intro ψ hψ
  rw [Section3.TransitionForm.normalize_underlyingFormulas H hH.normalizes] at hψ
  exact (D.subformula_confinement φ hInput).1 ψ hψ

/-- Every actual Derives output remains in the subformula envelope of its
actual input, both in the complete current labels and in the next state. -/
theorem Derives.formulas_below {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (D : Derives N F) (φ : Formula Var) (hN : Finiteness.StateFormulasBelow φ N) :
    Finiteness.FormFormulasBelow φ F := by
  cases D with
  | original hc hr => exact Finiteness.closure_formulas_below φ hc hN
  | resolved D hJ hH _ => exact D.normalized_formulas_below hJ hH φ hN

theorem Derives.current_formula_below {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (D : Derives N F) (φ : Formula Var) (hN : Finiteness.StateFormulasBelow φ N)
    (p : Predicate Clock Var) (hp : Local.predicate p ∈ F.current.locals) : p.formula ≼ φ :=
  (D.formulas_below φ hN).1 (.predicate p) hp

theorem Derives.next_formula_below {N M : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (D : Derives N F) (φ : Formula Var) (hN : Finiteness.StateFormulasBelow φ N)
    (hn : F.nextPart = some M) (p : Predicate Clock Var) (hp : Local.predicate p ∈ M.locals) : p.formula ≼ φ :=
  (D.formulas_below φ hN).2 M hn (.predicate p) hp

/-- Every actual run from a confined root has confined FULL current and next
labels at every state, independently of recognition or satisfaction. -/
theorem Derives.run_formulas_below
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var) (φ : Formula Var)
    (hroot : Finiteness.StateFormulasBelow φ root)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q root Derives)) :
    Subgraph.AllStates {F | Finiteness.FormFormulasBelow φ F} p := by
  have go : ∀ q : Path Clock (Section3.TransitionForm Clock Var),
      q.valid (JudgementTableau.tableau X Q root Derives) →
      Finiteness.FormFormulasBelow φ q.firstState →
      Subgraph.AllStates {F | Finiteness.FormFormulasBelow φ F} q := by
    intro q
    induction q with
    | last e F => intro hv hf; exact hf
    | step e F tail ih =>
      intro hv hf
      obtain ⟨N,hn,hD,hIncoming⟩ := hv.2.2.2.2
      exact ⟨hf,ih hv.2.1 (hD.formulas_below φ (hf.2 N hn))⟩
  exact go p hr.1 (hr.2.1.formulas_below φ hroot)
end STLTableau.Section4.Finiteness
