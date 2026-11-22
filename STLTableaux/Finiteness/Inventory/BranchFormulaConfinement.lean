import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue
import STLTableaux.Closure.Normalization.FaithfulAlphaStability

/-! Actual branch formulas are syntactic subformulas of the source formula,
including predicates below next/reset and scoped alpha representatives. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem underReset_underlyingFormulas (F : Section3.TransitionForm Clock Var)
    (Λ : ClockResetSet Clock) :
    (F.underReset Λ).underlyingFormulas = F.underlyingFormulas := rfl

private theorem mixed_branch_underlying_subformula
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var} (hb : ConcreteMixed.catalogue.Branch p Λ B)
    {ψ : Formula Var} (hψ : ψ ∈ B.underlyingFormulas) : ψ ≼ p.formula := by
  rcases hb with hf | hi | ho
  · obtain ⟨p₀,R,Ψ,F,rfl,hr,hΨ,hF,rfl⟩ := hf
    rw [underReset_underlyingFormulas,
      Section3.TransitionForm.normalize_underlyingFormulas _ hF] at hψ
    simpa only [Predicate.formula_ofFinite] using
      GeneratorStability.finite_branch_subformula hr hΨ hψ
  · obtain ⟨p₀,Bs,Ψ,F,rfl,hr,hΨ,hF,rfl⟩ := hi
    rw [underReset_underlyingFormulas,
      Section3.TransitionForm.normalize_underlyingFormulas _ hF] at hψ
    simpa only [Predicate.formula_ofUnbounded] using
      GeneratorStability.infinite_branch_subformula hr hΨ hψ
  · obtain ⟨c,m,kind,a,φ,F,rfl,hF,rfl⟩ := ho
    rw [underReset_underlyingFormulas,
      Section3.TransitionForm.normalize_underlyingFormulas _ hF] at hψ
    exact GeneratorStability.opening_branch_subformula c m kind a φ hψ

/-- All formulas in an actual contextual branch, current and next together,
are genuine syntactic subformulas of its source predicate formula. -/
theorem branch_underlying_subformula
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var} (hb : ConcreteContextual.catalogue.Branch p Λ B)
    {ψ : Formula Var} (hψ : ψ ∈ B.underlyingFormulas) : ψ ≼ p.formula := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  rw [underReset_underlyingFormulas,ha.underlyingFormulas] at hψ
  exact mixed_branch_underlying_subformula hR hψ

theorem branch_current_formula_subformula
    {p q : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var} (hb : ConcreteContextual.catalogue.Branch p Λ B)
    (hq : Local.predicate q ∈ B.current.locals) : q.formula ≼ p.formula :=
  branch_underlying_subformula hb (Or.inl ⟨q,hq,rfl⟩)

theorem branch_next_formula_subformula
    {p q : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var} (hb : ConcreteContextual.catalogue.Branch p Λ B)
    {N : Section3.StateForm Clock Var} (hN : B.nextPart = some N)
    (hq : Local.predicate q ∈ N.locals) : q.formula ≼ p.formula := by
  apply branch_underlying_subformula hb
  right
  rw [hN]
  exact ⟨q,hq,rfl⟩

end STLTableau.Section4.Finiteness
