import STLTableaux.Closure.Catalogue.FaithfulFreshBranch

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Predicate
@[simp] theorem complexity_rename (p : Predicate Clock Var) (e : Equiv.Perm Clock) :
    (p.rename e).complexity = p.complexity := by cases p <;> rfl
end Predicate
namespace TransitionForm
private theorem current_property_renamed (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (Q : Predicate Clock Var → Prop)
    (hQ : ∀ p, Q (p.rename e) ↔ Q p) :
    (∀ p, Local.predicate p ∈ (S.rename e).locals → Q p) ↔
      (∀ p, Local.predicate p ∈ S.locals → Q p) := by
  constructor
  · intro h p hp
    apply (hQ p).1
    exact h (p.rename e) ⟨.predicate p,hp,rfl⟩
  · intro h p hp
    obtain ⟨l,hl,he⟩ := hp
    cases l with
    | terminal => cases he
    | marker m => cases he
    | predicate q =>
        have he' : q.rename e = p := Local.predicate.inj he
        subst p
        exact (hQ q).2 (h q hl)

/-- Renaming bound clocks preserves clock-invariant properties of the current part. -/
theorem AlphaEquivalent.current_property {Φ Ψ : TransitionForm Clock Var}
    (h : AlphaEquivalent Φ Ψ) (Q : Predicate Clock Var → Prop)
    (hQ : ∀ (e : Equiv.Perm Clock) p, Q (p.rename e) ↔ Q p) :
    (∀ p, Local.predicate p ∈ Φ.current.locals → Q p) ↔
      (∀ p, Local.predicate p ∈ Ψ.current.locals → Q p) := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact current_property_renamed Φ.current e Q (hQ e)
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
end TransitionForm
namespace ClosureCatalogue
/-- Literal alpha closure of the concrete normalized branches. Its soundness
and strict complexity decrease follow from real permutation transport. -/
def alphaSaturated (E : ClosureCatalogue Clock Var) : ClosureCatalogue Clock Var where
  Admitted := E.Admitted
  Branch p Λ B := ∃ B₀, E.Branch p Λ B₀ ∧ TransitionForm.AlphaEquivalent B B₀
  branch_exists p hp hn Λ := by
    obtain ⟨B,hB⟩ := E.branch_exists p hp hn Λ
    exact ⟨B,B,hB,.refl B⟩
  branch_reduced := by
    rintro p Λ B ⟨B₀,hB,hα⟩ q hq
    exact ((hα.current_property (fun q => q.complexity < p.complexity)
      (fun e q => by rw [Predicate.complexity_rename])).2 (E.branch_reduced hB)) q hq
  branch_sound := by
    rintro p Λ B ⟨B₀,hB,hα⟩ σ P α k hk hi hs
    exact E.branch_sound hB σ P α k hk hi ((hα.holds σ P α k).1 hs)

theorem alphaSaturated_branch_iff (E : ClosureCatalogue Clock Var)
    (p : Predicate Clock Var) (Λ : ClockResetSet Clock) (B : TransitionForm Clock Var) :
    E.alphaSaturated.Branch p Λ B ↔
      ∃ B₀, E.Branch p Λ B₀ ∧ TransitionForm.AlphaEquivalent B B₀ := Iff.rfl

theorem alphaSaturated_branch_alpha (E : ClosureCatalogue Clock Var)
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B C : TransitionForm Clock Var}
    (h : E.alphaSaturated.Branch p Λ B) (ha : TransitionForm.AlphaEquivalent C B) :
    E.alphaSaturated.Branch p Λ C := by
  obtain ⟨B₀,hB,hα⟩ := h
  exact ⟨B₀,hB,ha.trans hα⟩
end ClosureCatalogue
end STLTableau.Section3
