import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization
import STLTableaux.Closure.Normalization.NormalizedStability

/-! Capture-avoiding clock permutations leave every underlying STL formula
unchanged, including formulas in the successor part. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

@[simp] theorem StateForm.underlyingFormulas_rename (S : StateForm Clock Var)
    (e : Equiv.Perm Clock) : (S.rename e).underlyingFormulas = S.underlyingFormulas := by
  ext φ
  constructor
  · rintro ⟨p, ⟨l, hl, he⟩, rfl⟩
    cases l with
    | terminal => cases he
    | marker m => cases he
    | predicate q =>
        have hq : q.rename e = p := Local.predicate.inj he
        subst p
        exact ⟨q, hl, Predicate.formula_rename e q⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.rename e, ⟨.predicate p, hp, rfl⟩, (Predicate.formula_rename e p).symm⟩

@[simp] theorem StateForm.underlyingFormulas_alphaReset (S : StateForm Clock Var)
    (e : Equiv.Perm Clock) : (S.alphaReset e).underlyingFormulas = S.underlyingFormulas := by
  exact S.underlyingFormulas_rename e

@[simp] theorem TransitionForm.underlyingFormulas_alphaOuter (F : TransitionForm Clock Var)
    (e : Equiv.Perm Clock) : (F.alphaOuter e).underlyingFormulas = F.underlyingFormulas := by
  cases hN : F.nextPart <;>
    simp [underlyingFormulas, alphaOuter, hN]

@[simp] theorem TransitionForm.underlyingFormulas_alphaNext (F : TransitionForm Clock Var)
    (e : Equiv.Perm Clock) : (F.alphaNext e).underlyingFormulas = F.underlyingFormulas := by
  cases hN : F.nextPart <;>
    simp [underlyingFormulas, alphaNext, hN]

theorem TransitionForm.AlphaEquivalent.underlyingFormulas
    {F G : TransitionForm Clock Var} (h : AlphaEquivalent F G) :
    F.underlyingFormulas = G.underlyingFormulas := by
  induction h with
  | refl => rfl
  | outer F e hf => exact F.underlyingFormulas_alphaOuter e
  | next F e hf => exact F.underlyingFormulas_alphaNext e
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem TransitionForm.AlphaEquivalent.underlyingStable
    {F G : TransitionForm Clock Var} (h : AlphaEquivalent F G)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    F.UnderlyingStable σ P ↔ G.UnderlyingStable σ P := by
  unfold UnderlyingStable
  rw [h.underlyingFormulas]

end STLTableau.Section3
