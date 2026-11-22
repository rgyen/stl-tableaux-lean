import STLTableaux.Closure.Normalization.ConcreteNormalization

/-! Closure soundness for the finite rule catalogue. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ConcreteFinite

theorem formulaComplexity_eq (φ : Formula Var) :
    Predicate.formulaComplexity φ = φ.complexity := by
  induction φ <;> simp_all [Predicate.formulaComplexity, Formula.complexity]

theorem complexity_ofFinite (p : IntervalPredicate Clock Var) :
    (Predicate.ofFinite p).complexity = p.complexity := by
  cases p <;> simp [Predicate.ofFinite, Predicate.complexity,
    IntervalPredicate.complexity, formulaComplexity_eq]

theorem currentPredicates_ofFinite (Ψ : STLTableau.Judgement Clock Var)
    (q : Predicate Clock Var) :
    q ∈ (Judgement.ofFinite Ψ).currentPredicates ↔
      ∃ p, q = Predicate.ofFinite p ∧ p ∈ Ψ.currentPredicates := by
  induction Ψ with
  | terminal => simp [Judgement.ofFinite, Judgement.currentPredicates,
      STLTableau.Judgement.currentPredicates]
  | clock c r a => simp [Judgement.ofFinite, Judgement.currentPredicates,
      STLTableau.Judgement.currentPredicates]
  | leftMarker m => simp [Judgement.ofFinite, Judgement.currentPredicates,
      STLTableau.Judgement.currentPredicates]
  | predicate p => simp [Judgement.ofFinite, Judgement.currentPredicates,
      STLTableau.Judgement.currentPredicates]
  | reset Λ Ψ ih => exact ih
  | next Ψ ih => simp [Judgement.ofFinite, Judgement.currentPredicates,
      STLTableau.Judgement.currentPredicates]
  | conj Φ Ψ ihΦ ihΨ =>
      simp only [Judgement.ofFinite, Judgement.currentPredicates,
        STLTableau.Judgement.currentPredicates, Set.mem_union, ihΦ, ihΨ]
      aesop

/-- A concrete finite source and an actual normalized branch. No semantic
closure property is built into this relation. -/
def Branch [DecidableEq Clock] (p : Predicate Clock Var) (Λ : ClockResetSet Clock)
    (B : TransitionForm Clock Var) : Prop :=
  ∃ (p₀ : IntervalPredicate Clock Var) (R : ExpansionRule Clock Var)
    (Ψ : STLTableau.Judgement Clock Var) (F : TransitionForm Clock Var),
    p = Predicate.ofFinite p₀ ∧ STLTableau.ConcreteRule p₀ R ∧ Ψ ∈ R.branches ∧
    TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F ∧ B = F.underReset Λ

/-- The admitted sources are atomic predicates or exactly the sources of
registered finite concrete rules. Infinite sources are added separately. -/
def Admitted [DecidableEq Clock] (p : Predicate Clock Var) : Prop :=
  p.IsAtomic ∨ ∃ (p₀ : IntervalPredicate Clock Var) (R : ExpansionRule Clock Var),
    p = Predicate.ofFinite p₀ ∧ STLTableau.ConcreteRule p₀ R

noncomputable def catalogue [DecidableEq Clock] : ClosureCatalogue Clock Var where
  Admitted := Admitted
  Branch := Branch
  branch_exists := by
    intro p hp hna Λ
    rcases hp with ha | ⟨p₀, R, rfl, hr⟩
    · exact (hna ha).elim
    obtain ⟨Ψ, hΨ⟩ := List.exists_mem_of_ne_nil R.branches R.branches_nonempty
    obtain ⟨F, hF, _⟩ := branch_normalization hr hΨ Λ
    exact ⟨F.underReset Λ, p₀, R, Ψ, F, rfl, hr, hΨ, hF, rfl⟩
  branch_reduced := by
    intro p Λ B hB q hq
    obtain ⟨p₀, R, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hB
    have hqraw := (TransitionForm.normalize_currentPredicates (Judgement.ofFinite Ψ) hF q).1 hq
    obtain ⟨q₀, rfl, hq₀⟩ := (currentPredicates_ofFinite Ψ q).1 hqraw
    have hlt := hr.complexityReduced Ψ hΨ q₀ hq₀
    simpa only [complexity_ofFinite, STLTableau.ConcreteRule.source_eq hr] using hlt
  branch_sound := by
    intro p Λ B hB σ P α k hk hi hs
    obtain ⟨p₀, R, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hB
    obtain ⟨G, hG, he⟩ := branch_normalization hr hΨ Λ
    have hFG : F = G := Option.some.inj (hF.symm.trans hG)
    subst G
    have hi₀ : ∀ hk' : k.1 < P.size, STLTableau.Invariant σ P (Λ.apply α) k hk' p₀ := by
      intro hk'
      cases p₀ <;> exact hi
    have hp := STLTableau.rule_sound hr σ P (Λ.apply α) k hi₀ ⟨Ψ, hΨ, (he σ P α k).1 hs⟩
    apply (Predicate.holds_ofFinite σ (P.interval ⟨k.1, hk⟩) (Λ.apply α) p₀).2
    simpa only [STLTableau.satisfies, dif_pos hk] using hp

/-- Finite-rule case of Theorem 4.14 (closure soundness). -/
theorem closed_holds_of_atomicProjection [DecidableEq Clock]
    {Φ : TransitionForm Clock Var} (hc : catalogue.IsClosed Φ)
    (hadmit : ∀ p, Local.predicate p ∈ Φ.current.locals → Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hi : ∀ p, Local.predicate p ∈ Φ.current.locals →
      p.Invariant σ P (Φ.current.resets.apply α) k hk)
    (hs : Φ.atomicProjection.holds σ P α k) : Φ.holds σ P α k :=
  ClosureCatalogue.closed_holds_of_atomicProjection catalogue hc hadmit σ P α k hk hi hs

end ConcreteFinite
end STLTableau.Section3
