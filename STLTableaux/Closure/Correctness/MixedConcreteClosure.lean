import STLTableaux.Closure.Correctness.ConcreteClosure
import STLTableaux.Closure.Normalization.UnboundedConcreteNormalization

namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace ClosureCatalogue

def union (E F : ClosureCatalogue Clock Var) : ClosureCatalogue Clock Var where
  Admitted := fun p => E.Admitted p ∨ F.Admitted p
  Branch := fun p Λ B => E.Branch p Λ B ∨ F.Branch p Λ B
  branch_exists := by
    intro p hp ha Λ
    rcases hp with h | h
    · obtain ⟨B, hB⟩ := E.branch_exists p h ha Λ
      exact ⟨B, Or.inl hB⟩
    · obtain ⟨B, hB⟩ := F.branch_exists p h ha Λ
      exact ⟨B, Or.inr hB⟩
  branch_reduced := by
    intro p Λ B hB q hq
    rcases hB with h | h
    · exact E.branch_reduced h q hq
    · exact F.branch_reduced h q hq
  branch_sound := by
    intro p Λ B hB σ P α k hk hi hs
    rcases hB with h | h
    · exact E.branch_sound h σ P α k hk hi hs
    · exact F.branch_sound h σ P α k hk hi hs

end ClosureCatalogue

namespace ConcreteInfinite
open UnboundedClocked

set_option linter.unusedSimpArgs false in
theorem raw_reduced [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {Ψ : Node Clock Var} (hΨ : Ψ ∈ Bs)
    (q : Predicate Clock Var) (hq : q ∈ (Judgement.ofUnbounded Ψ).currentPredicates) :
    q.complexity < (Predicate.ofUnbounded p).complexity := by
  classical
  (cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hΨ <;>
    (try split_ifs at hΨ) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hΨ) <;>
    rcases hΨ with rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
      alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
      boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
      Judgement.ofUnbounded, Judgement.currentPredicates, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, false_or, or_false] at hq <;>
    (try contradiction) <;> subst q <;>
    simp [Predicate.ofUnbounded, Predicate.complexity]

def Branch [DecidableEq Clock] (p : Predicate Clock Var) (Λ : ClockResetSet Clock)
    (B : TransitionForm Clock Var) : Prop :=
  ∃ (p₀ : UnboundedClocked.Predicate Clock Var) (Bs : List (Node Clock Var))
    (Ψ : Node Clock Var) (F : TransitionForm Clock Var),
    p = Predicate.ofUnbounded p₀ ∧ UnboundedClocked.ConcreteRule p₀ Bs ∧ Ψ ∈ Bs ∧
    TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F ∧ B = F.underReset Λ

def Admitted [DecidableEq Clock] (p : Predicate Clock Var) : Prop :=
  p.IsAtomic ∨ ∃ (p₀ : UnboundedClocked.Predicate Clock Var) (Bs : List (Node Clock Var)),
    p = Predicate.ofUnbounded p₀ ∧ UnboundedClocked.ConcreteRule p₀ Bs

noncomputable def catalogue [DecidableEq Clock] : ClosureCatalogue Clock Var where
  Admitted := Admitted
  Branch := Branch
  branch_exists := by
    intro p hp hna Λ
    rcases hp with ha | ⟨p₀, Bs, rfl, hr⟩
    · exact (hna ha).elim
    have hne : Bs ≠ [] := by
      cases hr <;> simp [upperAlwaysBranches, boundedAlwaysBranches,
        upperEventuallyBranches, boundedEventuallyBranches]
    obtain ⟨Ψ, hΨ⟩ := List.exists_mem_of_ne_nil Bs hne
    obtain ⟨F, hF, _⟩ := branch_normalization hr hΨ Λ
    exact ⟨F.underReset Λ, p₀, Bs, Ψ, F, rfl, hr, hΨ, hF, rfl⟩
  branch_reduced := by
    intro p Λ B hB q hq
    obtain ⟨p₀, Bs, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hB
    exact raw_reduced hr hΨ q ((TransitionForm.normalize_currentPredicates _ hF q).1 hq)
  branch_sound := by
    intro p Λ B hB σ P α k hk hi hs
    obtain ⟨p₀, Bs, Ψ, F, rfl, hr, hΨ, hF, rfl⟩ := hB
    obtain ⟨G, hG, he⟩ := branch_normalization hr hΨ Λ
    have hFG : F = G := Option.some.inj (hF.symm.trans hG)
    subst G
    have hi₀ : ∀ hk' : k.1 < P.size,
        UnboundedClocked.Invariant σ P (Λ.apply α) k hk' p₀ := by
      intro hk'
      cases p₀ <;> exact hi
    have hp := UnboundedClocked.rule_sound hr σ P (Λ.apply α) k hi₀
      ⟨Ψ, hΨ, (he σ P α k).1 hs⟩
    apply (Predicate.holds_ofUnbounded σ (P.interval ⟨k.1, hk⟩) (Λ.apply α) p₀).2
    simpa only [Node.holds, dif_pos hk] using hp

end ConcreteInfinite

namespace ConcreteOpening
open UnboundedClocked

def Branch [DecidableEq Clock] (p : Predicate Clock Var) (Λ : ClockResetSet Clock)
    (B : TransitionForm Clock Var) : Prop :=
  ∃ (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (F : TransitionForm Clock Var),
    p = .plain (UnboundedClocked.formula kind a φ) ∧
    TransitionForm.normalize? (Judgement.ofUnbounded (opening c m kind a φ)) = some F ∧
    B = F.underReset Λ

def Admitted (p : Predicate Clock Var) : Prop :=
  p.IsAtomic ∨ ∃ (c : Clock) (kind : TemporalKind) (a : NNReal) (φ : Formula Var),
    p = .plain (UnboundedClocked.formula kind a φ)

noncomputable def catalogue [DecidableEq Clock] : ClosureCatalogue Clock Var where
  Admitted := Admitted
  Branch := Branch
  branch_exists := by
    intro p hp hna Λ
    rcases hp with ha | ⟨c, kind, a, φ, rfl⟩
    · exact (hna ha).elim
    obtain ⟨F, hF, _⟩ := ConcreteInfinite.opening_normalization c ○ kind a φ Λ
    exact ⟨F.underReset Λ, c, ○, kind, a, φ, F, rfl, hF, rfl⟩
  branch_reduced := by
    intro p Λ B hB q hq
    obtain ⟨c, m, kind, a, φ, F, rfl, hF, rfl⟩ := hB
    have hraw := (TransitionForm.normalize_currentPredicates _ hF q).1 hq
    simp only [opening, Judgement.ofUnbounded, Judgement.currentPredicates,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false] at hraw
    subst q
    cases kind <;>
      simp [Predicate.ofUnbounded, Predicate.complexity, UnboundedClocked.formula,
        Formula.always, Formula.eventually, Predicate.formulaComplexity]
  branch_sound := by
    intro p Λ B hB σ P α k hk _hi hs
    obtain ⟨c, m, kind, a, φ, F, rfl, hF, rfl⟩ := hB
    obtain ⟨G, hG, he⟩ := ConcreteInfinite.opening_normalization c m kind a φ Λ
    have hFG : F = G := Option.some.inj (hF.symm.trans hG)
    subst G
    have hp := (opening_correct σ P (Λ.apply α) k c kind a φ).2
      ⟨m, (he σ P α k).1 hs⟩
    simpa only [Node.holds, dif_pos hk, Predicate.holds, STLTableau.predicateSatisfies] using hp

end ConcreteOpening

namespace ConcreteMixed

/-- All registered finite families, all literal infinite clocked families,
and both infinite opening families in one faithful transition syntax. -/
noncomputable def catalogue [DecidableEq Clock] : ClosureCatalogue Clock Var :=
  ConcreteFinite.catalogue.union (ConcreteInfinite.catalogue.union ConcreteOpening.catalogue)

theorem closed_holds_of_atomicProjection [DecidableEq Clock]
    {Φ : TransitionForm Clock Var} (hc : catalogue.IsClosed Φ)
    (hadmit : ∀ p, Local.predicate p ∈ Φ.current.locals → catalogue.Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hi : ∀ p, Local.predicate p ∈ Φ.current.locals →
      p.Invariant σ P (Φ.current.resets.apply α) k hk)
    (hs : Φ.atomicProjection.holds σ P α k) : Φ.holds σ P α k :=
  ClosureCatalogue.closed_holds_of_atomicProjection catalogue hc hadmit σ P α k hk hi hs

end ConcreteMixed
end STLTableau.Section3
