import STLTableaux.Tableau.Support.FreeClockRestriction
import STLTableaux.Closure.Support.BranchFreeClocks
import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! Free-clock safety of every literal minimal contextual closure. -/
namespace STLTableau.Section3
variable {Clock Var : Type*} [DecidableEq Clock]

theorem ConcreteContextual.branch_free_subset
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B) :
    B.freeClocks ⊆ (Judgement.predicate p).freeClocks \ Λ.clocks := by
  obtain ⟨R, A, hr, ha, rfl⟩ := hb
  intro c hc
  have hg := ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hr)
  obtain ⟨hc, hn⟩ := TransitionForm.freeClocks_underReset_subset A Λ hg hc
  rw [ha.freeClocks] at hc
  exact ⟨ConcreteMixed.branch_freeClocks hr hc, hn⟩

theorem ConcreteContextual.closure_freeClocks_subset
    {F U : TransitionForm Clock Var}
    (hc : ConcreteContextual.catalogue.IsClosure F U) : U.freeClocks ⊆ F.freeClocks := by
  let A := F.freeClocks
  let V := U.restrictFree A
  have hFV : SyntacticallySubsumed F V :=
    hc.extension.restrictFree_target A (Set.Subset.refl _)
  have hVU : SyntacticallySubsumed V U := U.restrictFree_subsumed A
  have hclosed : ConcreteContextual.catalogue.IsClosed V := by
    intro p hp
    have hpU : Local.predicate p ∈ U.current.locals := hp.1
    rcases hc.closed p hpU with hn | ⟨B, hb, hs⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, hs.restrictFree_target A ?_⟩
      intro c hcf
      obtain ⟨hpred, hn⟩ := branch_free_subset hb hcf
      exact (hp.2 hpred).resolve_right hn
  have hUV := hc.minimal V hFV hclosed hVU
  intro c hfree
  apply U.restrictFree_freeClocks_subset A
  rcases hfree with ⟨g, hg, he⟩ | ⟨hb, hn⟩
  · exact Or.inl ⟨g, hUV.current.guards hg, he⟩
  · exact Or.inr (hUV.unboundBody_mono ⟨hb, hn⟩)

end STLTableau.Section3
