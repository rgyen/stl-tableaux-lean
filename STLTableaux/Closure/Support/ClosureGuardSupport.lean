import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! Minimal rule-closed extensions cannot introduce current guards when
rule branches have no current guards. No free-clock safety is assumed. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

theorem ClosureCatalogue.IsClosure.current_guards_eq
    {E : ClosureCatalogue Clock Var} {Φ U : TransitionForm Clock Var}
    (hc : E.IsClosure Φ U)
    (hg : ∀ p Λ B, E.Branch p Λ B → B.current.guards = ∅) :
    U.current.guards = Φ.current.guards := by
  let V : TransitionForm Clock Var :=
    { U with current := { U.current with
        guards := Φ.current.guards, guards_finite := Φ.current.guards_finite } }
  have hΦV : SyntacticallySubsumed Φ V :=
    ⟨⟨Set.Subset.refl _, hc.extension.current.resets, hc.extension.current.locals⟩,
      hc.extension.outerFresh, hc.extension.next⟩
  have hVU : SyntacticallySubsumed V U := by
    have hr := SyntacticallySubsumed.refl U
    exact ⟨⟨hc.extension.current.guards, hr.current.resets, hr.current.locals⟩,
      hr.outerFresh, hr.next⟩
  have hclosed : E.IsClosed V := by
    intro p hp
    rcases hc.closed p hp with hn | ⟨B, hb, hs⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, ?_⟩
      refine ⟨⟨?_, hs.current.resets, hs.current.locals⟩, hs.outerFresh, hs.next⟩
      rw [hg p U.current.resets B hb]
      exact Set.empty_subset _
  exact Set.Subset.antisymm (hc.minimal V hΦV hclosed hVU).current.guards
    hc.extension.current.guards

theorem ConcreteContextual.branch_current_guards_empty [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B) : B.current.guards = ∅ := by
  obtain ⟨R, A, hr, ha, rfl⟩ := hb
  exact ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hr)

theorem ConcreteContextual.closure_current_guards_eq [DecidableEq Clock]
    {Φ U : TransitionForm Clock Var}
    (hc : ConcreteContextual.catalogue.IsClosure Φ U) :
    U.current.guards = Φ.current.guards :=
  hc.current_guards_eq (fun _ _ _ hb => branch_current_guards_empty hb)

end STLTableau.Section3
