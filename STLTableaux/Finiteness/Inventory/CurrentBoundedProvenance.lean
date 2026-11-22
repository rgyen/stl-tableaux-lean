import STLTableaux.Finiteness.Inventory.NextLocalProvenance

/-! Current-local provenance from literal closure minimality. No semantic,
expansion-history, or concrete-rule hypothesis is used. -/
namespace STLTableau.Section3.ClosureCatalogue
variable {Clock Var : Type*}

/-- Every current local is inherited or occurs in an actual represented
branch of a current predicate of this same closure. -/
theorem IsClosure.current_local_provenance {E : ClosureCatalogue Clock Var}
    {F G : TransitionForm Clock Var} (hc : E.IsClosure F G)
    (l : Local Clock Var) (hl : l ∈ G.current.locals) :
    l ∈ F.current.locals ∨
      ∃ p B, Local.predicate p ∈ G.current.locals ∧
        E.Branch p G.current.resets B ∧ SyntacticallySubsumed B G ∧
        l ∈ B.current.locals := by
  classical
  let Q : Local Clock Var → Prop := fun x => x ∈ F.current.locals ∨
    ∃ p B, Local.predicate p ∈ G.current.locals ∧
      E.Branch p G.current.resets B ∧ SyntacticallySubsumed B G ∧
      x ∈ B.current.locals
  let H := G.restrictLocals Q (fun _ => True)
  have hFH : SyntacticallySubsumed F H :=
    hc.extension.restrictLocalsTarget Q (fun _ => True)
      (fun _ hx => Or.inl hx) (by intros; trivial)
  have hclosed : E.IsClosed H := by
    intro p hp
    have hpG : Local.predicate p ∈ G.current.locals := hp.1
    rcases hc.closed p hpG with hn | ⟨B, hb, hBG⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, ?_⟩
      exact hBG.restrictLocalsTarget Q (fun _ => True)
        (fun _ hx => Or.inr ⟨p, B, hpG, hb, hBG, hx⟩) (by intros; trivial)
  have hGH := hc.minimal H hFH hclosed
    (G.restrictLocals_subsumed Q (fun _ => True))
  exact (hGH.current.locals hl).2

/-- If the local is absent from every represented current branch, minimal
closure cannot introduce it. The converse is the literal anchor extension. -/
theorem IsClosure.current_local_mem_iff_of_branch_absent
    {E : ClosureCatalogue Clock Var} {F G : TransitionForm Clock Var}
    (hc : E.IsClosure F G) (l : Local Clock Var)
    (habsent : ∀ p B, Local.predicate p ∈ G.current.locals →
      E.Branch p G.current.resets B → SyntacticallySubsumed B G →
      l ∉ B.current.locals) :
    l ∈ G.current.locals ↔ l ∈ F.current.locals := by
  constructor
  · intro hl
    rcases hc.current_local_provenance l hl with h | ⟨p, B, hp, hb, hBG, hm⟩
    · exact h
    · exact (habsent p B hp hb hBG hm).elim
  · intro hl
    exact hc.extension.current.locals hl

end STLTableau.Section3.ClosureCatalogue
