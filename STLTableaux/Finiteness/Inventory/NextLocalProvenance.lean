import STLTableaux.Closure.Expansion.FaithfulPExpansionProvenance

/-! Next-local provenance follows from literal minimality, without assuming
an expansion history or treating arbitrary closed extensions as minimal. -/
namespace STLTableau.Section3.ConcreteContextual
variable {Clock Var : Type*} [DecidableEq Clock]

theorem pExpansion_new_next_witness
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hexp : catalogue.PExpansion p F G)
    {M : StateForm Clock Var} (hM : G.nextPart = some M)
    (l : Local Clock Var) (hl : l ∈ M.locals)
    (hnew : ¬ ∃ N, F.nextPart = some N ∧ l ∈ N.locals) :
    ∃ B N, catalogue.Branch p G.current.resets B ∧
      SyntacticallySubsumed B G ∧ B.nextPart = some N ∧ l ∈ N.locals := by
  classical
  rcases hexp with ⟨_, rfl⟩ | ⟨hopen, hext, hclosed, hminimal⟩
  · exact (hnew ⟨M, hM, hl⟩).elim
  rcases hclosed with hnone | ⟨B, hB, hBG⟩
  · exact (hnone (branch_exists_of_not_ruleClosed hopen G.current.resets)).elim
  let Q : Local Clock Var → Prop := fun x =>
    (∃ N, F.nextPart = some N ∧ x ∈ N.locals) ∨
      (∃ N, B.nextPart = some N ∧ x ∈ N.locals)
  let H := G.restrictLocals (fun _ => True) Q
  have hFH : SyntacticallySubsumed F H :=
    hext.restrictLocalsTarget (fun _ => True) Q (by intros; trivial)
      (fun N _ hn _ x hx => Or.inl ⟨N, hn, hx⟩)
  have hBH : SyntacticallySubsumed B H :=
    hBG.restrictLocalsTarget (fun _ => True) Q (by intros; trivial)
      (fun N _ hn _ x hx => Or.inr ⟨N, hn, hx⟩)
  have hGH := hminimal H hFH (Or.inr ⟨B, hB, hBH⟩)
    (G.restrictLocals_subsumed (fun _ => True) Q)
  obtain ⟨M', hM', hi, _⟩ := hGH.next M hM
  have he : M' = M.restrictLocals Q := by
    simpa only [H, TransitionForm.restrictLocals, hM, Option.map_some,
      Option.some.injEq] using hM'.symm
  subst M'
  have hx : Q l := (hi.locals hl).2
  obtain ⟨N, hn, hln⟩ := hx.resolve_left hnew
  exact ⟨B, N, hB, hBG, hn, hln⟩

end STLTableau.Section3.ConcreteContextual

namespace STLTableau.Section3.ClosureCatalogue
variable {Clock Var : Type*}

/-- Every next local of a minimal closure is inherited from the anchor or
belongs to a represented branch of one of the closure's current predicates. -/
theorem IsClosure.next_local_provenance {E : ClosureCatalogue Clock Var}
    {F G : TransitionForm Clock Var} (hc : E.IsClosure F G)
    {M : StateForm Clock Var} (hM : G.nextPart = some M)
    (l : Local Clock Var) (hl : l ∈ M.locals) :
    (∃ N, F.nextPart = some N ∧ l ∈ N.locals) ∨
      ∃ p B N, Local.predicate p ∈ G.current.locals ∧
        E.Branch p G.current.resets B ∧ SyntacticallySubsumed B G ∧
        B.nextPart = some N ∧ l ∈ N.locals := by
  classical
  let Q : Local Clock Var → Prop := fun x =>
    (∃ N, F.nextPart = some N ∧ x ∈ N.locals) ∨
      ∃ p B N, Local.predicate p ∈ G.current.locals ∧
        E.Branch p G.current.resets B ∧ SyntacticallySubsumed B G ∧
        B.nextPart = some N ∧ x ∈ N.locals
  let H := G.restrictLocals (fun _ => True) Q
  have hFH : SyntacticallySubsumed F H :=
    hc.extension.restrictLocalsTarget (fun _ => True) Q (by intros; trivial)
      (fun N _ hn _ x hx => Or.inl ⟨N, hn, hx⟩)
  have hclosed : E.IsClosed H := by
    intro p hp
    have hpG : Local.predicate p ∈ G.current.locals := hp.1
    rcases hc.closed p hpG with hn | ⟨B, hb, hBG⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, ?_⟩
      exact hBG.restrictLocalsTarget (fun _ => True) Q (by intros; trivial)
        (fun N _ hN _ x hx => Or.inr ⟨p, B, N, hpG, hb, hBG, hN, hx⟩)
  have hGH := hc.minimal H hFH hclosed
    (G.restrictLocals_subsumed (fun _ => True) Q)
  obtain ⟨M', hM', hi, _⟩ := hGH.next M hM
  have he : M' = M.restrictLocals Q := by
    simpa only [H, TransitionForm.restrictLocals, hM, Option.map_some,
      Option.some.injEq] using hM'.symm
  subst M'
  exact (hi.locals hl).2

/-- A generator anchor has no inherited next part, so all successor locals
come from an actual represented branch. -/
theorem IsClosure.ofState_next_local_provenance {E : ClosureCatalogue Clock Var}
    {S : StateForm Clock Var} {G : TransitionForm Clock Var}
    (hc : E.IsClosure (TransitionForm.ofState S) G)
    {M : StateForm Clock Var} (hM : G.nextPart = some M)
    (l : Local Clock Var) (hl : l ∈ M.locals) :
    ∃ p B N, Local.predicate p ∈ G.current.locals ∧
      E.Branch p G.current.resets B ∧ SyntacticallySubsumed B G ∧
      B.nextPart = some N ∧ l ∈ N.locals := by
  rcases hc.next_local_provenance hM l hl with ⟨N, hN, _⟩ | h
  · cases hN
  · exact h

end STLTableau.Section3.ClosureCatalogue
