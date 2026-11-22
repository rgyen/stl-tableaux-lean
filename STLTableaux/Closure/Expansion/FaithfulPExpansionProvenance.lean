import STLTableaux.Closure.Expansion.FaithfulPExpansion
import STLTableaux.Closure.Subsumption.FaithfulClosureRestriction

/-! Literal minimal p-expansions introduce no new current predicates except
those of a witnessing contextual branch. Current and successor bindings are
kept fixed while filtering the target, so this argument does not require a
compatible union construction or any semantic assumptions. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ClosureCatalogue

theorem PExpansion.eq_of_source_ruleClosed {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.PExpansion p F G) (hc : E.RuleClosedFor F p) : G = F := by
  rcases h with ⟨_,he⟩ | ⟨hn,_⟩
  · exact he
  · exact (hn hc).elim
end ClosureCatalogue

namespace ConcreteContextual

/-- A genuinely open source has contextual branches at every surrounding
reset assignment. Bound-clock alpha representatives stay inside `Branch`. -/
theorem branch_exists_of_not_ruleClosed [DecidableEq Clock]
    {F : TransitionForm Clock Var} {p : Predicate Clock Var}
    (hopen : ¬ catalogue.RuleClosedFor F p) (Λ : ClockResetSet Clock) :
    ∃ B, catalogue.Branch p Λ B := by
  have hex : ∃ B, catalogue.Branch p F.current.resets B := by
    by_contra hn
    exact hopen (Or.inl hn)
  obtain ⟨B,R,A,hR,hA,rfl⟩ := hex
  exact ⟨A.underReset Λ,R,A,hR,hA,rfl⟩

/-- Minimality in the proof of Lemma 4.19. Every new current predicate
belongs to a branch for `p` that is subsumed by the target. -/
theorem pExpansion_new_current_witness [DecidableEq Clock]
    {p q : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hexp : catalogue.PExpansion p F G)
    (hq : Local.predicate q ∈ G.current.locals)
    (hqnew : Local.predicate q ∉ F.current.locals) :
    ∃ B, catalogue.Branch p G.current.resets B ∧
      SyntacticallySubsumed B G ∧ Local.predicate q ∈ B.current.locals := by
  classical
  rcases hexp with ⟨_,rfl⟩ | ⟨hopen,hext,hclosed,hminimal⟩
  · exact (hqnew hq).elim
  rcases hclosed with hnone | ⟨B,hB,hBG⟩
  · exact (hnone (branch_exists_of_not_ruleClosed hopen G.current.resets)).elim
  let Q : Local Clock Var → Prop := fun l => l ∈ F.current.locals ∨ l ∈ B.current.locals
  let H := G.restrictLocals Q (fun _ => True)
  have hFH : SyntacticallySubsumed F H :=
    hext.restrictLocalsTarget Q (fun _ => True)
      (fun l hl => Or.inl hl) (by intros; trivial)
  have hBH : SyntacticallySubsumed B H :=
    hBG.restrictLocalsTarget Q (fun _ => True)
      (fun l hl => Or.inr hl) (by intros; trivial)
  have hcH : catalogue.RuleClosedFor H p := Or.inr ⟨B,hB,hBH⟩
  have hGH := hminimal H hFH hcH (G.restrictLocals_subsumed Q (fun _ => True))
  have hmem := hGH.current.locals hq
  change Local.predicate q ∈ G.current.locals ∧ Q (.predicate q) at hmem
  exact ⟨B,hB,hBG,hmem.2.resolve_left hqnew⟩

/-- Every newly introduced current predicate has strictly smaller complexity
than the predicate expanded. No stability, invariant, truth, or source-next
renaming premise is necessary for this syntactic statement. -/
theorem pExpansion_new_current_complexity [DecidableEq Clock]
    {p q : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hexp : catalogue.PExpansion p F G)
    (hq : Local.predicate q ∈ G.current.locals)
    (hqnew : Local.predicate q ∉ F.current.locals) :
    q.complexity < p.complexity := by
  obtain ⟨B,hB,_,hqb⟩ := pExpansion_new_current_witness hexp hq hqnew
  exact catalogue.branch_reduced hB q hqb

/-- Classification used when tracing an unclosed end-of-round predicate
backward through the round's successive single-predicate expansions. -/
theorem pExpansion_current_classification [DecidableEq Clock]
    {p q : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hexp : catalogue.PExpansion p F G)
    (hq : Local.predicate q ∈ G.current.locals) :
    Local.predicate q ∈ F.current.locals ∨ q.complexity < p.complexity := by
  classical
  by_cases hold : Local.predicate q ∈ F.current.locals
  · exact Or.inl hold
  · exact Or.inr (pExpansion_new_current_complexity hexp hq hold)

end ConcreteContextual
end STLTableau.Section3
