import STLTableaux.Closure.Expansion.FaithfulPExpansion
import STLTableaux.Closure.Subsumption.FaithfulClosureRestriction
import STLTableaux.Closure.Expansion.BranchwiseRankCore

/-! The `p`-expansion relation (Definition 4.15) and successive expansion
levels (Definition 4.17). A step keeps a judgement that is rule-closed for
`p` or takes a minimal common extension with an expansion branch for `p`. -/
namespace STLTableau.Section3

variable {Clock Var : Type*}

namespace ClosureCatalogue

def BranchwisePExpansion (E : ClosureCatalogue Clock Var) (p : Predicate Clock Var)
    (F G : TransitionForm Clock Var) : Prop :=
  (E.RuleClosedFor F p ∧ G = F) ∨
    ∃ B, E.Branch p F.current.resets B ∧
      SyntacticallySubsumed F G ∧ SyntacticallySubsumed B G ∧
      ∀ H, SyntacticallySubsumed F H → SyntacticallySubsumed B H →
        SyntacticallySubsumed H G → SyntacticallySubsumed G H

theorem BranchwisePExpansion.extension {E : ClosureCatalogue Clock Var}
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.BranchwisePExpansion p F G) : SyntacticallySubsumed F G := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, h, _, _⟩
  · exact .refl _
  · exact h

/-- A fixed compatible branch has a minimal common extension below any
given common extension. Clock representatives remain fixed. -/
theorem branchwisePExpansion_exists_below (E : ClosureCatalogue Clock Var)
    {p : Predicate Clock Var} {F B U : TransitionForm Clock Var}
    (hb : E.Branch p F.current.resets B)
    (hFU : SyntacticallySubsumed F U) (hBU : SyntacticallySubsumed B U) :
    ∃ G, E.BranchwisePExpansion p F G ∧ SyntacticallySubsumed G U := by
  classical
  let Candidate := fun G : TransitionForm Clock Var =>
    SyntacticallySubsumed F G ∧ SyntacticallySubsumed B G ∧ SyntacticallySubsumed G U
  obtain ⟨G, hG⟩ := exists_minimalFor_of_wellFoundedLT Candidate
    TransitionForm.componentCount ⟨U, hFU, hBU, .refl U⟩
  refine ⟨G, Or.inr ⟨B, hb, hG.1.1, hG.1.2.1, ?_⟩, hG.1.2.2⟩
  intro H hFH hBH hHG
  have hcount := hHG.componentCount_le
  have hmin := hG.2 ⟨hFH, hBH, hHG.trans hG.1.2.2⟩ hcount
  have heq := hHG.eq_of_componentCount_eq (Nat.le_antisymm hcount hmin)
  subst H
  exact .refl G

theorem BranchwisePExpansion.new_current_witness {E : ClosureCatalogue Clock Var}
    {p q : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.BranchwisePExpansion p F G)
    (hq : Local.predicate q ∈ G.current.locals)
    (hnew : Local.predicate q ∉ F.current.locals) :
    ∃ B, E.Branch p F.current.resets B ∧
      SyntacticallySubsumed B G ∧ Local.predicate q ∈ B.current.locals := by
  rcases h with ⟨_, rfl⟩ | ⟨B, hB, hFG, hBG, hmin⟩
  · exact (hnew hq).elim
  let Q := fun l : Local Clock Var => l ∈ F.current.locals ∨ l ∈ B.current.locals
  let H := G.restrictLocals Q (fun _ => True)
  have hFH : SyntacticallySubsumed F H :=
    hFG.restrictLocalsTarget Q (fun _ => True)
      (fun _ hl => Or.inl hl) (by intros; trivial)
  have hBH : SyntacticallySubsumed B H :=
    hBG.restrictLocalsTarget Q (fun _ => True)
      (fun _ hl => Or.inr hl) (by intros; trivial)
  have hGH := hmin H hFH hBH (G.restrictLocals_subsumed Q (fun _ => True))
  have hmem := hGH.current.locals hq
  change Local.predicate q ∈ G.current.locals ∧ Q (.predicate q) at hmem
  exact ⟨B, hB, hBG, hmem.2.resolve_left hnew⟩

theorem BranchwisePExpansion.new_current_complexity {E : ClosureCatalogue Clock Var}
    {p q : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : E.BranchwisePExpansion p F G)
    (hq : Local.predicate q ∈ G.current.locals)
    (hnew : Local.predicate q ∉ F.current.locals) : q.complexity < p.complexity := by
  obtain ⟨_, hB, _, hqB⟩ := h.new_current_witness hq hnew
  exact E.branch_reduced hB q hqB

end ClosureCatalogue

namespace ConcreteContextual

theorem branchwisePExpansion_target_ruleClosed [DecidableEq Clock]
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : catalogue.BranchwisePExpansion p F G) : catalogue.RuleClosedFor G p := by
  rcases h with ⟨hc, rfl⟩ | ⟨_, hb, _, hBG, _⟩
  · exact hc
  · exact Or.inr (branch_rebase hb hBG)

/-- Source-next alpha-conversion affects no current predicate or reset. -/
def AlphaBranchwisePExpansion [DecidableEq Clock] (p : Predicate Clock Var)
    (F G : TransitionForm Clock Var) : Prop :=
  ∃ F', NextAlphaPath F F' ∧ catalogue.BranchwisePExpansion p F' G

def branchwiseCurrent (F : TransitionForm Clock Var) : Set (Predicate Clock Var) :=
  {p | Local.predicate p ∈ F.current.locals}

abbrev branchwiseExpansionLevel [DecidableEq Clock] :=
  BranchwiseExpansion.level (catalogue (Clock := Clock) (Var := Var)).BranchwisePExpansion
    branchwiseCurrent

abbrev alphaBranchwiseExpansionLevel [DecidableEq Clock] :=
  BranchwiseExpansion.level (AlphaBranchwisePExpansion (Clock := Clock) (Var := Var))
    branchwiseCurrent

noncomputable def branchwiseLevelRank [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) : ℕ :=
  BranchwiseExpansion.rank (catalogue (Clock := Clock) (Var := Var)).BranchwisePExpansion
    branchwiseCurrent Predicate.complexity F i

noncomputable def alphaBranchwiseLevelRank [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) : ℕ :=
  BranchwiseExpansion.rank (AlphaBranchwisePExpansion (Clock := Clock) (Var := Var))
    branchwiseCurrent Predicate.complexity F i

end ConcreteContextual
end STLTableau.Section3
