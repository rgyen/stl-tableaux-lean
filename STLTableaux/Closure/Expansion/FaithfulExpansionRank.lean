import STLTableaux.Closure.Expansion.FaithfulExpansionLevels
import STLTableaux.Closure.Expansion.FaithfulLevelComplexityBounded
import STLTableaux.Closure.Expansion.ExpansionRankTermination

/-! The auxiliary closure search groups single-predicate steps into rounds
and ranks unclosed predicates. The revised one-step rank, which
instead counts newly appearing predicates, is in `BranchwiseRank`. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ExpansionFamily

/-- Exactly the maximum of complexities of unclosed current predicates
across the entire i-th expansion family; max of the empty set is zero. -/
noncomputable def levelRank (E : ClosureCatalogue Clock Var)
    (Step : Predicate Clock Var → TransitionForm Clock Var → TransitionForm Clock Var → Prop)
    (F : TransitionForm Clock Var) (i : ℕ) : ℕ := familyRank E (level Step F i)

theorem levelRank_decrease (E : ClosureCatalogue Clock Var) {Step}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step E.RuleClosedFor)
    (F : TransitionForm Clock Var) (i : ℕ) (hpos : 0 < levelRank E Step F i) :
    levelRank E Step F (i+1) < levelRank E Step F i := by
  apply familyRank_lt_of_all_lt E hpos
  rintro G ⟨H, hH, hround⟩ q hq hopen
  obtain ⟨p, hp, hpo, hlt⟩ := hround.unclosed_origin laws q hq hopen
  exact hlt.trans_le (complexity_le_familyRank E
    (level_complexity_bounded laws F i) hH p hp hpo)

theorem levelRank_zero_stable [DecidableEq Clock] {Step}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step ConcreteContextual.catalogue.RuleClosedFor)
    (F : TransitionForm Clock Var) (i : ℕ)
    (hz : levelRank ConcreteContextual.catalogue Step F i = 0) :
    levelRank ConcreteContextual.catalogue Step F (i+1) = 0 := by
  apply familyRank_eq_zero_of_all_closed
  rintro G ⟨H, hH, hround⟩ q hq
  by_contra hopen
  obtain ⟨p, hp, hpo, _⟩ := hround.unclosed_origin laws q hq hopen
  have hclosed := (familyRank_zero_iff_closed (level_complexity_bounded laws F i)).1 hz
  exact hpo (hclosed H hH p hp)

theorem levelRank_eventually_zero [DecidableEq Clock] {Step}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step ConcreteContextual.catalogue.RuleClosedFor)
    (F : TransitionForm Clock Var) :
    ∃ k : ℕ, ∀ i ≥ k, levelRank ConcreteContextual.catalogue Step F i = 0 :=
  eventually_zero_of_rank_decrease _
    (levelRank_decrease ConcreteContextual.catalogue laws F)
    (levelRank_zero_stable laws F)

end ExpansionFamily
namespace ConcreteContextual

noncomputable def literalLevelRank [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :=
  ExpansionFamily.levelRank catalogue catalogue.PExpansion F i
noncomputable def alphaLevelRank [DecidableEq Clock] (F : TransitionForm Clock Var) (i : ℕ) :=
  ExpansionFamily.levelRank catalogue AlphaPExpansion F i

theorem literal_level_rank_decrease [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) (h : 0 < literalLevelRank F i) :
    literalLevelRank F (i+1) < literalLevelRank F i :=
  ExpansionFamily.levelRank_decrease catalogue literalStepLaws F i h

theorem alpha_level_rank_decrease [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) (h : 0 < alphaLevelRank F i) :
    alphaLevelRank F (i+1) < alphaLevelRank F i :=
  ExpansionFamily.levelRank_decrease catalogue alphaStepLaws F i h

theorem literal_level_rank_eventually_zero [DecidableEq Clock]
    (F : TransitionForm Clock Var) : ∃ k : ℕ, ∀ i ≥ k, literalLevelRank F i = 0 :=
  ExpansionFamily.levelRank_eventually_zero literalStepLaws F

theorem alpha_level_rank_eventually_zero [DecidableEq Clock]
    (F : TransitionForm Clock Var) : ∃ k : ℕ, ∀ i ≥ k, alphaLevelRank F i = 0 :=
  ExpansionFamily.levelRank_eventually_zero alphaStepLaws F

end ConcreteContextual
end STLTableau.Section3
