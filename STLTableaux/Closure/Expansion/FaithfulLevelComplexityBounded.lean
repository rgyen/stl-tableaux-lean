import STLTableaux.Closure.Expansion.FaithfulLevelRankBounds
import STLTableaux.Closure.Expansion.FaithfulExpansionLevels

/-! The exact all-enumerations expansion family has `↑↓` predicate
complexities even when its clock-name representatives form an infinite set. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ExpansionFamily

theorem Sequence.complexity_bounded {Step Closed}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {ps F G} (h : Sequence Step ps F G) (N : ℕ)
    (hF : ∀ q, Local.predicate q ∈ F.current.locals → q.complexity ≤ N)
    (hps : ∀ p ∈ ps, p.complexity ≤ N) :
    ∀ q, Local.predicate q ∈ G.current.locals → q.complexity ≤ N := by
  intro q hq
  by_cases hqF : Local.predicate q ∈ F.current.locals
  · exact hF q hqF
  · obtain ⟨p,hp,_,hlt⟩ := h.new_current_origin laws q hq hqF
    exact hlt.le.trans (hps p hp)

theorem Round.complexity_bounded {Step Closed}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    {F G} (h : Round Step F G) (N : ℕ)
    (hF : ∀ q, Local.predicate q ∈ F.current.locals → q.complexity ≤ N) :
    ∀ q, Local.predicate q ∈ G.current.locals → q.complexity ≤ N := by
  obtain ⟨ps,hen,hseq⟩ := h
  exact hseq.complexity_bounded laws N hF (fun p hp => hF p ((hen.2 p).1 hp))

theorem level_complexity_bounded {Step Closed}
    (laws : StepLaws (Clock := Clock) (Var := Var) Step Closed)
    (F : TransitionForm Clock Var) (i : ℕ) :
    ComplexityBounded (level Step F i) (initialBound F) := by
  induction i with
  | zero => exact singleton_bounded F
  | succ i ih =>
      rintro G ⟨H,hH,hRound⟩
      exact hRound.complexity_bounded laws (initialBound F) (fun p hp => ih H hH p hp)
end ExpansionFamily
namespace ConcreteContextual

theorem literal_expansionLevel_bounded [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) :
    ExpansionFamily.ComplexityBounded (catalogue.expansionLevel F i)
      (ExpansionFamily.initialBound F) :=
  ExpansionFamily.level_complexity_bounded literalStepLaws F i

theorem alpha_expansionLevel_bounded [DecidableEq Clock]
    (F : TransitionForm Clock Var) (i : ℕ) :
    ExpansionFamily.ComplexityBounded (alphaExpansionLevel F i)
      (ExpansionFamily.initialBound F) :=
  ExpansionFamily.level_complexity_bounded alphaStepLaws F i
end ConcreteContextual
end STLTableau.Section3
