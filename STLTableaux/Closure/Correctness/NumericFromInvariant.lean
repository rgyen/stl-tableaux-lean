import STLTableaux.Semantics.Invariants.NumericInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Local
theorem numeric_of_invariant (l : Local Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (h : l.EvaluatedInvariant σ P α k) : l.Numeric σ P α k := by
  cases l with
  | terminal => trivial
  | marker => trivial
  | predicate p => exact fun hk => p.numeric_of_invariant σ P α k hk (h hk)
end Local
namespace StateForm
theorem numeric_of_invariant (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (h : S.EvaluatedInvariant σ P α k) :
    S.EvaluatedNumeric σ P α k := fun l hl => l.numeric_of_invariant σ P _ k (h l hl)
end StateForm
namespace TransitionForm
theorem numeric_of_invariant (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (h : F.EvaluatedInvariant σ P α k) :
    F.EvaluatedNumeric σ P α k :=
  ⟨F.current.numeric_of_invariant σ P α k h.1,
    fun N hN hk => N.numeric_of_invariant σ P _ _ (h.2 N hN hk)⟩
end TransitionForm
end STLTableau.Section3
