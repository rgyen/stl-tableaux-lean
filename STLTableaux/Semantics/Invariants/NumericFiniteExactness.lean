import STLTableaux.Semantics.Invariants.NumericInvariant

/-! The positional and nonemptiness conditions for the finite numeric
invariant imply the auxiliary upper bound for `↑↓` `□`. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}

theorem finite_numeric_iff_positional (p : IntervalPredicate Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size) :
    (Predicate.ofFinite p).Numeric (P.interval ⟨k.1,hk⟩) α ↔
    let J := P.interval ⟨k.1,hk⟩
    match p with
    | .plain _ => True
    | .upper c b .always I _ => (α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower
    | .bounded c d b q .always I _ =>
        (α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower ∧
        (α d : ℝ) <[Marker.conj b q] ((α c : ℝ)+(I.upper-I.lower))
    | .upper c b .eventually I _ =>
        (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper ∧
        (0 : ℝ) <[Marker.conj b J.rightBoundary] ((α c : ℝ)+(J.right-J.left))
    | .bounded c d b q .eventually I _ =>
        (α c : ℝ) <[Marker.imp b J.leftBoundary] I.upper ∧
        (α d : ℝ) <[Marker.conj b q] (α c : ℝ) := by
  cases p with
  | plain => rfl
  | upper c b kind I φ => cases kind <;>
      simp [Predicate.ofFinite,Predicate.Numeric,IntervalPredicate.Invariant,STLTableau.AlwaysSafe]
  | bounded c d b q kind I φ =>
      cases kind with
      | eventually =>
          simp [Predicate.ofFinite,Predicate.Numeric,IntervalPredicate.Invariant,
            STLTableau.AlwaysSafe]
      | always =>
          constructor
          · exact fun h => ⟨h.2,h.1.1⟩
          · intro h
            exact ⟨STLTableau.invariant_implies_residual σ P α k hk _ h,h.1⟩
end STLTableau.Section3
