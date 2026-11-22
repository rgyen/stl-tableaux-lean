import STLTableaux.Closure.Correctness.MixedConcreteClosure

/-! Stability attached to every underlying formula of a generator, including
predicates below next and reset. This supplies the formula-provenance part of
successor stability without assuming stability of an unrelated root formula. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}

namespace Predicate

def formula : Predicate Clock Var → Formula Var
  | .plain φ => φ
  | .upper _ _ .always I φ | .bounded _ _ _ _ .always I φ => □[I] φ
  | .upper _ _ .eventually I φ | .bounded _ _ _ _ .eventually I φ => ◇[I] φ

@[simp] theorem formula_ofFinite (p : IntervalPredicate Clock Var) :
    (ofFinite p).formula = p.formula := by cases p <;> (try cases ‹TemporalKind›) <;> rfl

@[simp] theorem formula_ofUnbounded (p : UnboundedClocked.Predicate Clock Var) :
    (ofUnbounded p).formula = p.formula := by cases p <;> (try cases ‹TemporalKind›) <;> rfl

end Predicate

namespace Judgement

/-- All predicate formulas, including those under next and reset. -/
def underlyingFormulas : Judgement Clock Var → Set (Formula Var)
  | .predicate p => {p.formula}
  | .conj Φ Ψ => underlyingFormulas Φ ∪ underlyingFormulas Ψ
  | .next Ψ | .reset _ Ψ => underlyingFormulas Ψ
  | _ => ∅

def UnderlyingStable (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Ψ : Judgement Clock Var) : Prop :=
  ∀ φ ∈ Ψ.underlyingFormulas, σ.StablePartition φ P

theorem underlyingStable_of_subformulas (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (Ψ : Judgement Clock Var) (φ : Formula Var)
    (hsub : ∀ ψ ∈ Ψ.underlyingFormulas, ψ ≼ φ)
    (hst : σ.StablePartition φ P) : Ψ.UnderlyingStable σ P := by
  intro ψ hψ j χ hχ
  exact hst j χ (hχ.trans (hsub ψ hψ))

@[simp] theorem underlyingStable_next (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (Ψ : Judgement Clock Var) :
    UnderlyingStable σ P (.next Ψ) ↔ UnderlyingStable σ P Ψ := Iff.rfl

@[simp] theorem underlyingStable_reset (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (Λ : ClockResetSet Clock) (Ψ : Judgement Clock Var) :
    UnderlyingStable σ P (.reset Λ Ψ) ↔ UnderlyingStable σ P Ψ := Iff.rfl

@[simp] theorem underlyingStable_plain (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (φ : Formula Var) :
    UnderlyingStable σ P (.predicate (.plain φ) : Judgement Clock Var) ↔
      σ.StablePartition φ P := by simp [UnderlyingStable, underlyingFormulas, Predicate.formula]

end Judgement

namespace GeneratorStability
open STLTableau.ExpansionRule

-- All rule schemas are inspected, including their next predicates.
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem finite_branch_subformula [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) {φ : Formula Var}
    (hφ : φ ∈ (Judgement.ofFinite B).underlyingFormulas) : φ ≼ p.formula := by
  classical
  cases hr <;>
    simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
      upperAlways, boundedAlways, upperEventually, boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [upperAlways_defer, upperAlways_check, boundedAlways_defer,
      boundedAlways_check, boundedAlways_finish, upperEventually_defer,
      upperEventually_check, boundedEventually_defer, boundedEventually_check,
      boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock] at hφ) <;>
    simp_all [Judgement.ofFinite, Judgement.underlyingFormulas,
      upperAlways_defer, upperAlways_check, boundedAlways_defer, boundedAlways_check,
      boundedAlways_finish, upperEventually_defer, upperEventually_check,
      boundedEventually_defer, boundedEventually_check, boundedEventually_finish,
      IntervalPredicate.formula, Formula.or, Formula.release, Formula.untimedUntil,
      Formula.eventually, Formula.always] <;>
    try solve_by_elim (maxDepth := 8) [Formula.IsSubformula.refl, Formula.IsSubformula.neg,
      Formula.IsSubformula.and_left, Formula.IsSubformula.and_right,
      Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]
  all_goals rcases hφ with rfl | rfl
  all_goals solve_by_elim (maxDepth := 8) [Formula.IsSubformula.refl, Formula.IsSubformula.neg,
    Formula.IsSubformula.and_left, Formula.IsSubformula.and_right,
    Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]

theorem finite_branch_stable [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition p.formula P) :
    (Judgement.ofFinite B).UnderlyingStable σ P :=
  Judgement.underlyingStable_of_subformulas σ P _ _ (fun _ h => finite_branch_subformula hr hB h) hst


open UnboundedClocked

-- Every next/reset predicate is inspected, without a current-only cutoff.
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem infinite_branch_subformula [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : Node Clock Var}
    (hB : B ∈ Bs) {φ : Formula Var}
    (hφ : φ ∈ (Judgement.ofUnbounded B).underlyingFormulas) : φ ≼ p.formula := by
  classical
  cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
      alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
      boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
      Node.lt, Node.gt, Judgement.ofUnbounded, Judgement.underlyingFormulas,
      UnboundedClocked.Predicate.formula, UnboundedClocked.formula,
      Formula.eventually, Formula.always] <;>
    try solve_by_elim (maxDepth := 8) [Formula.IsSubformula.refl, Formula.IsSubformula.neg,
      Formula.IsSubformula.and_left, Formula.IsSubformula.and_right,
      Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]
  all_goals rcases hφ with rfl | rfl
  all_goals solve_by_elim (maxDepth := 8) [Formula.IsSubformula.refl, Formula.IsSubformula.neg,
    Formula.IsSubformula.and_left, Formula.IsSubformula.and_right,
    Formula.IsSubformula.until_left, Formula.IsSubformula.until_right]

theorem infinite_branch_stable [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : Node Clock Var} (hB : B ∈ Bs)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition p.formula P) :
    (Judgement.ofUnbounded B).UnderlyingStable σ P :=
  Judgement.underlyingStable_of_subformulas σ P _ _
    (fun _ h => infinite_branch_subformula hr hB h) hst

theorem opening_branch_subformula [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (ψ : Formula Var)
    {φ : Formula Var}
    (hφ : φ ∈ (Judgement.ofUnbounded (opening c m kind a ψ)).underlyingFormulas) :
    φ ≼ UnboundedClocked.formula kind a ψ := by
  have he : φ = UnboundedClocked.formula kind a ψ := by
    simpa [opening, Judgement.ofUnbounded, Judgement.underlyingFormulas,
      UnboundedClocked.Predicate.formula] using hφ
  rw [he]
  exact .refl _

theorem opening_branch_stable [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : σ.StablePartition (UnboundedClocked.formula kind a φ) P) :
    (Judgement.ofUnbounded (opening c m kind a φ)).UnderlyingStable σ P :=
  Judgement.underlyingStable_of_subformulas σ P _ _
    (fun _ h => opening_branch_subformula c m kind a φ h) hst

end GeneratorStability
end STLTableau.Section3
