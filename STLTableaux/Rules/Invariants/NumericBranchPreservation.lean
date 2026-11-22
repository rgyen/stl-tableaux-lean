import STLTableaux.Closure.Normalization.NumericAlphaTransport
import STLTableaux.Closure.Normalization.NonPredicateAlphaTransport
import STLTableaux.Closure.Normalization.NumericFiniteNormalization
import STLTableaux.Closure.Normalization.NumericInfiniteNormalization
import STLTableaux.Closure.Normalization.NonPredicateFiniteNormalization
import STLTableaux.Closure.Normalization.NonPredicateInfiniteNormalization

namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace TransitionForm

theorem underReset_numeric (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset Λ).EvaluatedNumeric σ P α k ↔ F.EvaluatedNumeric σ P (Λ.apply α) k := by
  simp only [underReset,EvaluatedNumeric,StateForm.EvaluatedNumeric,ClockResetSet.apply_union_eq_comp]

theorem underReset_nonPredicate (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock)
    (hg : F.current.guards = ∅) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset Λ).nonPredicateHolds σ P α k ↔ F.nonPredicateHolds σ P (Λ.apply α) k := by
  simp only [underReset,nonPredicateHolds,StateForm.nonPredicateHolds,hg,Set.mem_empty_iff_false,
    IsEmpty.forall_iff,implies_true,true_and,ClockResetSet.apply_union_eq_comp]
end TransitionForm
namespace NumericBranch

private theorem finite_source_legacy (p : IntervalPredicate Clock Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (hi : (Predicate.ofFinite p).Numeric J α) :
    IntervalPredicate.Invariant J α p := by
  cases p with
  | plain => trivial
  | upper => exact hi.1
  | bounded => exact hi.1

private theorem finite_source_direct (p : IntervalPredicate Clock Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (hi : (Predicate.ofFinite p).Numeric J α) :
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
  | plain => trivial
  | upper c b kind I φ => cases kind with
    | always => exact hi.2
    | eventually => exact hi.1
  | bounded c d b q kind I φ => cases kind with
    | always => exact ⟨hi.2,hi.1.1⟩
    | eventually => exact hi.1

theorem finite_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteFinite.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.nonPredicateHolds σ P α k) : B.EvaluatedNumeric σ P α k := by
  obtain ⟨p₀,R,raw,F,rfl,hr,hm,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteFinite.branch_nonPredicate_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  have hraw := (hguard σ P α k).1 hs
  have hparts := STLTableau.branch_nonpast_parts hr raw hm σ P (Λ.apply α) k
    (fun hk => finite_source_legacy p₀ _ _ (hi hk))
    ((Judgement.nonPredicate_ofFinite raw σ P (Λ.apply α) k).1 hraw)
  obtain ⟨G,hG,hnum⟩ := ConcreteFinite.branch_numeric_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  exact (hnum σ P α k).2
    (Judgement.numeric_ofFinite_of_parts raw σ P (Λ.apply α) k hparts.1 hparts.2)

theorem infinite_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteInfinite.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.nonPredicateHolds σ P α k) : B.EvaluatedNumeric σ P α k := by
  obtain ⟨p₀,Bs,raw,F,rfl,hr,hm,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteInfinite.branch_nonPredicate_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  have hraw := (Judgement.nonPredicate_ofUnbounded raw σ P (Λ.apply α) k).1
    ((hguard σ P α k).1 hs)
  have hi' : UnboundedClocked.EvaluatedNonpast σ P (Λ.apply α) k (.predicate p₀) := by
    intro hk
    have h := hi hk
    cases p₀ with
    | upper c b kind a φ => cases kind <;> exact h
    | bounded c d b q kind a φ => cases kind <;> exact h
  have hpres := UnboundedClocked.branch_nonpast_preserves hr raw hm σ P (Λ.apply α) k hi' hraw
  obtain ⟨G,hG,hnum⟩ := ConcreteInfinite.branch_numeric_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  exact (hnum σ P α k).2 ((Judgement.numeric_ofUnbounded raw σ P (Λ.apply α) k).2 hpres)

theorem opening_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteOpening.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : B.nonPredicateHolds σ P α k) : B.EvaluatedNumeric σ P α k := by
  obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteInfinite.opening_nonPredicate_normalization c m kind a φ Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  have hraw := (Judgement.nonPredicate_ofUnbounded _ σ P (Λ.apply α) k).1
    ((hguard σ P α k).1 hs)
  have hpres := UnboundedClocked.opening_nonpast_preserves σ P (Λ.apply α) k c m kind a φ hraw
  obtain ⟨G,hG,hnum⟩ := ConcreteInfinite.opening_numeric_normalization c m kind a φ Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  exact (hnum σ P α k).2 ((Judgement.numeric_ofUnbounded _ σ P (Λ.apply α) k).2 hpres)

theorem mixed_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.nonPredicateHolds σ P α k) : B.EvaluatedNumeric σ P α k := by
  rcases hb with h | h | h
  · exact finite_preserves h σ P α k hi hs
  · exact infinite_preserves h σ P α k hi hs
  · exact opening_preserves h σ P α k hs

theorem contextual_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.nonPredicateHolds σ P α k) : B.EvaluatedNumeric σ P α k := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  have hg := ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hR)
  have hA := (A.underReset_nonPredicate Λ hg σ P α k).1 hs
  have hsR := (ha.nonPredicate σ P (Λ.apply α) k).1 hA
  have hnR := mixed_preserves hR σ P (Λ.apply α) k
    (by simpa only [ClockResetSet.apply_empty] using hi) hsR
  exact (A.underReset_numeric Λ σ P α k).2
    ((ha.evaluatedNumeric σ P (Λ.apply α) k).2 hnR)
theorem finite_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteFinite.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.holds σ P α k) : Judgement.holds σ P (Λ.apply α) k (.predicate p) := by
  obtain ⟨p₀,R,raw,F,rfl,hr,hm,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteFinite.branch_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  have hraw := (hguard σ P α k).1 hs
  exact (Judgement.holds_ofFinite σ P (Λ.apply α) k (.predicate p₀)).2
    (STLTableau.rule_sound_without_past hr σ P (Λ.apply α) k
      (fun hk => by
        have h := finite_source_direct p₀ _ _ (hi hk)
        cases p₀ with
        | plain => exact h
        | upper c b kind I φ => cases kind <;> exact h
        | bounded c d b q kind I φ => cases kind <;> exact h) ⟨raw,hm,hraw⟩)

theorem infinite_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteInfinite.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.holds σ P α k) : Judgement.holds σ P (Λ.apply α) k (.predicate p) := by
  obtain ⟨p₀,Bs,raw,F,rfl,hr,hm,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteInfinite.branch_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  have hraw := (hguard σ P α k).1 hs
  apply (Judgement.holds_ofUnbounded σ P (Λ.apply α) k (.predicate p₀)).2
  apply UnboundedClocked.rule_sound_without_past hr σ P (Λ.apply α) k _ ⟨raw,hm,hraw⟩
  intro hk
  have h := hi hk
  cases p₀ with
  | upper c b kind a φ => cases kind <;> exact h
  | bounded c d b q kind a φ => cases kind <;> exact h

theorem opening_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteOpening.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : B.holds σ P α k) : Judgement.holds σ P (Λ.apply α) k (.predicate p) := by
  obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := hb
  obtain ⟨G,hG,hguard⟩ := ConcreteInfinite.opening_normalization c m kind a φ Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  exact (Judgement.holds_ofUnbounded σ P (Λ.apply α) k (.plain _)).2
    ((UnboundedClocked.opening_correct σ P (Λ.apply α) k c kind a φ).2
      ⟨m,(hguard σ P α k).1 hs⟩)

theorem mixed_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.holds σ P α k) : Judgement.holds σ P (Λ.apply α) k (.predicate p) := by
  rcases hb with h | h | h
  · exact finite_sound h σ P α k hi hs
  · exact infinite_sound h σ P α k hi hs
  · exact opening_sound h σ P α k hs

/-- Local faithful soundness uses the derived numeric clauses, never a
past-cover or branch-operand satisfaction premise. -/
theorem contextual_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α))
    (hs : B.holds σ P α k) : Judgement.holds σ P (Λ.apply α) k (.predicate p) := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  have hg := ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hR)
  have hA := (A.underReset_holds Λ hg σ P α k).1 hs
  have hsR := (ha.holds σ P (Λ.apply α) k).1 hA
  simpa only [ClockResetSet.apply_empty] using mixed_sound hR σ P (Λ.apply α) k
    (by simpa only [ClockResetSet.apply_empty] using hi) hsR
end NumericBranch
end STLTableau.Section3
