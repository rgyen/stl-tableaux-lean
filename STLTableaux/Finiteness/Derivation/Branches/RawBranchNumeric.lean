import STLTableaux.Finiteness.Derivation.Derivation
import STLTableaux.Rules.Invariants.NumericBranchPreservation

/-! Soundness of expansion branches under the numeric invariant and
preservation of that invariant before normalization. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- A satisfied expansion branch implies its source predicate under the
source's numeric invariant. -/
theorem RawBranch.numeric_sound [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α)
    (hs : Judgement.holds σ P α k B) : Judgement.holds σ P α k (.predicate p) := by
  cases h with
  | @finite p₀ R rule B₀ member =>
    apply (Judgement.holds_ofFinite σ P α k (.predicate p₀)).2
    apply STLTableau.rule_sound_without_past rule σ P α k
    · intro hk
      have hn := hi hk
      cases p₀ with
      | plain => trivial
      | upper c b kind I φ => cases kind with
        | always => exact hn.2
        | eventually => exact hn.1
      | bounded c d b q kind I φ => cases kind with
        | always => exact ⟨hn.2,hn.1.1⟩
        | eventually => exact hn.1
    · exact ⟨B₀,member,(Judgement.holds_ofFinite σ P α k B₀).1 hs⟩
  | @infinite p₀ Bs rule B₀ member =>
    apply (Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).2
    apply UnboundedClocked.rule_sound_without_past rule σ P α k
    · intro hk
      have hn := hi hk
      cases p₀ with
      | upper c b kind a φ => cases kind <;> exact hn
      | bounded c d b q kind a φ => cases kind <;> exact hn
    · exact ⟨B₀,member,(Judgement.holds_ofUnbounded σ P α k B₀).1 hs⟩
  | opening c m kind a φ =>
    have hp := (UnboundedClocked.opening_correct σ P α k c kind a φ).2
      ⟨m,(Judgement.holds_ofUnbounded σ P α k _).1 hs⟩
    exact (Judgement.holds_ofUnbounded σ P α k _).2 hp

/-- Every actual raw branch preserves the numeric invariant in its real next
and reset scopes, using only source numeric clauses and non-predicate guards.
In particular, the conclusion is derived rather than supplied per output node. -/
theorem RawBranch.numeric_preserves [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α)
    (hs : Judgement.nonPredicateHolds σ P α k B) :
    Judgement.EvaluatedNumeric σ P α k B := by
  cases h with
  | @finite p₀ R rule B₀ member =>
    have hlegacy : ∀ hk : k.1 < P.size,
        IntervalPredicate.Invariant (P.interval ⟨k.1,hk⟩) α p₀ := by
      intro hk
      have hn := hi hk
      cases p₀ with
      | plain => trivial
      | upper => exact hn.1
      | bounded => exact hn.1
    have hp := STLTableau.branch_nonpast_parts rule B₀ member σ P α k hlegacy
      ((Judgement.nonPredicate_ofFinite B₀ σ P α k).1 hs)
    exact Judgement.numeric_ofFinite_of_parts B₀ σ P α k hp.1 hp.2
  | @infinite p₀ Bs rule B₀ member =>
    have hsource : UnboundedClocked.EvaluatedNonpast σ P α k (.predicate p₀) := by
      intro hk
      have hn := hi hk
      cases p₀ with
      | upper c b kind a φ => cases kind <;> exact hn
      | bounded c d b q kind a φ => cases kind <;> exact hn
    have hp := UnboundedClocked.branch_nonpast_preserves rule B₀ member σ P α k hsource
      ((Judgement.nonPredicate_ofUnbounded B₀ σ P α k).1 hs)
    exact (Judgement.numeric_ofUnbounded B₀ σ P α k).2 hp
  | opening c m kind a φ =>
    have hp := UnboundedClocked.opening_nonpast_preserves σ P α k c m kind a φ
      ((Judgement.nonPredicate_ofUnbounded _ σ P α k).1 hs)
    exact (Judgement.numeric_ofUnbounded _ σ P α k).2 hp

end STLTableau.Section4.Finiteness
