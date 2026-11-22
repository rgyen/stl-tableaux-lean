import STLTableaux.Rules.Unbounded.UnboundedAlwaysCompleteness
import STLTableaux.Rules.Unbounded.UnboundedEventuallyCompleteness
import STLTableaux.Rules.Unbounded.UnboundedPreservation

/-! Correctness and invariant preservation for the four unbounded clocked
rule families. Rule opening is covered by `opening_correct`. -/
namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

def Predicate.formula : Predicate Clock Var → Formula Var
  | .upper _ _ kind a φ | .bounded _ _ _ _ kind a φ =>
      STLTableau.UnboundedClocked.formula kind a φ

inductive ConcreteRule [DecidableEq Clock] :
    Predicate Clock Var → List (Node Clock Var) → Prop where
  | upperAlways (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.upper c b .always a φ) (upperAlwaysBranches c d b a φ)
  | boundedAlways (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.bounded c d b q .always a φ) (boundedAlwaysBranches c d b q a φ)
  | upperEventually (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.upper c b .eventually a φ) (upperEventuallyBranches c d b a φ)
  | boundedEventually (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.bounded c d b q .eventually a φ) (boundedEventuallyBranches c d b q a φ)

/-- Unbounded case of Theorem 3.13 (rule soundness) under the source invariant. -/
theorem rule_sound [DecidableEq Clock] {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hs : BranchSatisfied Bs σ P α k) : Node.holds σ P α k (.predicate p) := by
  cases hr with
  | upperAlways c d b a φ hcd => exact upperAlways_sound σ P α k c d b a φ hcd hi hs
  | boundedAlways c d b q a φ _ => exact boundedAlways_sound σ P α k c d b q a φ hi hs
  | upperEventually c d b a φ hcd => exact upperEventually_sound σ P α k c d b a φ hcd hs
  | boundedEventually c d b q a φ hcd => exact boundedEventually_sound σ P α k c d b q a φ hcd hs

/-- Unbounded case of Theorem 3.13 (rule completeness). The partition is fully
stable for the source formula, and the source satisfies its full invariant. -/
theorem rule_complete [DecidableEq Clock] {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : Node.holds σ P α k (.predicate p)) : BranchSatisfied Bs σ P α k := by
  cases hr with
  | upperAlways c d b a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact upperAlways_complete σ P α k c d b a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ)))) ) hs
  | boundedAlways c d b q a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact boundedAlways_complete σ P α k c d b q a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ)))) ) hs
  | upperEventually c d b a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact upperEventually_complete σ P α k c d b a φ hcd hi
        (fun j => hst j φ (.until_right (.refl φ))) hs
  | boundedEventually c d b q a φ _ =>
      simp only [Predicate.formula, formula] at hst
      exact boundedEventually_complete σ P α k c d b q a φ hi
        (fun j => hst j φ (.until_right (.refl φ))) hs

theorem rule_correct [DecidableEq Clock] {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) :
    Node.holds σ P α k (.predicate p) ↔ BranchSatisfied Bs σ P α k :=
  ⟨rule_complete hr σ P α k hi hst, rule_sound hr σ P α k hi⟩

/-- The unbounded soundness claim also omits past-cover, without defining
a second named invariant. The remaining positional/nonemptiness clauses
are exactly those of the unified invariant. -/
theorem rule_sound_without_past [DecidableEq Clock]
    {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size,
      let J := P.interval ⟨k.1,hk⟩
      match p with
      | .upper c b .always a _ | .bounded c _ b _ .always a _ =>
          (α c : ℝ) <[Marker.imp b J.leftBoundary] (a : ℝ)
      | .upper c b .eventually _ _ =>
          (0 : ℝ) <[Marker.conj b J.rightBoundary]
            ((α c : ℝ) + J.right - J.left)
      | .bounded c d b q .eventually _ _ =>
          (α d : ℝ) <[Marker.conj b q] (α c : ℝ))
    (hs : BranchSatisfied Bs σ P α k) : Node.holds σ P α k (.predicate p) := by
  cases hr with
  | upperAlways c d b a φ hcd => exact upperAlways_sound σ P α k c d b a φ hcd hi hs
  | boundedAlways c d b q a φ _ => exact boundedAlways_sound σ P α k c d b q a φ hi hs
  | upperEventually c d b a φ hcd => exact upperEventually_sound σ P α k c d b a φ hcd hs
  | boundedEventually c d b q a φ hcd => exact boundedEventually_sound σ P α k c d b q a φ hcd hs

/-- Proposition 3.14, now also for unbounded timing.
The very same branch witnesses satisfaction and the unified invariant
under every actual reset/next evaluation context. -/
theorem rule_complete_preserving [DecidableEq Clock]
    {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : Node.holds σ P α k (.predicate p)) : CertifiedBranchSatisfied Bs σ P α k := by
  cases hr with
  | upperAlways c d b a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact upperAlways_complete_preserving σ P α k c d b a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ))))) hs
  | boundedAlways c d b q a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact boundedAlways_complete_preserving σ P α k c d b q a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ))))) hs
  | upperEventually c d b a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact upperEventually_complete_preserving σ P α k c d b a φ hcd hi
        (fun j => hst j φ (.until_right (.refl φ))) hs
  | boundedEventually c d b q a φ hcd =>
      simp only [Predicate.formula, formula] at hst
      exact boundedEventually_complete_preserving σ P α k c d b q a φ hcd hi
        (fun j => hst j φ (.until_right (.refl φ))) hs

theorem rule_correct_preserving [DecidableEq Clock]
    {p : Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : ConcreteRule p Bs) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) :
    Node.holds σ P α k (.predicate p) ↔ CertifiedBranchSatisfied Bs σ P α k := by
  constructor
  · exact rule_complete_preserving hr σ P α k hi hst
  · rintro ⟨B, hB, h, _⟩
    exact rule_sound hr σ P α k hi ⟨B, hB, h⟩

end STLTableau.UnboundedClocked
