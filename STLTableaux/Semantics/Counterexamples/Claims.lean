import STLTableaux.Semantics.IntervalSemantics

/-! Statements about splitting interval predicates with weakened marker and
clock premises. The statements use either a fixed marker or one chosen from
the context. Their counterexamples use `↑↓` `□` predicates,
natural-number clocks, and one signal variable. -/
namespace STLTableau.Claims
open scoped STL

def opening (c : Nat) (b : Marker) (I : BoundedTimeInterval)
    (φ : Formula Unit) : Judgement Nat Unit :=
  ⟦c ↦ᶜ 0⟧ ·ⱼ (.predicate (.upper c b .always I φ) ∧ⱼ lty[b])

def split (c d : Nat) (b m : Marker) (I : BoundedTimeInterval)
    (φ : Formula Unit) : Judgement Nat Unit :=
  (⟦d ↦ᶜ 0⟧ ·ⱼ (.predicate (.bounded c d b (¬ₘ m) .always I φ) ∧ⱼ lty[m])) ∧ⱼ
    .predicate (.plain (□[(I : TimeInterval)] φ))

/-- The always instance of printed part (1), with its marker fixed before
the semantic context. Even this instance would follow from the full claim. -/
def PrintedOpeningFixedMarker : Prop :=
  ∀ (c : Nat) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Unit),
    Equivalent (.predicate (.plain (□[(I : TimeInterval)] φ))) (opening c b I φ)

/-- The always instance of printed part (2), including distinct source and
fresh reset clocks. -/
def PrintedSplitFixedMarker : Prop :=
  ∀ (c d : Nat) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Unit),
    c ≠ d → Equivalent (.predicate (.upper c b .always I φ)) (split c d b m I φ)

/-- A more generous reading of part (2) permits selecting the declaring
marker separately in every semantic context. This too is false. -/
def PrintedSplitChosenMarker : Prop :=
  ∀ (c d : Nat) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Unit),
    c ≠ d → ∀ (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
      (α : ClockValuation Nat) (k : Judgement.Position P),
      satisfies σ P α k (.predicate (.upper c b .always I φ)) ↔
        ∃ m : Marker, satisfies σ P α k (split c d b m I φ)

end STLTableau.Claims
