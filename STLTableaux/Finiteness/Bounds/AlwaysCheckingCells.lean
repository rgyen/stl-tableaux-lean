import STLTableaux.Finiteness.Derivation.Merging.AlwaysCheckingMerge

/-! An explicit bounded grouping of ordinary G regions. Cell membership uses
only unary age comparisons. Selecting extreme endpoints and realizing a
composable normalized transition are still separate obligations. -/
namespace STLTableau.Section4.Finiteness.DirectTracking

open scoped STL
variable {Clock Var : Type*}

/-- All subtraction is real subtraction, including possibly negative cutoffs. -/
def AgeCell (a w : ℝ) (j : ℕ) (age : ℝ) : Prop :=
  a - ((j : ℝ) + 1) * w < age ∧ age ≤ a - (j : ℝ) * w

/-- A nonnegative checking offset belongs to its ordinary half-open grid cell. -/
theorem ageCell_of_floor (I : BoundedTimeInterval) (age : ℝ)
    (hstart : age ≤ I.lower) :
    AgeCell I.lower (I.upper - I.lower)
      ⌊(I.lower - age) / (I.upper - I.lower)⌋₊ age := by
  have hw : 0 < I.upper - I.lower := sub_pos.mpr I.nonSingular
  have hx : 0 ≤ (I.lower - age) / (I.upper - I.lower) :=
    div_nonneg (sub_nonneg.mpr hstart) hw.le
  have hlo := (le_div_iff₀ hw).1 (Nat.floor_le hx)
  have hhi := (div_lt_iff₀ hw).1
    (Nat.lt_floor_add_one ((I.lower - age) / (I.upper - I.lower)))
  constructor <;> linarith

/-- At most floor(b / (b-a)) cells are occupied by nonnegative clock ages. -/
theorem ageCell_index_lt (I : BoundedTimeInterval) (j : ℕ) (age : ℝ)
    (hnonneg : 0 ≤ age) (hcell : AgeCell I.lower (I.upper - I.lower) j age) :
    j < ⌊I.upper / (I.upper - I.lower)⌋₊ := by
  have hw : 0 < I.upper - I.lower := sub_pos.mpr I.nonSingular
  have hbound : ((j + 1 : ℕ) : ℝ) * (I.upper - I.lower) ≤ I.upper := by
    dsimp [AgeCell] at hcell
    push_cast
    nlinarith [hcell.2]
  have hj : j + 1 ≤ ⌊I.upper / (I.upper - I.lower)⌋₊ :=
    Nat.le_floor ((le_div_iff₀ hw).2 hbound)
  omega

/-- The cell inequalities are exactly unary conditions on the left age. -/
theorem ageCell_iff_checking_left (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (l r : Marker) (I : BoundedTimeInterval) (j : ℕ) :
    AgeCell I.lower (I.upper - I.lower) j (α c : ℝ) ↔
      J.left + (j : ℝ) * (I.upper - I.lower) ≤ (checking J α c d l r I).left ∧
      (checking J α c d l r I).left <
        J.left + ((j : ℝ) + 1) * (I.upper - I.lower) := by
  dsimp [AgeCell, checking]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Same-cell ordinary regions have a STRICT checking join. Thus there is
no touching-endpoint marker side condition in this case. -/
theorem same_cell_strict_join (α : ClockValuation Clock)
    (c₁ d₁ c₂ : Clock) (I : BoundedTimeInterval) (j : ℕ)
    (hordinary : α d₁ ≤ α c₁)
    (h₁ : AgeCell I.lower (I.upper - I.lower) j (α c₁ : ℝ))
    (h₂ : AgeCell I.lower (I.upper - I.lower) j (α c₂ : ℝ)) :
    (α d₁ : ℝ) - (α c₂ : ℝ) < I.upper - I.lower := by
  have ho : (α d₁ : ℝ) ≤ (α c₁ : ℝ) := by exact_mod_cast hordinary
  dsimp [AgeCell] at h₁ h₂
  nlinarith [h₁.2, h₂.1]

/-- Once outer endpoints are selected, a same-cell ordinary merge needs
only the endpoint ordering premises; cell membership supplies the join. -/
theorem bounded_always_merge_same_cell (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ d₂ : Clock)
    (l₁ r₁ l₂ r₂ : Marker) (I : BoundedTimeInterval) (φ : Formula Var) (j : ℕ)
    (hordinary : α d₁ ≤ α c₁)
    (h₁ : AgeCell I.lower (I.upper - I.lower) j (α c₁ : ℝ))
    (h₂ : AgeCell I.lower (I.upper - I.lower) j (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp l₂ l₁] (α c₁ : ℝ))
    (hright : (α d₂ : ℝ) <[Marker.imp r₁ r₂] (α d₁ : ℝ)) :
    (STLTableau.predicateSatisfies σ J α (.bounded c₁ d₁ l₁ r₁ .always I φ) ∧
      STLTableau.predicateSatisfies σ J α (.bounded c₂ d₂ l₂ r₂ .always I φ)) ↔
      STLTableau.predicateSatisfies σ J α (.bounded c₁ d₂ l₁ r₂ .always I φ) :=
  bounded_always_merge σ J α c₁ d₁ c₂ d₂ l₁ r₁ l₂ r₂ I φ hleft
    (Or.inl (same_cell_strict_join α c₁ d₁ c₂ I j hordinary h₁ h₂)) hright

#print axioms ageCell_of_floor
#print axioms ageCell_index_lt
#print axioms ageCell_iff_checking_left
#print axioms same_cell_strict_join
#print axioms bounded_always_merge_same_cell

end STLTableau.Section4.Finiteness.DirectTracking
