import STLTableaux.Finiteness.Derivation.Derivation
import STLTableaux.Finiteness.Bounds.RightClockAge
import STLTableaux.Semantics.Invariants.NumericInvariant

/-! Local preservation of an unrelated pending requirement's right clock and
the numeric age window for `↑↓` predicates. These facts do not assign
predicates to source truth intervals or prove a global ownership invariant. -/
namespace STLTableau.Section4.Finiteness.RightClockContext
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- A right clock used by the pending context and absent from the expanded
source cannot be reset anywhere in that actual fresh raw branch. -/
theorem freshFor_excludes_context_reset (p : Predicate Clock Var) (B Γ : MixedJ Clock Var)
    (h : FreshFor p B Γ) (d : Clock) (hdΓ : d ∈ syntaxClocks Γ)
    (hdp : d ∉ syntaxClocks (.predicate p)) : d ∉ resetNames B := by
  intro hdB
  exact Set.disjoint_left.1 h ⟨hdB,hdp⟩ (Or.inl hdΓ)

theorem value_none_of_not_reset (R : ClockResetSet Clock) (d : Clock)
    (h : d ∉ R.clocks) : R.value d = none := by
  cases hr : R.value d with
  | none => rfl
  | some a => exact False.elim (h ⟨a,hr⟩)

theorem not_reset_of_value_none (R : ClockResetSet Clock) (d : Clock)
    (h : R.value d = none) : d ∉ R.clocks := by
  rintro ⟨a,ha⟩
  rw [h] at ha
  cases ha

/-- Absence of a right clock from `resetNames J` is equivalent to
`NoRightReset`, including under nested next and reset scopes. -/
theorem noRightReset_iff_not_resetNames (J : MixedJ Clock Var) (d : Clock) :
    RightClockAge.NoRightReset d J ↔ d ∉ resetNames J := by
  induction J with
  | terminal => simp [resetNames,RightClockAge.NoRightReset]
  | clock => simp [resetNames,RightClockAge.NoRightReset]
  | marker => simp [resetNames,RightClockAge.NoRightReset]
  | predicate => simp [resetNames,RightClockAge.NoRightReset]
  | next J ih => exact ih
  | conj J K ih ig =>
    simpa only [resetNames,RightClockAge.NoRightReset,Set.mem_union,not_or] using and_congr ih ig
  | reset R J ih =>
    change (R.value d = none ∧ RightClockAge.NoRightReset d J) ↔
      ¬ (d ∈ R.clocks ∨ d ∈ resetNames J)
    rw [not_or,← ih]
    exact and_congr ⟨not_reset_of_value_none R d,value_none_of_not_reset R d⟩ Iff.rfl

theorem freshFor_context_noRightReset (p : Predicate Clock Var) (B Γ : MixedJ Clock Var)
    (h : FreshFor p B Γ) (d : Clock) (hdΓ : d ∈ syntaxClocks Γ)
    (hdp : d ∉ syntaxClocks (.predicate p)) : RightClockAge.NoRightReset d B :=
  (noRightReset_iff_not_resetNames B d).2 (freshFor_excludes_context_reset p B Γ h d hdΓ hdp)

/-- Endpoint preservation through all real reset/next scopes of the other
branch, obtained from whole pending-context freshness rather than assumed. -/
theorem freshFor_context_endpointAlong {D : Set ℝ} (P : IntervalPartition D)
    (p : Predicate Clock Var) (B Γ : MixedJ Clock Var) (h : FreshFor p B Γ)
    (d : Clock) (hdΓ : d ∈ syntaxClocks Γ) (hdp : d ∉ syntaxClocks (.predicate p))
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (u : ℝ) :
    RightClockAge.EndpointAlong P d (RightClockAge.endpoint d u α) α k u B :=
  RightClockAge.endpointAlong_of_noRightReset P d _ B
    (freshFor_context_noRightReset p B Γ h d hdΓ hdp) α k u rfl

/-- A `↑↓` source's own right clock is not reset by any of its actual
finite or unbounded propagation branches. This complements context freshness:
it covers the clock that does occur in the expanded source itself. -/
private theorem bounded_noRightReset_of_eq [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hp : p = .bounded c d b q kind I φ) : RightClockAge.NoRightReset d B := by
  cases h with
  | @finite p₀ R rule B₀ member =>
    cases p₀ with
    | plain ψ => cases hp
    | upper c m kind I φ => cases hp
    | bounded c₀ d₀ b₀ q₀ kind₀ I₀ φ₀ =>
      simp only [Predicate.ofFinite,Predicate.bounded.injEq] at hp
      obtain ⟨rfl,rfl,rfl,rfl,rfl,hI,rfl⟩ := hp
      cases hI
      cases rule with
      | boundedAlways c d b q I φ hcd =>
        exact RightClockAge.finite_bounded_no_right_reset .always _ _ hcd _ _ _ _ B₀ member
      | boundedEventually c d b q I φ hcd =>
        exact RightClockAge.finite_bounded_no_right_reset .eventually _ _ hcd _ _ _ _ B₀ member
  | @infinite p₀ Bs rule B₀ member =>
    cases p₀ with
    | upper c m kind a φ => cases hp
    | bounded c₀ d₀ b₀ q₀ kind₀ a₀ φ₀ =>
      simp only [Predicate.ofUnbounded,Predicate.bounded.injEq] at hp
      obtain ⟨rfl,rfl,rfl,rfl,rfl,hI,rfl⟩ := hp
      cases hI
      cases rule with
      | boundedAlways c d b q a φ hcd =>
        exact RightClockAge.unbounded_bounded_no_right_reset .always _ _ hcd _ _ _ _ B₀ member
      | boundedEventually c d b q a φ hcd =>
        exact RightClockAge.unbounded_bounded_no_right_reset .eventually _ _ hcd _ _ _ _ B₀ member
  | opening c m kind a φ => cases hp

theorem owned_bounded_noRightReset [DecidableEq Clock]
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (B : MixedJ Clock Var)
    (h : RawBranch (.bounded c d b q kind I φ) B) : RightClockAge.NoRightReset d B :=
  bounded_noRightReset_of_eq h c d b q kind I φ rfl

theorem owned_bounded_endpointAlong [DecidableEq Clock] {D : Set ℝ}
    (P : IntervalPartition D) (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (B : MixedJ Clock Var)
    (h : RawBranch (.bounded c d b q kind I φ) B)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (u : ℝ) :
    RightClockAge.EndpointAlong P d (RightClockAge.endpoint d u α) α k u B :=
  RightClockAge.endpointAlong_of_noRightReset P d _ B
    (owned_bounded_noRightReset c d b q kind I φ B h) α k u rfl

private theorem marked_le {m : Marker} {x y : ℝ} (h : x <[m] y) : x ≤ y := by
  rcases h with h | ⟨h,_⟩
  · exact h.le
  · exact h.le

/-- The finite G/F numeric invariants bound the actual right-clock age.
For G use its right-age upper clause; for F compose d≤c with c≤sup I. -/
theorem right_age_le_upper_of_numeric (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : BoundedTimeInterval)
    (φ : Formula Var)
    (h : Predicate.Numeric J α (.bounded c d b q kind (.bounded I) φ)) :
    (α d : ℝ) ≤ I.upper := by
  cases kind with
  | always => exact marked_le h.1.2
  | eventually => exact (marked_le h.1.2).trans (marked_le h.1.1)

/-- The endpoint window is derived from the actual numeric invariant; no
endpoint-origin or window bound is included among the hypotheses. -/
theorem endpoint_window_of_numeric (J : MarkedInterval) (α : ClockValuation Clock)
    (u : ℝ) (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : BoundedTimeInterval)
    (φ : Formula Var)
    (h : Predicate.Numeric J α (.bounded c d b q kind (.bounded I) φ)) :
    u-I.upper ≤ RightClockAge.endpoint d u α ∧ RightClockAge.endpoint d u α ≤ u := by
  have hb := right_age_le_upper_of_numeric J α c d b q kind I φ h
  have hn := (α d).coe_nonneg
  simp only [RightClockAge.endpoint]
  constructor <;> linarith

/-- State-form instance at the real valuation after that state's own reset map.
This uses actual local membership and actual EvaluatedNumeric, not a valuation
chosen independently of the judgement's reset scope. -/
theorem state_bounded_endpoint_window (S : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c d : Clock) (b q : Marker) (kind : TemporalKind) (I : BoundedTimeInterval)
    (φ : Formula Var) (hp : Local.predicate (.bounded c d b q kind (.bounded I) φ) ∈ S.locals)
    (h : S.EvaluatedNumeric σ P α k) :
    let u := (P.interval ⟨k.1,hk⟩).left
    u-I.upper ≤ RightClockAge.endpoint d u (S.resets.apply α) ∧
      RightClockAge.endpoint d u (S.resets.apply α) ≤ u :=
  endpoint_window_of_numeric _ _ _ c d b q kind I φ (h (.predicate _) hp hk)

end STLTableau.Section4.Finiteness.RightClockContext
