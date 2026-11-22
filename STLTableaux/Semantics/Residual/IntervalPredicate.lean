/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Stability.Stability

/-!
# Clocked interval predicates

Syntax and scopes of interval predicates (Definitions 3.1 and 3.2), with
the residual satisfaction relation used by the bounded-rule development.
-/

namespace STLTableau

/-- A clock valuation assigns a nonnegative real to every clock. -/
abbrev ClockValuation (Clock : Type*) := Clock → NNReal

/-- A scope records the endpoints and markers of Definition 3.2. Its
endpoints may be inverted after clock subtraction. -/
structure Scope where
  leftBoundary : Marker
  left : ℝ
  right : ℝ
  rightBoundary : Marker

namespace Scope

/-- Regard a scope as a marked interval specification when reusing interval
membership and set-theoretic results. This does not assert nonemptiness. -/
def toMarkedInterval (S : Scope) : MarkedInterval :=
  ⟨S.left, S.right, S.leftBoundary, S.rightBoundary⟩

/-- The real points denoted by a scope quadruple. -/
def carrier (S : Scope) : Set ℝ := S.toMarkedInterval.carrier

instance : Membership ℝ Scope := ⟨fun S t => t ∈ S.carrier⟩

@[simp] theorem mem_carrier {S : Scope} {t : ℝ} : t ∈ S.carrier ↔ t ∈ S := Iff.rfl

@[simp] theorem mem_toMarkedInterval {S : Scope} {t : ℝ} :
    t ∈ S.toMarkedInterval ↔ t ∈ S := Iff.rfl

/-- Use the endpoints and markers of a marked interval as a scope. -/
def ofMarkedInterval (I : MarkedInterval) : Scope :=
  ⟨I.leftBoundary, I.left, I.right, I.rightBoundary⟩

@[simp] theorem toMarkedInterval_ofMarkedInterval (I : MarkedInterval) :
    (ofMarkedInterval I).toMarkedInterval = I := rfl

@[simp] theorem mem_ofMarkedInterval {I : MarkedInterval} {t : ℝ} :
    t ∈ ofMarkedInterval I ↔ t ∈ I := by
  rfl

end Scope

/-- The two temporal operators carried by clocked interval predicates. -/
inductive TemporalKind where
  | always
  | eventually
  deriving DecidableEq, Repr

/-- The interval-predicate forms of Definition 3.1. Clocked predicates here
have bounded timing intervals. -/
inductive IntervalPredicate (Clock Var : Type*) where
  | plain (φ : Formula Var)
  | upper (clock : Clock) (leftBoundary : Marker) (kind : TemporalKind)
      (timing : BoundedTimeInterval) (φ : Formula Var)
  | bounded (leftClock rightClock : Clock) (leftBoundary rightBoundary : Marker)
      (kind : TemporalKind) (timing : BoundedTimeInterval) (φ : Formula Var)

/-- Notation for one-clock and two-clock interval predicates. -/
scoped[STL] notation:70 "↑[" c "," b "]" "□[" I "]" φ:70 =>
  STLTableau.IntervalPredicate.upper c b STLTableau.TemporalKind.always I φ
scoped[STL] notation:70 "↑[" c "," b "]" "◇[" I "]" φ:70 =>
  STLTableau.IntervalPredicate.upper c b STLTableau.TemporalKind.eventually I φ
scoped[STL] notation:70 "↑↓[" c "," d "," b "," b' "]" "□[" I "]" φ:70 =>
  STLTableau.IntervalPredicate.bounded c d b b' STLTableau.TemporalKind.always I φ
scoped[STL] notation:70 "↑↓[" c "," d "," b "," b' "]" "◇[" I "]" φ:70 =>
  STLTableau.IntervalPredicate.bounded c d b b' STLTableau.TemporalKind.eventually I φ

open scoped STL

namespace IntervalPredicate

variable {Clock Var : Type*}

/-- Clock variables occurring in an interval predicate, as a set. Unlike
`clocks`, this definition needs no decidable equality. -/
@[simp] def clockSet : IntervalPredicate Clock Var → Set Clock
  | .plain _ => ∅
  | .upper c _ _ _ _ => {c}
  | .bounded c d _ _ _ _ _ => {c, d}

/-- The STL formula represented by an interval predicate. -/
def formula : IntervalPredicate Clock Var → Formula Var
  | .plain φ => φ
  | .upper _ _ .always I φ => □[I] φ
  | .upper _ _ .eventually I φ => ◇[I] φ
  | .bounded _ _ _ _ .always I φ => □[I] φ
  | .bounded _ _ _ _ .eventually I φ => ◇[I] φ

/-- The clock variables that occur in an interval predicate. -/
def clocks [DecidableEq Clock] : IntervalPredicate Clock Var → Finset Clock
  | .plain _ => ∅
  | .upper c _ _ _ _ => {c}
  | .bounded c d _ _ _ _ _ => {c, d}

/-- Definition 3.2 (scope) for unclocked predicates and clocked predicates in the `↑` and
`↑↓` forms. -/
def scope (J : MarkedInterval) (α : ClockValuation Clock) :
    IntervalPredicate Clock Var → Scope
  | .plain _ => Scope.ofMarkedInterval J
  | .upper c leftBoundary _ _ _ =>
      ⟨leftBoundary, J.left - α c, J.right, J.rightBoundary⟩
  | .bounded c d leftBoundary rightBoundary _ _ _ =>
      ⟨leftBoundary, J.left - α c, J.left - α d, rightBoundary⟩

@[simp] theorem scope_plain (J : MarkedInterval) (α : ClockValuation Clock)
    (φ : Formula Var) :
    scope J α (.plain φ) = Scope.ofMarkedInterval J := rfl

@[simp] theorem scope_up_always (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    scope J α (↑[c, b] □[I] φ) =
      ⟨b, J.left - α c, J.right, J.rightBoundary⟩ := rfl

@[simp] theorem scope_up_eventually (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    scope J α (↑[c, b] ◇[I] φ) =
      ⟨b, J.left - α c, J.right, J.rightBoundary⟩ := rfl

@[simp] theorem scope_up_down_always (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    scope J α (↑↓[c, d, b, b'] □[I] φ) =
      ⟨b, J.left - α c, J.left - α d, b'⟩ := rfl

@[simp] theorem scope_up_down_eventually (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    scope J α (↑↓[c, d, b, b'] ◇[I] φ) =
      ⟨b, J.left - α c, J.left - α d, b'⟩ := rfl

/-- Scope depends only on the clocks occurring in the predicate. -/
theorem scope_eq_of_agree [DecidableEq Clock] {J : MarkedInterval}
    {α β : ClockValuation Clock} {p : IntervalPredicate Clock Var}
    (hagree : ∀ c ∈ p.clocks, α c = β c) : scope J α p = scope J β p := by
  cases p with
  | plain φ => rfl
  | upper c b kind I φ =>
      have hc := hagree c (by simp [clocks])
      simp [scope, hc]
  | bounded c d b b' kind I φ =>
      have hc := hagree c (by simp [clocks])
      have hd := hagree d (by simp [clocks])
      simp [scope, hc, hd]

/-- An `↑` scope contains the current interval exactly when its coincident
left endpoint includes every point included by the current left marker. -/
theorem current_subset_upperScope_iff (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker)
    (hJ : J.carrier.Nonempty) :
    J.carrier ⊆ (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier ↔
      ((α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes) := by
  constructor
  · intro hsub hz hm
    have h := hsub (J.left_mem hJ hm)
    change (J.left - (α c : ℝ) < J.left ∨
      (J.left - (α c : ℝ) = J.left ∧ b.Includes)) ∧ _ at h
    simpa [hz] using h.1
  · intro hm x hx
    change (J.left - (α c : ℝ) < x ∨
      (J.left - (α c : ℝ) = x ∧ b.Includes)) ∧ _
    refine ⟨?_, hx.2⟩
    by_cases hz : (α c : ℝ) = 0
    · rcases hx.1 with hlt | ⟨heq, hinc⟩
      · exact Or.inl (by simpa [hz] using hlt)
      · exact Or.inr ⟨by simpa [hz] using heq, hm hz hinc⟩
    · have hp : 0 < (α c : ℝ) := lt_of_le_of_ne (α c).coe_nonneg (Ne.symm hz)
      have hxleft := MarkedInterval.left_le_of_mem hx
      exact Or.inl (by linarith)

/-- Auxiliary scope split for the conditional decomposition into the `↑↓` and unclocked forms.
The declaring
interval is nonempty, including a singleton. If the tracked left endpoint coincides
with the cut (`α c = 0`), its marker must include every endpoint included by
the declaring interval's left marker. -/
theorem carrier_union_split_upperScope (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker)
    (hJ : J.carrier.Nonempty)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes) :
    (⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ : Scope).carrier ∪
        (Scope.ofMarkedInterval J).carrier =
      (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier := by
  have hleft : J.left - (α c : ℝ) < J.left ∨
      (J.left - (α c : ℝ) = J.left ∧ (J.leftBoundary.Includes → b.Includes)) := by
    rcases (α c).coe_nonneg.eq_or_lt with hc | hc
    · exact Or.inr ⟨by linarith, hmarker (by linarith)⟩
    · exact Or.inl (by linarith)
  have hright : J.left < J.right ∨
      (J.left = J.right ∧ ((¬ₘ J.leftBoundary).Includes → J.rightBoundary.Includes)) := by
    rcases (MarkedInterval.nonempty_iff J).1 hJ with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, fun _ => ((Marker.includes_conj _ _).1 hm).2⟩
  have hjoin : J.left < J.left ∨
      (J.left = J.left ∧ ((¬ₘ J.leftBoundary).Includes ∨ J.leftBoundary.Includes)) := by
    right
    refine ⟨rfl, ?_⟩
    cases J.leftBoundary <;> simp
  have h := MarkedInterval.carrier_union_connected
    (J.left - (α c : ℝ)) (J.left) (J.left) (J.right)
    b (¬ₘ J.leftBoundary) J.leftBoundary J.rightBoundary hleft hjoin hright
  simpa [Scope.carrier, Scope.toMarkedInterval,
    Scope.ofMarkedInterval] using h

/-- The interval used to interpret an `always` predicate: add the lower timing
bound to the left endpoint and the upper timing bound to the right endpoint. -/
def alwaysRegion (S : Scope) (I : BoundedTimeInterval) : Scope :=
  ⟨S.leftBoundary, S.left + I.lower, S.right + I.upper, S.rightBoundary⟩

/-- Shifted-region analogue of `carrier_union_split_upperScope` for always
predicates. The two component regions overlap because the timing interval is
non-singular. -/
theorem carrier_union_split_upperAlwaysRegion (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (hJ : J.carrier.Nonempty)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes) :
    (alwaysRegion ⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ I).carrier ∪
        (alwaysRegion (Scope.ofMarkedInterval J) I).carrier =
      (alwaysRegion ⟨b, J.left - α c, J.right, J.rightBoundary⟩ I).carrier := by
  have hleft : J.left - (α c : ℝ) + I.lower < J.left + I.lower ∨
      (J.left - (α c : ℝ) + I.lower = J.left + I.lower ∧
        (J.leftBoundary.Includes → b.Includes)) := by
    rcases (α c).coe_nonneg.eq_or_lt with hc | hc
    · exact Or.inr ⟨by linarith, hmarker (by linarith)⟩
    · exact Or.inl (by linarith)
  have hright : J.left + I.upper < J.right + I.upper ∨
      (J.left + I.upper = J.right + I.upper ∧
        ((¬ₘ J.leftBoundary).Includes → J.rightBoundary.Includes)) := by
    rcases (MarkedInterval.nonempty_iff J).1 hJ with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, fun _ => ((Marker.includes_conj _ _).1 hm).2⟩
  have hjoin : J.left + I.lower < J.left + I.upper ∨
      (J.left + I.lower = J.left + I.upper ∧
        ((¬ₘ J.leftBoundary).Includes ∨ J.leftBoundary.Includes)) := by
    exact Or.inl (by linarith [I.nonSingular])
  have h := MarkedInterval.carrier_union_connected
    (J.left - (α c : ℝ) + I.lower) (J.left + I.lower) (J.left + I.upper) (J.right + I.upper)
    b (¬ₘ J.leftBoundary) J.leftBoundary J.rightBoundary hleft hjoin hright
  simpa [alwaysRegion, Scope.carrier, Scope.toMarkedInterval,
    Scope.ofMarkedInterval] using h

/-- A two-clock scope ending before the current interval's left endpoint is
contained in the corresponding `↑` scope. -/
theorem boundedScope_subset_upperScope (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (hJ : J.carrier.Nonempty) :
    (⟨b, J.left - α c, J.left - α d, b'⟩ : Scope).carrier ⊆
      (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier := by
  intro x hx
  change MarkedInterval.Mem
    ⟨J.left - α c, J.left - α d, b, b'⟩ x at hx
  change MarkedInterval.Mem
    ⟨J.left - α c, J.right, b, J.rightBoundary⟩ x
  refine ⟨hx.1, ?_⟩
  have hxd : x ≤ J.left - (α d : ℝ) := MarkedInterval.le_right_of_mem hx
  have hd : 0 ≤ (α d : ℝ) := (α d).coe_nonneg
  rcases (MarkedInterval.nonempty_iff J).1 hJ with hlt | ⟨heq, hm⟩
  · left
    linarith
  · have hxle : x ≤ J.right := by linarith
    rcases hxle.lt_or_eq with hlt | heq'
    · exact Or.inl hlt
    · exact Or.inr ⟨heq', ((Marker.includes_conj _ _).1 hm).2⟩

/-- The shifted checking region of the `↑↓` `□` predicate is contained
in that of the corresponding `↑` `□` predicate. -/
theorem boundedAlwaysRegion_subset_upperAlwaysRegion (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (hJ : J.carrier.Nonempty) :
    (alwaysRegion ⟨b, J.left - α c, J.left - α d, b'⟩ I).carrier ⊆
      (alwaysRegion ⟨b, J.left - α c, J.right, J.rightBoundary⟩ I).carrier := by
  intro x hx
  change MarkedInterval.Mem
    ⟨J.left - α c + I.lower, J.left - α d + I.upper, b, b'⟩ x at hx
  change MarkedInterval.Mem
    ⟨J.left - α c + I.lower, J.right + I.upper, b, J.rightBoundary⟩ x
  refine ⟨hx.1, ?_⟩
  have hxd : x ≤ J.left - (α d : ℝ) + I.upper :=
    MarkedInterval.le_right_of_mem hx
  have hd : 0 ≤ (α d : ℝ) := (α d).coe_nonneg
  rcases (MarkedInterval.nonempty_iff J).1 hJ with hlt | ⟨heq, hm⟩
  · left
    linarith
  · have hxle : x ≤ J.right + I.upper := by linarith
    rcases hxle.lt_or_eq with hlt | heq'
    · exact Or.inl hlt
    · exact Or.inr ⟨heq', ((Marker.includes_conj _ _).1 hm).2⟩

/-- Scope union for Lemma 3.12, including equality in both clock
conditions and singleton declaring intervals. -/
theorem carrier_union_bounded_upper (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (hne : J.carrier.Nonempty)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    (⟨b₁, J.left - α c₁, J.left - α d₁, q₁⟩ : Scope).carrier ∪
        (⟨b₂, J.left - α c₂, J.right, J.rightBoundary⟩ : Scope).carrier =
      (⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ : Scope).carrier := by
  apply MarkedInterval.carrier_union_connected
  · rcases hleft with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  · rcases hjoin with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  · have hd := (α d₁).coe_nonneg
    rcases (MarkedInterval.nonempty_iff J).1 hne with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · have hle : J.left - (α d₁ : ℝ) ≤ J.right := by linarith
      rcases hle.lt_or_eq with hlt | heq'
      · exact Or.inl hlt
      · exact Or.inr ⟨heq', fun _ => ((Marker.includes_conj _ _).1 hm).2⟩

/-- The always checking regions merge under the same clock conditions as
the scopes; non-singularity of the timing interval makes the join overlap. -/
theorem carrier_union_bounded_upper_alwaysRegion (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (I : BoundedTimeInterval) (hne : J.carrier.Nonempty)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    (alwaysRegion ⟨b₁, J.left - α c₁, J.left - α d₁, q₁⟩ I).carrier ∪
        (alwaysRegion ⟨b₂, J.left - α c₂, J.right, J.rightBoundary⟩ I).carrier =
      (alwaysRegion ⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ I).carrier := by
  dsimp only [alwaysRegion]
  apply MarkedInterval.carrier_union_connected
  · rcases hleft with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, hm⟩
  · have hle : (α d₁ : ℝ) ≤ α c₂ :=
      hjoin.elim le_of_lt (fun h => h.1.le)
    exact Or.inl (by linarith [I.nonSingular])
  · have hd := (α d₁).coe_nonneg
    rcases (MarkedInterval.nonempty_iff J).1 hne with hlt | ⟨heq, hm⟩
    · exact Or.inl (by linarith)
    · have hle : J.left - (α d₁ : ℝ) + I.upper ≤ J.right + I.upper := by linarith
      rcases hle.lt_or_eq with hlt | heq'
      · exact Or.inl hlt
      · exact Or.inr ⟨heq', fun _ => ((Marker.includes_conj _ _).1 hm).2⟩

/-- If advancing to `K` preserves the shifted left endpoint and `K` extends
strictly beyond `J`, the `↑` scope declared on `J` is contained in the one
declared on `K`. -/
theorem upperScope_subset_nextUpperScope (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b : Marker)
    (hleft : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hright : J.right < K.right) :
    (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier ⊆
      (⟨b, K.left - β c, K.right, K.rightBoundary⟩ : Scope).carrier := by
  intro x hx
  change MarkedInterval.Mem
    ⟨J.left - α c, J.right, b, J.rightBoundary⟩ x at hx
  change MarkedInterval.Mem
    ⟨K.left - β c, K.right, b, K.rightBoundary⟩ x
  constructor
  · simpa [hleft] using hx.1
  · exact Or.inl ((MarkedInterval.le_right_of_mem hx).trans_lt hright)

/-- Closed-endpoint core of the covering fact needed for the always instance
of Proposition 3.10 (1). -/
theorem exists_mem_Icc_and_mem_translate
    (L R x : ℝ) (I : BoundedTimeInterval) (hLR : L ≤ R)
    (hx : L + I.lower ≤ x ∧ x ≤ R + I.upper) :
    ∃ u : ℝ, u ∈ Set.Icc L R ∧ x ∈ (I : TimeInterval).translate u := by
  refine ⟨max L (x - I.upper), ?_⟩
  have hL : L ≤ x - I.lower := by linarith [hx.1]
  have hxba : x - I.upper ≤ x - I.lower := by linarith [I.nonSingular.le]
  have huUpper : max L (x - I.upper) ≤ x - I.lower := max_le hL hxba
  constructor
  · exact ⟨le_max_left _ _, max_le hLR (by linarith [hx.2])⟩
  · exact ⟨by linarith, by linarith [le_max_right L (x - I.upper)]⟩

/-- Right-open variant of `exists_mem_Icc_and_mem_translate`. -/
theorem exists_mem_Ico_and_mem_translate
    (L R x : ℝ) (I : BoundedTimeInterval) (hLR : L < R)
    (hx : L + I.lower ≤ x ∧ x < R + I.upper) :
    ∃ u : ℝ, u ∈ Set.Ico L R ∧ x ∈ (I : TimeInterval).translate u := by
  refine ⟨max L (x - I.upper), ?_⟩
  have hL : L ≤ x - I.lower := by linarith [hx.1]
  have hxba : x - I.upper ≤ x - I.lower := by linarith [I.nonSingular.le]
  have huUpper : max L (x - I.upper) ≤ x - I.lower := max_le hL hxba
  constructor
  · exact ⟨le_max_left _ _, max_lt hLR (by linarith [hx.2])⟩
  · exact ⟨by linarith, by linarith [le_max_right L (x - I.upper)]⟩

/-- Left-open variant of `exists_mem_Icc_and_mem_translate`. -/
theorem exists_mem_Ioc_and_mem_translate
    (L R x : ℝ) (I : BoundedTimeInterval) (hLR : L < R)
    (hx : L + I.lower < x ∧ x ≤ R + I.upper) :
    ∃ u : ℝ, u ∈ Set.Ioc L R ∧ x ∈ (I : TimeInterval).translate u := by
  let y := (L + min R (x - I.lower)) / 2
  let u := max (x - I.upper) y
  have hLM : L < min R (x - I.lower) := lt_min hLR (by linarith [hx.1])
  have hLy : L < y := by dsimp [y]; linarith
  have hyR : y ≤ R := by
    dsimp [y]
    linarith [min_le_left R (x - I.lower), hLM.le]
  have hyxa : y ≤ x - I.lower := by
    dsimp [y]
    linarith [min_le_right R (x - I.lower), hLM.le]
  have hxba : x - I.upper ≤ x - I.lower := by linarith [I.nonSingular.le]
  have huUpper : u ≤ x - I.lower := by
    exact max_le hxba hyxa
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · exact lt_max_of_lt_right hLy
  · exact max_le (by linarith [hx.2]) hyR
  · exact ⟨by linarith, by
      dsimp [u]
      linarith [le_max_left (x - I.upper) y]⟩

/-- Open variant of `exists_mem_Icc_and_mem_translate`. -/
theorem exists_mem_Ioo_and_mem_translate
    (L R x : ℝ) (I : BoundedTimeInterval) (hLR : L < R)
    (hx : L + I.lower < x ∧ x < R + I.upper) :
    ∃ u : ℝ, u ∈ Set.Ioo L R ∧ x ∈ (I : TimeInterval).translate u := by
  let y := (L + min R (x - I.lower)) / 2
  let u := max (x - I.upper) y
  have hLM : L < min R (x - I.lower) := lt_min hLR (by linarith [hx.1])
  have hLy : L < y := by dsimp [y]; linarith
  have hyR : y < R := by
    dsimp [y]
    linarith [min_le_left R (x - I.lower), hLM]
  have hyxa : y ≤ x - I.lower := by
    dsimp [y]
    linarith [min_le_right R (x - I.lower), hLM.le]
  have hxba : x - I.upper ≤ x - I.lower := by linarith [I.nonSingular.le]
  have huUpper : u ≤ x - I.lower := by
    exact max_le hxba hyxa
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · exact lt_max_of_lt_right hLy
  · exact max_lt (by linarith [hx.2]) hyR
  · exact ⟨by linarith, by
      dsimp [u]
      linarith [le_max_left (x - I.upper) y]⟩

/-- Marker-uniform covering theorem: the endpoint-expanded region is exactly
covered by translations of the original nonempty marked interval. -/
theorem exists_mem_and_mem_translate_of_mem_alwaysRegion
    (J : MarkedInterval) (I : BoundedTimeInterval) (hne : J.carrier.Nonempty)
    {x : ℝ} (hx : x ∈ alwaysRegion (Scope.ofMarkedInterval J) I) :
    ∃ u : ℝ, u ∈ J ∧ x ∈ (I : TimeInterval).translate u := by
  have horder := (MarkedInterval.nonempty_iff J).1 hne
  have hxMarked : x ∈ (alwaysRegion (Scope.ofMarkedInterval J) I).toMarkedInterval :=
    Scope.mem_toMarkedInterval.mpr hx
  rcases J with ⟨L, R, lb, rb⟩
  cases lb <;> cases rb
  · have hLR : L < R := by
      simpa [MarkedLT, Marker.conj, Marker.Includes] using horder
    have hxSet : x ∈ Set.Ioo (L + I.lower) (R + I.upper) := by
      have hxCarrier : x ∈ (alwaysRegion (Scope.ofMarkedInterval
          ⟨L, R, ○, ○⟩) I).toMarkedInterval.carrier := hxMarked
      simpa [alwaysRegion, Scope.ofMarkedInterval, Scope.toMarkedInterval,
        MarkedInterval.carrier_eq] using hxCarrier
    obtain ⟨u, hu, ht⟩ := exists_mem_Ioo_and_mem_translate L R x I hLR hxSet
    refine ⟨u, ?_, ht⟩
    exact (show u ∈ (⟨L, R, ○, ○⟩ : MarkedInterval).carrier by
      simpa [MarkedInterval.carrier_eq] using hu)
  · have hLR : L < R := by
      simpa [MarkedLT, Marker.conj, Marker.Includes] using horder
    have hxSet : x ∈ Set.Ioc (L + I.lower) (R + I.upper) := by
      have hxCarrier : x ∈ (alwaysRegion (Scope.ofMarkedInterval
          ⟨L, R, ○, ●⟩) I).toMarkedInterval.carrier := hxMarked
      simpa [alwaysRegion, Scope.ofMarkedInterval, Scope.toMarkedInterval,
        MarkedInterval.carrier_eq] using hxCarrier
    obtain ⟨u, hu, ht⟩ := exists_mem_Ioc_and_mem_translate L R x I hLR hxSet
    refine ⟨u, ?_, ht⟩
    exact (show u ∈ (⟨L, R, ○, ●⟩ : MarkedInterval).carrier by
      simpa [MarkedInterval.carrier_eq] using hu)
  · have hLR : L < R := by
      simpa [MarkedLT, Marker.conj, Marker.Includes] using horder
    have hxSet : x ∈ Set.Ico (L + I.lower) (R + I.upper) := by
      have hxCarrier : x ∈ (alwaysRegion (Scope.ofMarkedInterval
          ⟨L, R, ●, ○⟩) I).toMarkedInterval.carrier := hxMarked
      simpa [alwaysRegion, Scope.ofMarkedInterval, Scope.toMarkedInterval,
        MarkedInterval.carrier_eq] using hxCarrier
    obtain ⟨u, hu, ht⟩ := exists_mem_Ico_and_mem_translate L R x I hLR hxSet
    refine ⟨u, ?_, ht⟩
    exact (show u ∈ (⟨L, R, ●, ○⟩ : MarkedInterval).carrier by
      simpa [MarkedInterval.carrier_eq] using hu)
  · have hLR : L ≤ R := by
      simpa [MarkedLT, Marker.conj, Marker.Includes] using horder
    have hxSet : x ∈ Set.Icc (L + I.lower) (R + I.upper) := by
      have hxCarrier : x ∈ (alwaysRegion (Scope.ofMarkedInterval
          ⟨L, R, ●, ●⟩) I).toMarkedInterval.carrier := hxMarked
      simpa [alwaysRegion, Scope.ofMarkedInterval, Scope.toMarkedInterval,
        MarkedInterval.carrier_eq] using hxCarrier
    obtain ⟨u, hu, ht⟩ := exists_mem_Icc_and_mem_translate L R x I hLR hxSet
    refine ⟨u, ?_, ht⟩
    exact (show u ∈ (⟨L, R, ●, ●⟩ : MarkedInterval).carrier by
      simpa [MarkedInterval.carrier_eq] using hu)

/-- Membership in the suffix of the signal beginning at the left endpoint of
the current partition interval, respecting its boundary marker. -/
def InCurrentSuffix (J : MarkedInterval) (t : ℝ) : Prop :=
  J.left < t ∨ (J.left = t ∧ J.leftBoundary.Includes)

/-- The witness suffix shrinks on moving across an adjacent nonempty piece,
including when the current piece is a singleton. -/
theorem inCurrentSuffix_of_adjacent (J K : MarkedInterval)
    (hne : J.carrier.Nonempty) (hadj : J.right = K.left)
    {t : ℝ} (ht : InCurrentSuffix K t) : InCurrentSuffix J t := by
  have htge : K.left ≤ t := ht.elim le_of_lt (fun h => h.1.le)
  rcases (MarkedInterval.nonempty_iff J).1 hne with hlt | ⟨heq, hm⟩
  · exact Or.inl ((hlt.trans_eq hadj).trans_le htge)
  · have hle : J.left ≤ t := (heq.trans hadj).le.trans htge
    rcases hle.lt_or_eq with hlt | heq'
    · exact Or.inl hlt
    · exact Or.inr ⟨heq', ((Marker.includes_conj _ _).1 hm).1⟩

/-- Adjacent complementary boundaries split a suffix into the current piece
and the next suffix, including the shared endpoint. -/
theorem mem_or_inCurrentSuffix_of_adjacent (J K : MarkedInterval)
    (hadj : J.right = K.left)
    (hm : J.rightBoundary = Marker.complement K.leftBoundary)
    {t : ℝ} (ht : InCurrentSuffix J t) :
    t ∈ J ∨ InCurrentSuffix K t := by
  by_cases hs : InCurrentSuffix K t
  · exact Or.inr hs
  · left
    refine ⟨ht, ?_⟩
    have hle : t ≤ K.left := by
      by_contra hn
      exact hs (Or.inl (lt_of_not_ge hn))
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inl (hadj ▸ hlt)
    · have hn : ¬K.leftBoundary.Includes := fun hb => hs (Or.inr ⟨heq.symm, hb⟩)
      exact Or.inr ⟨heq.trans hadj.symm, hm ▸ (Marker.includes_complement _).2 hn⟩

/-- Residual satisfaction of an interval predicate. Always checking points
and eventuality witnesses are restricted to `InCurrentSuffix J`. -/
def Satisfies (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) : IntervalPredicate Clock Var → Prop
  | .plain φ =>
      ∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ φ
  | .upper c b .always I φ =>
      let S := scope J α (↑[c, b] □[I] φ)
      ∀ t : σ.Time, t.1 ∈ alwaysRegion S I → InCurrentSuffix J t.1 →
        (σ, t) ⊨ φ
  | .upper c b .eventually I φ =>
      let S := scope J α (↑[c, b] ◇[I] φ)
      ∀ t : ℝ, t ∈ S → ∃ t' : σ.Time,
        t'.1 ∈ (I : TimeInterval).translate t ∧ InCurrentSuffix J t'.1 ∧
          (σ, t') ⊨ φ
  | .bounded c d b b' .always I φ =>
      let S := scope J α (↑↓[c, d, b, b'] □[I] φ)
      ∀ t : σ.Time, t.1 ∈ alwaysRegion S I → InCurrentSuffix J t.1 →
        (σ, t) ⊨ φ
  | .bounded c d b b' .eventually I φ =>
      let S := scope J α (↑↓[c, d, b, b'] ◇[I] φ)
      ∀ t : ℝ, t ∈ S → ∃ t' : σ.Time,
        t'.1 ∈ (I : TimeInterval).translate t ∧ InCurrentSuffix J t'.1 ∧
          (σ, t') ⊨ φ

/-- Interval-predicate satisfaction notation. This project-specific symbol is
global for reliable editor support across imported modules. -/
notation:45 "(" σ "," J "," α ")" "⊨ᵢ" p =>
  STLTableau.IntervalPredicate.Satisfies σ J α p

open scoped STL

/-- On a nonempty current interval, satisfaction of an `↑` `◇`
implies satisfaction of the corresponding `↑↓` `◇`.  This is the
eventuality case of Lemma 3.11 (1). -/
theorem satisfies_bounded_eventually_of_upper
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty)
    (h : (σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ)) :
    (σ,J,α)⊨ᵢ(↑↓[c,d,b,b']◇[I]φ) := by
  intro t ht
  exact h t (boundedScope_subset_upperScope J α c d b b' hJ ht)

/-- On a nonempty current interval, satisfaction of a predicate in the `↑` form of `□`
implies satisfaction of the corresponding bounded invariant.  This is the
always case of Lemma 3.11 (1). -/
theorem satisfies_bounded_always_of_upper
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty)
    (h : (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) :
    (σ,J,α)⊨ᵢ(↑↓[c,d,b,b']□[I]φ) := by
  intro t ht hsuffix
  exact h t (boundedAlwaysRegion_subset_upperAlwaysRegion J α c d b b' I hJ ht)
    hsuffix

/-- Satisfaction of the `↑` form of `◇` propagates from the next interval
back to the current one when clock elapse preserves the shifted left endpoint.
This is the semantic core of Lemma 3.11 (2). -/
theorem satisfies_upper_eventually_of_next
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hright : J.right < K.right) (hadvance : J.left < K.left)
    (h : (σ,K,β)⊨ᵢ(↑[c,b]◇[I]φ)) :
    (σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
  intro t ht
  obtain ⟨t', ht'I, ht'K, ht'φ⟩ := h t
    (upperScope_subset_nextUpperScope J K α β c b hleft hright ht)
  refine ⟨t', ht'I, ?_, ht'φ⟩
  rcases ht'K with hlt | ⟨heq, _⟩
  · exact Or.inl (hadvance.trans hlt)
  · exact Or.inl (hadvance.trans_eq heq)

/-- Singleton-safe version of backward `↑` `◇` propagation. The
complementary markers exclude the shared endpoint from `J` when `K` is a singleton. -/
theorem satisfies_upper_eventually_of_adjacent
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hK : K.carrier.Nonempty)
    (hadj : J.right = K.left)
    (hm : J.rightBoundary = Marker.complement K.leftBoundary)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (h : (σ,K,β)⊨ᵢ(↑[c,b]◇[I]φ)) :
    (σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
  intro t ht
  have htK : t ∈ scope K β (↑[c,b]◇[I]φ) := by
    change MarkedInterval.Mem ⟨J.left - α c, J.right, b, J.rightBoundary⟩ t at ht
    change MarkedInterval.Mem ⟨K.left - β c, K.right, b, K.rightBoundary⟩ t
    constructor
    · simpa only [hc] using ht.1
    · rcases (MarkedInterval.nonempty_iff K).1 hK with hlt | ⟨heq, hmarkers⟩
      · exact Or.inl ((MarkedInterval.le_right_of_mem ht).trans_lt (hadj ▸ hlt))
      · have hclosed := ((Marker.includes_conj _ _).1 hmarkers).1
        rcases ht.2 with hlt | ⟨_, hinc⟩
        · exact Or.inl (hlt.trans_eq (hadj.trans heq))
        · rw [hm] at hinc
          exact ((Marker.includes_complement _).1 hinc hclosed).elim
  obtain ⟨t', ht'I, ht'K, ht'φ⟩ := h t htK
  exact ⟨t', ht'I, inCurrentSuffix_of_adjacent J K hJ hadj ht'K, ht'φ⟩

/-- With equal scopes, transfer satisfaction from the next `↑↓` form of `◇`
to the current `↑` form using inclusion of witness suffixes. -/
theorem satisfies_upper_eventually_of_bounded_next
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.right = K.left - (β d : ℝ))
    (hm : J.rightBoundary = b')
    (hsuffix : ∀ t, InCurrentSuffix K t → InCurrentSuffix J t)
    (h : (σ,K,β)⊨ᵢ(↑↓[c,d,b,b']◇[I]φ)) :
    (σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ) := by
  intro t ht
  have htK : t ∈ scope K β (↑↓[c,d,b,b']◇[I]φ) := by
    simpa only [scope, hc, hd, hm] using ht
  obtain ⟨t', ht'I, ht'K, ht'φ⟩ := h t htK
  exact ⟨t', ht'I, hsuffix t'.1 ht'K, ht'φ⟩

/-- Two-clock eventuality propagates backward when both shifted endpoints
are preserved and the next witness suffix is contained in the current one. -/
theorem satisfies_bounded_eventually_of_next
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.left - (α d : ℝ) = K.left - (β d : ℝ))
    (hsuffix : ∀ t, InCurrentSuffix K t → InCurrentSuffix J t)
    (h : (σ,K,β)⊨ᵢ(↑↓[c,d,b,b']◇[I]φ)) :
    (σ,J,α)⊨ᵢ(↑↓[c,d,b,b']◇[I]φ) := by
  intro t ht
  have htK : t ∈ scope K β (↑↓[c,d,b,b']◇[I]φ) := by
    simpa only [scope, hc, hd] using ht
  obtain ⟨t', ht'I, ht'K, ht'φ⟩ := h t htK
  exact ⟨t', ht'I, hsuffix t'.1 ht'K, ht'φ⟩

/-- An `↑` `□` predicate yields a next `↑↓` `□` predicate with
the same scope and a smaller checking suffix. -/
theorem satisfies_bounded_always_next_of_upper
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.right = K.left - (β d : ℝ))
    (hm : J.rightBoundary = b')
    (hsuffix : ∀ t, InCurrentSuffix K t → InCurrentSuffix J t)
    (h : (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) :
    (σ,K,β)⊨ᵢ(↑↓[c,d,b,b']□[I]φ) := by
  intro t ht hs
  apply h t
  · simpa only [scope, hc, hd, hm] using ht
  · exact hsuffix t.1 hs

/-- The defer guard places every point of the `↑↓` `□` checking region
in the declaring interval's suffix, including the equality/marker case. -/
theorem inCurrentSuffix_of_always_guard
    (K : MarkedInterval) (β : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hg : (β c : ℝ) <[Marker.imp b K.leftBoundary] I.lower)
    {t : ℝ} (ht : t ∈ alwaysRegion (scope K β (↑↓[c,d,b,q]□[I]φ)) I) :
    InCurrentSuffix K t := by
  have hl : K.left - (β c : ℝ) + I.lower < t ∨
      (K.left - (β c : ℝ) + I.lower = t ∧ b.Includes) := ht.1
  rcases hg with hlt | ⟨heq, hm⟩
  · left
    rcases hl with hl | ⟨hl, _⟩ <;> linarith
  · rcases hl with hl | ⟨hl, hb⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩

/-- Backward always transfer under the defer guard. Equal scopes alone are
not sufficient: the guard ensures no checking points are lost before `K`. -/
theorem satisfies_upper_always_of_bounded_next_of_guard
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.right = K.left - (β d : ℝ)) (hm : J.rightBoundary = q)
    (hg : (β c : ℝ) <[Marker.imp b K.leftBoundary] I.lower)
    (h : (σ,K,β)⊨ᵢ(↑↓[c,d,b,q]□[I]φ)) :
    (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ) := by
  intro t ht _
  have htK : t.1 ∈ alwaysRegion (scope K β (↑↓[c,d,b,q]□[I]φ)) I := by
    simpa only [scope, hc, hd, hm] using ht
  exact h t htK (inCurrentSuffix_of_always_guard K β c d b q I φ hg htK)

/-- Backward `↑↓` `□` transfer when the defer guard prevents the next
suffix from losing any checking points. -/
theorem satisfies_bounded_always_of_next_of_guard
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.left - (α d : ℝ) = K.left - (β d : ℝ))
    (hg : (β c : ℝ) <[Marker.imp b K.leftBoundary] I.lower)
    (h : (σ,K,β)⊨ᵢ(↑↓[c,d,b,q]□[I]φ)) :
    (σ,J,α)⊨ᵢ(↑↓[c,d,b,q]□[I]φ) := by
  intro t ht _
  have htK : t.1 ∈ alwaysRegion (scope K β (↑↓[c,d,b,q]□[I]φ)) I := by
    simpa only [scope, hc, hd] using ht
  exact h t htK (inCurrentSuffix_of_always_guard K β c d b q I φ hg htK)

/-- The finish guard excludes every next-suffix point from the checking
region. At equality, its marker condition excludes simultaneous inclusion. -/
theorem not_mem_alwaysRegion_of_finish_guard
    (K : MarkedInterval) (β : ClockValuation Clock) (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hg : I.upper <[Marker.notConj q K.leftBoundary] (β d : ℝ))
    {t : ℝ} (hs : InCurrentSuffix K t) :
    t ∉ alwaysRegion (scope K β (↑↓[c,d,b,q]□[I]φ)) I := by
  intro ht
  have hl : K.left ≤ t := hs.elim le_of_lt (fun h => h.1.le)
  have hr : t ≤ K.left - (β d : ℝ) + I.upper := MarkedInterval.le_right_of_mem ht
  rcases hg with hlt | ⟨heq, hm⟩
  · linarith
  · have hq : q.Includes := by
      rcases ht.2 with ht | ⟨_, hq⟩
      · change t < K.left - (β d : ℝ) + I.upper at ht
        exfalso
        linarith
      · exact hq
    have hk : K.leftBoundary.Includes := by
      rcases hs with hs | ⟨_, hk⟩
      · exfalso
        linarith
      · exact hk
    exact ((Marker.includes_notConj _ _).1 hm).elim (fun hn => hn hq) (fun hn => hn hk)

/-- A `↑↓` `□` predicate propagates forward: the checking region is
unchanged, while the next suffix is contained in the current suffix. -/
theorem satisfies_bounded_always_next_of_current
    (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.left - (α d : ℝ) = K.left - (β d : ℝ))
    (hsuffix : ∀ t, InCurrentSuffix K t → InCurrentSuffix J t)
    (h : (σ,J,α)⊨ᵢ(↑↓[c,d,b,b']□[I]φ)) :
    (σ,K,β)⊨ᵢ(↑↓[c,d,b,b']□[I]φ) := by
  intro t ht hs
  apply h t
  · simpa only [scope, hc, hd] using ht
  · exact hsuffix t.1 hs

/-- Eventuality case of Lemma 3.12 at the interval-predicate level. -/
theorem satisfies_eventually_merge_iff
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    (((σ,J,α)⊨ᵢ(↑↓[c₁,d₁,b₁,q₁]◇[I]φ)) ∧
      ((σ,J,α)⊨ᵢ(↑[c₂,b₂]◇[I]φ))) ↔
      ((σ,J,α)⊨ᵢ(↑[c₁,b₁]◇[I]φ)) := by
  have hu := carrier_union_bounded_upper J α c₁ d₁ c₂ b₁ q₁ b₂ hne hleft hjoin
  constructor
  · rintro ⟨hb, hupp⟩ t ht
    change t ∈ (⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ : Scope).carrier at ht
    rw [← hu] at ht
    exact ht.elim (hb t) (hupp t)
  · intro h
    constructor
    · intro t ht
      apply h t
      change t ∈ (⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ : Scope).carrier
      rw [← hu]
      exact Or.inl ht
    · intro t ht
      apply h t
      change t ∈ (⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ : Scope).carrier
      rw [← hu]
      exact Or.inr ht

/-- Always case of Lemma 3.12 at the interval-predicate level. -/
theorem satisfies_always_merge_iff
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    (((σ,J,α)⊨ᵢ(↑↓[c₁,d₁,b₁,q₁]□[I]φ)) ∧
      ((σ,J,α)⊨ᵢ(↑[c₂,b₂]□[I]φ))) ↔
      ((σ,J,α)⊨ᵢ(↑[c₁,b₁]□[I]φ)) := by
  have hu := carrier_union_bounded_upper_alwaysRegion J α c₁ d₁ c₂ b₁ q₁ b₂ I
    hne hleft hjoin
  constructor
  · rintro ⟨hb, hupp⟩ t ht hs
    change t.1 ∈ (alwaysRegion ⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ I).carrier at ht
    rw [← hu] at ht
    exact ht.elim (fun ht => hb t ht hs) (fun ht => hupp t ht hs)
  · intro h
    constructor
    · intro t ht hs
      apply h t _ hs
      change t.1 ∈ (alwaysRegion ⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ I).carrier
      rw [← hu]
      exact Or.inl ht
    · intro t ht hs
      apply h t _ hs
      change t.1 ∈ (alwaysRegion ⟨b₁, J.left - α c₁, J.right, J.rightBoundary⟩ I).carrier
      rw [← hu]
      exact Or.inr ht

@[simp] theorem satisfies_plain_iff (σ : FiniteSignal Var)
    (J : MarkedInterval) (α : ClockValuation Clock) (φ : Formula Var) :
    ((σ, J, α) ⊨ᵢ (.plain φ)) ↔
      ∀ t : σ.Time, t.1 ∈ J → (σ, t) ⊨ φ := Iff.rfl

/-- The eventuality instance of Proposition 3.10 (1), stated with the
implicit locality condition used by the proof. When the clock of the `↑` form
is zero and its marker is the current interval's left marker, the clocked and
unclocked predicates have the same meaning. -/
theorem satisfies_plain_eventually_iff_upper_of_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (hJ : J.carrier ⊆ σ.domain) :
    ((σ, J, α) ⊨ᵢ (.plain (◇[(I : TimeInterval)] φ))) ↔
      ((σ, J, α) ⊨ᵢ (↑[c, b] ◇[I] φ)) := by
  have hscope : scope J α (↑[c, b] ◇[I] φ) = Scope.ofMarkedInterval J := by
    rcases J with ⟨left, right, lb, rb⟩
    simp [scope, Scope.ofMarkedInterval, hc, hb]
  constructor
  · intro h t ht
    have htJ : t ∈ J := by
      simpa [hscope] using ht
    have htDomain : t ∈ σ.domain := hJ htJ
    let u : σ.Time := ⟨t, htDomain⟩
    obtain ⟨t', ht'I, ht'φ⟩ := (FiniteSignal.satisfies_eventually_iff σ
      (I : TimeInterval) φ u).1 (h u htJ)
    refine ⟨t', ht'I, ?_, ht'φ⟩
    have hle : t ≤ t'.1 := TimeInterval.le_of_mem_translate ht'I
    rcases htJ.1 with hlt | ⟨heq, hinc⟩
    · exact Or.inl (hlt.trans_le hle)
    · rcases hle.lt_or_eq with hlt | heq'
      · exact Or.inl (heq ▸ hlt)
      · exact Or.inr ⟨heq.trans heq', hb ▸ hinc⟩
  · intro h u hu
    rw [FiniteSignal.satisfies_eventually_iff]
    have hscope : u.1 ∈ scope J α (↑[c, b] ◇[I] φ) := by
      simpa [hscope] using hu
    obtain ⟨t', ht'I, _, ht'φ⟩ := h u.1 hscope
    exact ⟨t', ht'I, ht'φ⟩

/-- Auxiliary conditional decomposition into the `↑↓` and unclocked forms of `◇`.
The current interval is handled by an unclocked predicate. -/
theorem satisfies_upper_eventually_iff_bounded_and_plain
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hd : (α d : ℝ) = 0) (hJ : J.carrier.Nonempty)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes)
    (hDomain : J.carrier ⊆ σ.domain) :
    ((σ,J,α)⊨ᵢ(↑[c,b]◇[I]φ)) ↔
      ((σ,J,α)⊨ᵢ(↑↓[c,d,b,¬ₘ J.leftBoundary]◇[I]φ)) ∧
        ((σ,J,α)⊨ᵢ(.plain (◇[(I : TimeInterval)] φ))) := by
  have hplain := satisfies_plain_eventually_iff_upper_of_zero
    σ J α d J.leftBoundary I φ hd rfl hDomain
  rw [hplain]
  have hsplit := carrier_union_split_upperScope J α c b hJ hmarker
  have hscopeCurrent : scope J α (↑[d, J.leftBoundary] ◇[I] φ) =
      Scope.ofMarkedInterval J := by
    rcases J with ⟨left, right, lb, rb⟩
    simp [scope, Scope.ofMarkedInterval, hd]
  constructor
  · intro h
    constructor
    · intro t ht
      apply h t
      have htLeft : t ∈
          (⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ : Scope).carrier := by
        simpa [scope, hd] using ht
      have htUnion : t ∈
          (⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ : Scope).carrier ∪
            (Scope.ofMarkedInterval J).carrier := Or.inl htLeft
      rw [hsplit] at htUnion
      exact htUnion
    · intro t ht
      apply h t
      have htJ : t ∈ (Scope.ofMarkedInterval J).carrier := by
        simpa [hscopeCurrent] using ht
      have htUnion : t ∈
          (⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ : Scope).carrier ∪
            (Scope.ofMarkedInterval J).carrier := Or.inr htJ
      rw [hsplit] at htUnion
      exact htUnion
  · rintro ⟨hbounded, hcurrent⟩ t ht
    have htUpper : t ∈
        (⟨b, J.left - α c, J.right, J.rightBoundary⟩ : Scope).carrier := by
      simpa [scope] using ht
    rw [← hsplit] at htUpper
    rcases htUpper with htLeft | htRight
    · apply hbounded t
      simpa [scope, hd] using htLeft
    · apply hcurrent t
      simpa [hscopeCurrent] using htRight

/-- Easy direction of the always instance of Proposition 3.10 (1): an
clocked interval predicate in the `↑` form with a zero clock and the current left marker entails
the corresponding unclocked predicate for `□`. -/
theorem satisfies_plain_always_of_upper_of_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (h : (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) :
    (σ,J,α)⊨ᵢ(.plain (□[(I : TimeInterval)] φ)) := by
  intro u hu
  rw [FiniteSignal.satisfies_always_iff]
  intro t ht
  apply h t
  · rcases hu with ⟨hul, hur⟩
    rcases ht with ⟨htl, htr⟩
    change
      ((J.left - (α c : ℝ) + I.lower < t.1 ∨
          (J.left - (α c : ℝ) + I.lower = t.1 ∧ b.Includes)) ∧
        (t.1 < J.right + I.upper ∨
          (t.1 = J.right + I.upper ∧ J.rightBoundary.Includes)))
    rw [hc, sub_zero, hb]
    constructor
    · rcases hul with hul | ⟨hul, hub⟩
      · exact Or.inl (by
          linarith)
      · rcases lt_or_eq_of_le htl with hdelay | hdelay
        · exact Or.inl (by
            linarith)
        · exact Or.inr ⟨by
            linarith, hb ▸ hub⟩
    · rcases hur with hur | ⟨hur, hub⟩
      · exact Or.inl (by
          linarith)
      · rcases lt_or_eq_of_le htr with hdelay | hdelay
        · exact Or.inl (by
            linarith)
        · exact Or.inr ⟨by
            linarith, hub⟩
  · have hut : u.1 ≤ t.1 := TimeInterval.le_of_mem_translate ht
    rcases hu.1 with hul | ⟨hul, hub⟩
    · exact Or.inl (hul.trans_le hut)
    · rcases hut.lt_or_eq with hut | hut
      · exact Or.inl (hul ▸ hut)
      · exact Or.inr ⟨hul.trans hut, hub⟩

/-- Covering direction of the always instance of Proposition 3.10 (1). -/
theorem satisfies_upper_always_of_plain_of_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain)
    (h : (σ,J,α)⊨ᵢ(.plain (□[(I : TimeInterval)] φ))) :
    (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ) := by
  have hscope : scope J α (↑[c, b] □[I] φ) = Scope.ofMarkedInterval J := by
    rcases J with ⟨left, right, lb, rb⟩
    simp [scope, Scope.ofMarkedInterval, hc, hb]
  intro t ht _
  have ht' : t.1 ∈ alwaysRegion (Scope.ofMarkedInterval J) I := by
    simpa [hscope] using ht
  obtain ⟨u, huJ, htu⟩ :=
    exists_mem_and_mem_translate_of_mem_alwaysRegion J I hne ht'
  let u' : σ.Time := ⟨u, hJ huJ⟩
  have huAlways := h u' huJ
  exact (FiniteSignal.satisfies_always_iff σ (I : TimeInterval) φ u').1 huAlways t htu

/-- An unclocked predicate for `□` agrees with the `↑` form when the clock is zero
and the marker is the current interval's left marker. -/
theorem satisfies_plain_always_iff_upper_of_zero
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hb : b = J.leftBoundary)
    (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain) :
    ((σ,J,α)⊨ᵢ(.plain (□[(I : TimeInterval)] φ))) ↔
      (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ) :=
  ⟨satisfies_upper_always_of_plain_of_zero σ J α c b I φ hc hb hne hJ,
    satisfies_plain_always_of_upper_of_zero σ J α c b I φ hc hb⟩

/-- Auxiliary conditional decomposition into the `↑↓` and unclocked forms of `□`.
The current interval is handled by an unclocked predicate. -/
theorem satisfies_upper_always_iff_bounded_and_plain
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hd : (α d : ℝ) = 0) (hJ : J.carrier.Nonempty)
    (hmarker : (α c : ℝ) = 0 → J.leftBoundary.Includes → b.Includes)
    (hDomain : J.carrier ⊆ σ.domain) :
    ((σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) ↔
      ((σ,J,α)⊨ᵢ(↑↓[c,d,b,¬ₘ J.leftBoundary]□[I]φ)) ∧
        ((σ,J,α)⊨ᵢ(.plain (□[(I : TimeInterval)] φ))) := by
  have hne : J.carrier.Nonempty := hJ
  have hplain := satisfies_plain_always_iff_upper_of_zero
    σ J α d J.leftBoundary I φ hd rfl hne hDomain
  rw [hplain]
  have hscopeCurrent : scope J α (↑[d, J.leftBoundary] □[I] φ) =
      Scope.ofMarkedInterval J := by
    rcases J with ⟨left, right, lb, rb⟩
    simp [scope, Scope.ofMarkedInterval, hd]
  have hsplit := carrier_union_split_upperAlwaysRegion J α c b I hJ hmarker
  constructor
  · intro h
    constructor
    · intro t ht hsuffix
      apply h t
      · have htLeft : t.1 ∈
            (alwaysRegion ⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ I).carrier := by
          simpa [scope, hd] using ht
        have htUnion := (show t.1 ∈
          (alwaysRegion ⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ I).carrier ∪
            (alwaysRegion (Scope.ofMarkedInterval J) I).carrier from Or.inl htLeft)
        rw [hsplit] at htUnion
        exact htUnion
      · exact hsuffix
    · intro t ht hsuffix
      apply h t
      · have htCurrent : t.1 ∈ (alwaysRegion (Scope.ofMarkedInterval J) I).carrier := by
          simpa [hscopeCurrent] using ht
        have htUnion := (show t.1 ∈
          (alwaysRegion ⟨b, J.left - α c, J.left, ¬ₘ J.leftBoundary⟩ I).carrier ∪
            (alwaysRegion (Scope.ofMarkedInterval J) I).carrier from Or.inr htCurrent)
        rw [hsplit] at htUnion
        exact htUnion
      · exact hsuffix
  · rintro ⟨hbounded, hcurrent⟩ t ht hsuffix
    have htUpper : t.1 ∈
        (alwaysRegion ⟨b, J.left - α c, J.right, J.rightBoundary⟩ I).carrier := by
      simpa [scope] using ht
    rw [← hsplit] at htUpper
    rcases htUpper with htLeft | htCurrent
    · apply hbounded t
      · simpa [scope, hd] using htLeft
      · exact hsuffix
    · apply hcurrent t
      · simpa [hscopeCurrent] using htCurrent
      · exact hsuffix

/-- If an `↑` `□` checking region starts strictly before the current
right endpoint, it supplies a truth point in a non-singular declaring interval.
Stability then lifts that point to the whole interval. -/
theorem satisfies_plain_of_upper_always_of_overlap
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.left < J.right) (hDomain : J.carrier ⊆ σ.domain)
    (hcut : J.left - (α c : ℝ) + I.lower < J.right)
    (hstable : σ.Stable J φ) (h : (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) :
    (σ,J,α)⊨ᵢ(.plain φ) := by
  obtain ⟨x, hxlo, hxr⟩ := exists_between (max_lt hJ hcut)
  have hxl : J.left < x := (le_max_left _ _).trans_lt hxlo
  have hxcut : J.left - (α c : ℝ) + I.lower < x :=
    (le_max_right _ _).trans_lt hxlo
  have hxJ : x ∈ J := ⟨Or.inl hxl, Or.inl hxr⟩
  let t : σ.Time := ⟨x, hDomain hxJ⟩
  have htφ : (σ,t)⊨φ := by
    apply h t
    · change (J.left - (α c : ℝ) + I.lower < x ∨ _) ∧
        (x < J.right + I.upper ∨ _)
      refine ⟨Or.inl hxcut, Or.inl ?_⟩
      have hupper := I.lower_nonnegative.trans_lt I.nonSingular
      linarith
    · exact Or.inl hxl
  intro u hu
  exact (hstable t u hxJ hu).1 htφ

/-- Marker-sensitive overlap lifts an `↑` `□` truth point to the whole
stable declaring interval. Unlike the strict-overlap helper, this includes
singleton intervals and a checking region touching the current right endpoint. -/
theorem satisfies_plain_of_upper_always_of_marked_overlap
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hJ : J.carrier.Nonempty) (hDomain : J.carrier ⊆ σ.domain)
    (hcut : J.left - (α c : ℝ) + I.lower <[Marker.conj b J.rightBoundary] J.right)
    (hstable : σ.Stable J φ) (h : (σ,J,α)⊨ᵢ(↑[c,b]□[I]φ)) :
    (σ,J,α)⊨ᵢ(.plain φ) := by
  let K := (alwaysRegion (scope J α (↑[c,b]□[I]φ)) I).toMarkedInterval
  obtain ⟨a, ha⟩ := hJ
  have hle : J.left ≤ J.right :=
    (MarkedInterval.left_le_of_mem ha).trans (MarkedInterval.le_right_of_mem ha)
  have hc := (α c).coe_nonneg
  have hi := I.lower_nonnegative.trans_lt I.nonSingular
  have hK : K.carrier.Nonempty := by
    apply (MarkedInterval.nonempty_iff K).2
    left
    change J.left - (α c : ℝ) + I.lower < J.right + I.upper
    linarith [I.nonSingular]
  have hcross : J.left <[Marker.conj J.leftBoundary K.rightBoundary] K.right := by
    left
    change J.left < J.right + I.upper
    linarith
  obtain ⟨x, hxJ, hxK⟩ := MarkedInterval.inter_nonempty_of_cross_bounds J K
    ⟨a, ha⟩ hK hcross hcut
  let t : σ.Time := ⟨x, hDomain hxJ⟩
  have htφ : (σ,t)⊨φ := h t hxK hxJ.1
  intro u hu
  exact (hstable t u hxJ hu).1 htφ

/-- Atomic interval predicates are unclocked predicates for atomic propositions or Boolean
constants.
Here `Formula.falsity` is represented by `.neg .truth`. -/
def IsAtomic : IntervalPredicate Clock Var → Prop
  | .plain (.atom _) | .plain .truth | .plain (.neg .truth) => True
  | _ => False

@[simp] theorem atomic_plain_atom (a : AtomicProposition Var) :
    IsAtomic (IntervalPredicate.plain (.atom a) : IntervalPredicate Clock Var) := trivial

@[simp] theorem atomic_plain_truth :
    IsAtomic (IntervalPredicate.plain .truth : IntervalPredicate Clock Var) := trivial

@[simp] theorem atomic_plain_falsity :
    IsAtomic (IntervalPredicate.plain Formula.falsity : IntervalPredicate Clock Var) := trivial

end IntervalPredicate

end STLTableau
