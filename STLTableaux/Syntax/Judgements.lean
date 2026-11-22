/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Semantics.Residual.IntervalPredicate

/-!
# Interval sequence judgements and clock resets

Judgement syntax (Definition 3.5) and residual satisfaction on a partition.
-/

namespace STLTableau

/-- The five clock comparisons in Definition 3.5. -/
inductive ClockRelation where
  | ge | gt | eq | lt | le
  deriving DecidableEq, Repr

namespace ClockRelation

/-- Interpretation of a clock relation over nonnegative reals. -/
def Holds : ClockRelation → NNReal → NNReal → Prop
  | .ge => (· ≥ ·)
  | .gt => (· > ·)
  | .eq => (· = ·)
  | .lt => (· < ·)
  | .le => (· ≤ ·)

end ClockRelation

/-- A clock reset set assigns one nonnegative value to each of finitely many clocks. -/
structure ClockResetSet (Clock : Type*) where
  value : Clock → Option NNReal
  finite_domain : Set.Finite {c | ∃ a, value c = some a}

namespace ClockResetSet

variable {Clock : Type*}

/-- Apply all resets in `Λ` to `α`. -/
def apply (Λ : ClockResetSet Clock) (α : ClockValuation Clock) : ClockValuation Clock :=
  fun c => match Λ.value c with
    | Option.some a => a
    | Option.none => α c

/-- The clocks reset by `Λ`. -/
def clocks (Λ : ClockResetSet Clock) : Set Clock := {c | ∃ a, Λ.value c = Option.some a}

/-- Two reset sets agree wherever both specify a value. -/
def Consistent (Λ₁ Λ₂ : ClockResetSet Clock) : Prop :=
  ∀ c a b, Λ₁.value c = Option.some a → Λ₂.value c = Option.some b → a = b

/-- Left-biased union of reset sets. Under consistency the bias is immaterial. -/
def union (Λ₁ Λ₂ : ClockResetSet Clock) : ClockResetSet Clock where
  value := fun c => match Λ₁.value c with
    | Option.some a => Option.some a
    | Option.none => Λ₂.value c
  finite_domain := by
    apply Set.Finite.subset (Λ₁.finite_domain.union Λ₂.finite_domain)
    rintro c ⟨a, ha⟩
    by_cases h₁ : ∃ b, Λ₁.value c = Option.some b
    · exact Or.inl h₁
    · right
      cases h : Λ₁.value c with
      | none =>
          change ∃ b, Λ₂.value c = Option.some b
          rw [h] at ha
          change Λ₂.value c = Option.some a at ha
          exact ⟨a, ha⟩
      | some b => exact (h₁ ⟨b, h⟩).elim

/-- Empty reset set. -/
def empty : ClockResetSet Clock where
  value := fun _ => (Option.none : Option NNReal)
  finite_domain := by
    apply Set.Finite.subset (Set.finite_empty : Set.Finite (∅ : Set Clock))
    rintro c ⟨a, h⟩
    cases h

/-- The reset set containing the single assignment `c ↦ a`. -/
def singleton [DecidableEq Clock] (c : Clock) (a : NNReal) : ClockResetSet Clock where
  value := fun d => if d = c then Option.some a else Option.none
  finite_domain := by
    apply Set.Finite.subset (Set.finite_singleton c)
    rintro d ⟨b, hb⟩
    simp only [Set.mem_singleton_iff]
    by_contra hdc
    have : (Option.none : Option NNReal) = Option.some b := by
      simpa [hdc] using hb
    cases this

/-- Notation for a singleton clock reset. -/
scoped[STL] notation:max "⟦" c " ↦ᶜ " a "⟧" =>
  STLTableau.ClockResetSet.singleton c a

open scoped STL

/-- Add a constant duration to every clock. -/
def elapse (α : ClockValuation Clock) (δ : NNReal) : ClockValuation Clock :=
  fun c => α c + δ

@[simp] theorem apply_empty (α : ClockValuation Clock) : empty.apply α = α := by
  rfl

@[simp] theorem apply_singleton_self [DecidableEq Clock] (c : Clock) (a : NNReal)
    (α : ClockValuation Clock) : (⟦c ↦ᶜ a⟧).apply α c = a := by
  simp [apply, singleton]

@[simp] theorem apply_singleton_of_ne [DecidableEq Clock] {c d : Clock} (a : NNReal)
    (α : ClockValuation Clock) (h : d ≠ c) : (⟦c ↦ᶜ a⟧).apply α d = α d := by
  unfold apply
  rw [show (singleton c a).value d = Option.none by simp [singleton, h]]

@[simp] theorem clocks_singleton [DecidableEq Clock] (c : Clock) (a : NNReal) :
    (⟦c ↦ᶜ a⟧ : ClockResetSet Clock).clocks = {c} := by
  ext d
  simp only [clocks, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, hb⟩
    by_contra hdc
    have : (Option.none : Option NNReal) = Option.some b := by
      simpa [singleton, hdc] using hb
    cases this
  · rintro rfl
    exact ⟨a, by simp [singleton]⟩

theorem apply_union_eq_left_of_mem (Λ₁ Λ₂ : ClockResetSet Clock)
    (α : ClockValuation Clock) {c : Clock} (hc : c ∈ Λ₁.clocks) :
    (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
  obtain ⟨a, ha⟩ := hc
  unfold apply
  rw [show (Λ₁.union Λ₂).value c =
    (match Λ₁.value c with | Option.some a => Option.some a | Option.none => Λ₂.value c) from rfl]
  rw [ha]

theorem apply_union_eq_left_of_not_mem (Λ₁ Λ₂ : ClockResetSet Clock)
    (α : ClockValuation Clock) {c : Clock} (hc : c ∉ Λ₂.clocks) :
    (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
  cases h₁ : Λ₁.value c with
  | some a => exact apply_union_eq_left_of_mem Λ₁ Λ₂ α ⟨a, h₁⟩
  | none =>
      cases h₂ : Λ₂.value c with
      | some b => exact (hc ⟨b, h₂⟩).elim
      | none =>
          unfold apply
          rw [show (Λ₁.union Λ₂).value c =
            (match Λ₁.value c with
              | Option.some a => Option.some a | Option.none => Λ₂.value c) from rfl]
          rw [h₁, h₂]

theorem apply_union_eq_right_of_not_mem (Λ₁ Λ₂ : ClockResetSet Clock)
    (α : ClockValuation Clock) {c : Clock} (hc : c ∉ Λ₁.clocks) :
    (Λ₁.union Λ₂).apply α c = Λ₂.apply α c := by
  cases h₁ : Λ₁.value c with
  | some a => exact (hc ⟨a, h₁⟩).elim
  | none =>
      unfold apply
      rw [show (Λ₁.union Λ₂).value c =
        (match Λ₁.value c with
          | Option.some a => Option.some a | Option.none => Λ₂.value c) from rfl]
      rw [h₁]

theorem apply_union_eq_right_of_consistent (Λ₁ Λ₂ : ClockResetSet Clock)
    (hcon : Λ₁.Consistent Λ₂) (α : ClockValuation Clock) {c : Clock}
    (hc : c ∈ Λ₂.clocks) :
    (Λ₁.union Λ₂).apply α c = Λ₂.apply α c := by
  obtain ⟨b, hb⟩ := hc
  cases h₁ : Λ₁.value c with
  | none => exact apply_union_eq_right_of_not_mem Λ₁ Λ₂ α (by
      rintro ⟨a, ha⟩
      rw [h₁] at ha
      cases ha)
  | some a =>
      have hab := hcon c a b h₁ hb
      rw [apply_union_eq_left_of_mem Λ₁ Λ₂ α ⟨a, h₁⟩]
      unfold apply
      rw [h₁, hb, hab]

/-- Sequentially applying consistent reset sets is the same as applying their union. -/
theorem apply_apply_eq_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (hcon : Λ₁.Consistent Λ₂) (α : ClockValuation Clock) :
    Λ₂.apply (Λ₁.apply α) = (Λ₁.union Λ₂).apply α := by
  funext c
  by_cases hc₂ : c ∈ Λ₂.clocks
  · symm
    rw [apply_union_eq_right_of_consistent Λ₁ Λ₂ hcon α hc₂]
    obtain ⟨b, hb⟩ := hc₂
    unfold apply
    rw [hb]
  · rw [apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂]
    cases h₂ : Λ₂.value c with
    | none =>
        unfold apply
        rw [h₂]
    | some b => exact (hc₂ ⟨b, h₂⟩).elim

end ClockResetSet

/-- Definition 3.5 (interval sequence judgement) with bounded timing intervals
in clocked predicates. -/
inductive Judgement (Clock Var : Type*) where
  | terminal
  | clock (clock : Clock) (relation : ClockRelation) (value : NNReal)
  | leftMarker (marker : Marker)
  | predicate (predicate : IntervalPredicate Clock Var)
  | next (body : Judgement Clock Var)
  | reset (resets : ClockResetSet Clock) (body : Judgement Clock Var)
  | conj (left right : Judgement Clock Var)

/-- An interval predicate can be used as an interval sequence judgement. -/
instance {Clock Var : Type*} : Coe (IntervalPredicate Clock Var) (Judgement Clock Var) :=
  ⟨Judgement.predicate⟩

/-- Notation for the judgement constructors. -/
scoped[STL] notation "∗" => STLTableau.Judgement.terminal
scoped[STL] notation:max "lty[" m "]" => STLTableau.Judgement.leftMarker m
scoped[STL] notation:50 c:51 " ≥ᶜ " a:51 =>
  STLTableau.Judgement.clock c STLTableau.ClockRelation.ge a
scoped[STL] notation:50 c:51 " >ᶜ " a:51 =>
  STLTableau.Judgement.clock c STLTableau.ClockRelation.gt a
scoped[STL] notation:50 c:51 " =ᶜ " a:51 =>
  STLTableau.Judgement.clock c STLTableau.ClockRelation.eq a
scoped[STL] notation:50 c:51 " <ᶜ " a:51 =>
  STLTableau.Judgement.clock c STLTableau.ClockRelation.lt a
scoped[STL] notation:50 c:51 " ≤ᶜ " a:51 =>
  STLTableau.Judgement.clock c STLTableau.ClockRelation.le a
scoped[STL] infixr:65 " ·ⱼ " => STLTableau.Judgement.reset

namespace Judgement

variable {Clock Var : Type*}

open scoped STL

/-- Atomic judgements are terminal judgements, clock constraints, interval
type judgements, and interval predicates (Section 3.2). -/
def IsAtomic : Judgement Clock Var → Prop
  | .terminal | .clock _ _ _ | .leftMarker _ | .predicate _ => True
  | _ => False

/-- Clock variables occurring in an interval predicate, as a set. -/
def predicateClocks : IntervalPredicate Clock Var → Set Clock
  | p => p.clockSet

/-- All free clocks of a judgement. A reset binds its clocks in its body. -/
def freeClocks : Judgement Clock Var → Set Clock
  | .terminal | .leftMarker _ => ∅
  | .clock c _ _ => {c}
  | .predicate p => predicateClocks p
  | .next Ψ => freeClocks Ψ
  | .reset Λ Ψ => freeClocks Ψ \ Λ.clocks
  | .conj Φ Ψ => freeClocks Φ ∪ freeClocks Ψ

/-- All clocks occurring in a judgement, including clocks bound by resets. -/
def clocks : Judgement Clock Var → Set Clock
  | .terminal | .leftMarker _ => ∅
  | .clock c _ _ => {c}
  | .predicate p => predicateClocks p
  | .next Ψ => clocks Ψ
  | .reset Λ Ψ => Λ.clocks ∪ clocks Ψ
  | .conj Φ Ψ => clocks Φ ∪ clocks Ψ

@[simp] theorem atomic_terminal :
    IsAtomic (∗ : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock (c : Clock) (r : ClockRelation) (a : NNReal) :
    IsAtomic (.clock c r a : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock_ge (c : Clock) (a : NNReal) :
    IsAtomic (c ≥ᶜ a : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock_gt (c : Clock) (a : NNReal) :
    IsAtomic (c >ᶜ a : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock_eq (c : Clock) (a : NNReal) :
    IsAtomic (c =ᶜ a : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock_lt (c : Clock) (a : NNReal) :
    IsAtomic (c <ᶜ a : Judgement Clock Var) := trivial

@[simp] theorem atomic_clock_le (c : Clock) (a : NNReal) :
    IsAtomic (c ≤ᶜ a : Judgement Clock Var) := trivial

@[simp] theorem atomic_leftMarker (m : Marker) :
    IsAtomic (lty[m] : Judgement Clock Var) := trivial

@[simp] theorem atomic_predicate (p : IntervalPredicate Clock Var) :
    IsAtomic (p : Judgement Clock Var) := trivial

/-- Positions include the terminal position immediately after the last interval. -/
abbrev Position {domain : Set ℝ} (P : IntervalPartition domain) := Fin (P.size + 1)

/-- The nonnegative duration of a nonempty partition interval. -/
noncomputable def duration {domain : Set ℝ} (P : IntervalPartition domain)
    (i : Fin P.size) : NNReal := by
  refine ⟨(P.interval i).right - (P.interval i).left, sub_nonneg.mpr ?_⟩
  obtain ⟨t, ht⟩ := P.nonempty i
  exact (MarkedInterval.left_le_of_mem ht).trans (MarkedInterval.le_right_of_mem ht)

/-- Advancing clocks by the duration of `Jᵢ` preserves the shifted left
endpoint at `Jᵢ₊₁`. -/
theorem next_left_sub_elapse_eq {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (α : ClockValuation Clock)
    (i : Fin P.size) (hi : i.1 + 1 < P.size) (c : Clock) :
    (P.interval ⟨i.1 + 1, hi⟩).left -
        (ClockResetSet.elapse α (duration P i) c : ℝ) =
      (P.interval i).left - (α c : ℝ) := by
  have hadj := P.adjacent_right_eq_left i hi
  change (P.interval ⟨i.1 + 1, hi⟩).left -
      ((α c : ℝ) + ((duration P i : NNReal) : ℝ)) =
    (P.interval i).left - (α c : ℝ)
  rw [show ((duration P i : NNReal) : ℝ) =
      (P.interval i).right - (P.interval i).left from rfl]
  rw [← hadj]
  ring

/-- Satisfaction of a judgement at a partition position. -/
def Satisfies (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Position P) → Judgement Clock Var → Prop
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .leftMarker m =>
      if h : k.1 < P.size then (P.interval ⟨k.1, h⟩).leftBoundary = m else m = ●
  | k, .predicate p =>
      if h : k.1 < P.size then (σ, P.interval ⟨k.1, h⟩, α) ⊨ᵢ p else False
  | k, .next Ψ =>
      if h : k.1 < P.size then
        Satisfies σ P (ClockResetSet.elapse α (duration P ⟨k.1, h⟩))
          ⟨k.1 + 1, by omega⟩ Ψ
      else False
  | k, .reset Λ Ψ => Satisfies σ P (Λ.apply α) k Ψ
  | k, .conj Ψ₁ Ψ₂ => Satisfies σ P α k Ψ₁ ∧ Satisfies σ P α k Ψ₂

/-- Satisfaction notation for interval-sequence judgements. -/
notation:45 "(" σ "," P "," α "," k ")" "⊨ⱼ" Ψ =>
  STLTableau.Judgement.Satisfies σ P α k Ψ

/-- Semantic equivalence of judgements. -/
def Equivalent (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P),
    ((σ, P, α, k) ⊨ⱼ Φ) ↔ ((σ, P, α, k) ⊨ⱼ Ψ)

/-- Judgement equivalence restricted to valuations satisfying the stated
clock condition. Marker parameters remain fixed in both judgements. -/
def EquivalentUnder (H : ClockValuation Clock → Prop)
    (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P), H α →
    (((σ,P,α,k) ⊨ⱼ Φ) ↔ ((σ,P,α,k) ⊨ⱼ Ψ))

/-- Semantic implication between judgements. -/
def Implies (Φ Ψ : Judgement Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P),
    ((σ, P, α, k) ⊨ⱼ Φ) → ((σ, P, α, k) ⊨ⱼ Ψ)

scoped[STL] infix:50 " ≡ⱼ " => STLTableau.Judgement.Equivalent
scoped[STL] infix:50 " ⇒ⱼ " => STLTableau.Judgement.Implies
scoped[STL] infixr:60 " ∧ⱼ " => STLTableau.Judgement.conj
scoped[STL] prefix:max "Xⱼ " => STLTableau.Judgement.next

open scoped STL

@[simp] theorem satisfies_terminal (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) :
    ((σ, P, α, k) ⊨ⱼ (∗ : Judgement Clock Var)) ↔ k.1 = P.size := Iff.rfl

@[simp] theorem satisfies_conj (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (Φ Ψ : Judgement Clock Var) :
    ((σ, P, α, k) ⊨ⱼ (Φ ∧ⱼ Ψ)) ↔
      ((σ, P, α, k) ⊨ⱼ Φ) ∧ ((σ, P, α, k) ⊨ⱼ Ψ) := Iff.rfl

/-- Interval-predicate satisfaction depends only on its occurring clocks. -/
private theorem predicate_satisfies_congr {p : IntervalPredicate Clock Var}
    {α β : ClockValuation Clock} (h : ∀ c ∈ predicateClocks p, α c = β c)
    (σ : FiniteSignal Var) (J : MarkedInterval) :
    ((σ, J, α) ⊨ᵢ p) ↔ ((σ, J, β) ⊨ᵢ p) := by
  cases p with
  | plain φ => rfl
  | upper c b kind I φ =>
      have hc : α c = β c := h c (by simp [predicateClocks])
      cases kind <;> simp [IntervalPredicate.Satisfies, IntervalPredicate.scope, hc]
  | bounded c d b b' kind I φ =>
      have hc : α c = β c := h c (by simp [predicateClocks])
      have hd : α d = β d := h d (by simp [predicateClocks])
      cases kind <;> simp [IntervalPredicate.Satisfies, IntervalPredicate.scope, hc, hd]

/-- Satisfaction depends only on the free clocks of a judgement. -/
theorem satisfies_congr_of_agree {Ψ : Judgement Clock Var}
    {α β : ClockValuation Clock} (h : ∀ c ∈ freeClocks Ψ, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (k : Position P) :
    ((σ, P, α, k) ⊨ⱼ Ψ) ↔ ((σ, P, β, k) ⊨ⱼ Ψ) := by
  induction Ψ generalizing α β k with
  | terminal => rfl
  | clock c r a =>
      have hc := h c (by simp [freeClocks])
      simp [Satisfies, hc]
  | leftMarker m => rfl
  | predicate p =>
      simp only [Satisfies]
      split
      · exact predicate_satisfies_congr h σ _
      · rfl
  | next Ψ ih =>
      simp only [Satisfies]
      split
      · apply ih
        intro c hc
        simp [ClockResetSet.elapse, h c (by simpa [freeClocks] using hc)]
      · rfl
  | reset Λ Ψ ih =>
      apply ih
      intro c hc
      cases hΛ : Λ.value c with
      | some a => simp [ClockResetSet.apply, hΛ]
      | none =>
          have hcnot : c ∉ Λ.clocks := by
            rintro ⟨a, ha⟩
            rw [hΛ] at ha
            cases ha
          have hcfree : c ∈ freeClocks (.reset Λ Ψ) := ⟨hc, hcnot⟩
          have hα : Λ.apply α c = α c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          have hβ : Λ.apply β c = β c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          rw [hα, hβ]
          exact h c hcfree
  | conj Φ Ψ ihΦ ihΨ =>
      constructor
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).1 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).1 hΨ
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).2 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).2 hΨ

/-- Proposition 3.9 (1), idempotence. -/
theorem conj_idem (Ψ : Judgement Clock Var) : Ψ ∧ⱼ Ψ ≡ⱼ Ψ := by
  intro σ P α k
  simp

/-- Proposition 3.9 (1), commutativity. -/
theorem conj_comm (Φ Ψ : Judgement Clock Var) : Φ ∧ⱼ Ψ ≡ⱼ Ψ ∧ⱼ Φ := by
  intro σ P α k
  exact and_comm

/-- Proposition 3.9 (1), distribution of next over conjunction. -/
theorem next_conj (Φ Ψ : Judgement Clock Var) : Xⱼ (Φ ∧ⱼ Ψ) ≡ⱼ (Xⱼ Φ) ∧ⱼ (Xⱼ Ψ) := by
  intro σ P α k
  simp only [Satisfies]
  split <;> simp_all

/-- Proposition 3.9 (2), merging two parallel reset judgements. -/
theorem reset_conj_reset_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (Λ₁ ·ⱼ Φ)))
    (h₂₁ : Disjoint Λ₁.clocks (freeClocks (Λ₂ ·ⱼ Ψ))) :
    (Λ₁ ·ⱼ Φ) ∧ⱼ (Λ₂ ·ⱼ Ψ) ≡ⱼ (Λ₁.union Λ₂) ·ⱼ (Φ ∧ⱼ Ψ) := by
  intro σ P α k
  have hagree₁ : ∀ c ∈ freeClocks Φ,
      (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := by
        intro hc₂
        exact Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  have hagree₂ : ∀ c ∈ freeClocks Ψ,
      (Λ₁.union Λ₂).apply α c = Λ₂.apply α c := by
    intro c hc
    by_cases hc₂ : c ∈ Λ₂.clocks
    · exact ClockResetSet.apply_union_eq_right_of_consistent Λ₁ Λ₂ hcon α hc₂
    · have hc₁ : c ∉ Λ₁.clocks := by
        intro hc₁
        exact Set.disjoint_left.1 h₂₁ hc₁ ⟨hc, hc₂⟩
      exact ClockResetSet.apply_union_eq_right_of_not_mem Λ₁ Λ₂ α hc₁
  have hΦ := satisfies_congr_of_agree hagree₁ σ P k
  have hΨ := satisfies_congr_of_agree hagree₂ σ P k
  change
    (((σ, P, Λ₁.apply α, k) ⊨ⱼ Φ) ∧ ((σ, P, Λ₂.apply α, k) ⊨ⱼ Ψ)) ↔
      ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ⱼ Φ) ∧
        ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ⱼ Ψ)
  exact and_congr hΦ.symm hΨ.symm

/-- Proposition 3.9 (2), pulling a nested reset out of a
conjunction. The manuscript states the same symmetric side conditions as for
`reset_conj_reset_equiv_union`; only the condition protecting `Φ` is needed
for this orientation. -/
theorem reset_conj_nested_equiv_union (Λ₁ Λ₂ : ClockResetSet Clock)
    (Φ Ψ : Judgement Clock Var) (hcon : Λ₁.Consistent Λ₂)
    (h₁₂ : Disjoint Λ₂.clocks (freeClocks (Λ₁ ·ⱼ Φ))) :
    Λ₁ ·ⱼ (Φ ∧ⱼ (Λ₂ ·ⱼ Ψ)) ≡ⱼ (Λ₁.union Λ₂) ·ⱼ (Φ ∧ⱼ Ψ) := by
  intro σ P α k
  have hagree : ∀ c ∈ freeClocks Φ,
      (Λ₁.union Λ₂).apply α c = Λ₁.apply α c := by
    intro c hc
    by_cases hc₁ : c ∈ Λ₁.clocks
    · exact ClockResetSet.apply_union_eq_left_of_mem Λ₁ Λ₂ α hc₁
    · have hc₂ : c ∉ Λ₂.clocks := by
        intro hc₂
        exact Set.disjoint_left.1 h₁₂ hc₂ ⟨hc, hc₁⟩
      exact ClockResetSet.apply_union_eq_left_of_not_mem Λ₁ Λ₂ α hc₂
  have hΦ := satisfies_congr_of_agree hagree σ P k
  have hreset := ClockResetSet.apply_apply_eq_union Λ₁ Λ₂ hcon α
  change
    (((σ, P, Λ₁.apply α, k) ⊨ⱼ Φ) ∧
        ((σ, P, Λ₂.apply (Λ₁.apply α), k) ⊨ⱼ Ψ)) ↔
      ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ⱼ Φ) ∧
        ((σ, P, (Λ₁.union Λ₂).apply α, k) ⊨ⱼ Ψ)
  rw [hreset]
  exact and_congr hΦ.symm Iff.rfl

/-- Fixed-marker form used internally to prove the satisfaction-driven form
of Proposition 3.10 (1). -/
theorem satisfies_plain_eventually_iff_reset_upper_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hb : b = (P.interval ⟨k.1, hk⟩).leftBoundary) :
    ((σ, P, α, k) ⊨ⱼ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ((σ, P, α, k) ⊨ⱼ
      (⟦c ↦ᶜ 0⟧ ·ⱼ
        ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  let i : Fin P.size := ⟨k.1, hk⟩
  have hJ : (P.interval i).carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hpred := IntervalPredicate.satisfies_plain_eventually_iff_upper_of_zero
    σ (P.interval i) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
    (by simp) hb hJ
  change
    (if h : k.1 < P.size then
      (σ, P.interval ⟨k.1, h⟩, α) ⊨ᵢ
        IntervalPredicate.plain (◇[(I : TimeInterval)] φ)
    else False) ↔
      ((if h : k.1 < P.size then
        (σ, P.interval ⟨k.1, h⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ᵢ
          (↑[c, b] ◇[I] φ)
      else False) ∧
        (if h : k.1 < P.size then
          (P.interval ⟨k.1, h⟩).leftBoundary = b
        else b = ●))
  simp only [dif_pos hk]
  dsimp [i] at hpred
  change
    ((σ, P.interval ⟨k.1, hk⟩, α) ⊨ᵢ
      IntervalPredicate.plain (◇[(I : TimeInterval)] φ)) ↔ _ at hpred
  rw [hpred]
  simp [hb]

/-- Eventuality instance of Proposition 3.10 (1). The marker is selected
inside satisfaction: `lty[b]` ensures that the witness `b` is precisely the
left marker of the current partition interval. -/
private theorem satisfies_plain_eventually_iff_reset_upper_of_valid_position
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ⱼ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ⱼ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  constructor
  · intro h
    let b := (P.interval ⟨k.1, hk⟩).leftBoundary
    refine ⟨b, ?_⟩
    exact (satisfies_plain_eventually_iff_reset_upper_of_marker
      σ P α k hk c b I φ rfl).1 h
  · rintro ⟨b, h⟩
    have hb : b = (P.interval ⟨k.1, hk⟩).leftBoundary := by
      have hmarker : (P.interval ⟨k.1, hk⟩).leftBoundary = b := by
        change
          (if hp : k.1 < P.size then
            (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ᵢ
              (↑[c, b] ◇[I] φ)
          else False) ∧
            (if hp : k.1 < P.size then
              (P.interval ⟨k.1, hp⟩).leftBoundary = b
            else b = ●) at h
        exact (by simpa only [dif_pos hk] using h.2)
      exact hmarker.symm
    exact (satisfies_plain_eventually_iff_reset_upper_of_marker
      σ P α k hk c b I φ hb).2 h

/-- Eventuality instance of Proposition 3.10 (1), including the terminal
position. The marker is bound existentially and checked solely by `lty[b]`. -/
theorem satisfies_plain_eventually_iff_reset_upper
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ⱼ
      ((IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ⱼ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  by_cases hk : k.1 < P.size
  · exact satisfies_plain_eventually_iff_reset_upper_of_valid_position
      σ P α k hk c I φ
  · simp [Satisfies, hk]

/-- Proven direction of the always instance of Proposition 3.10 (1).
Marker selection remains internal to judgement satisfaction. -/
theorem reset_upper_always_implies_plain
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    (∃ b : Marker,
      ((σ, P, α, k) ⊨ⱼ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] □[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b])))) →
    ((σ, P, α, k) ⊨ⱼ
      ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) := by
  by_cases hk : k.1 < P.size
  · rintro ⟨b, h⟩
    change
      (if hp : k.1 < P.size then
        (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ᵢ
          (↑[c, b] □[I] φ)
      else False) ∧
        (if hp : k.1 < P.size then
          (P.interval ⟨k.1, hp⟩).leftBoundary = b
        else b = ●) at h
    simp only [dif_pos hk] at h
    change
      (if hp : k.1 < P.size then
        (σ, P.interval ⟨k.1, hp⟩, α) ⊨ᵢ
          IntervalPredicate.plain (□[(I : TimeInterval)] φ)
      else False)
    rw [dif_pos hk]
    exact IntervalPredicate.satisfies_plain_always_of_upper_of_zero
      σ (P.interval ⟨k.1, hk⟩) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
      (by simp) h.2.symm h.1
  · simp [Satisfies, hk]

/-- Complete satisfaction-level always characterization corresponding to
Proposition 3.10 (1). -/
theorem satisfies_plain_always_iff_reset_upper
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((σ, P, α, k) ⊨ⱼ
      ((IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
        IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ b : Marker,
      ((σ, P, α, k) ⊨ⱼ
        (⟦c ↦ᶜ 0⟧ ·ⱼ
          ((↑[c, b] □[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[b]))) := by
  constructor
  · intro h
    by_cases hk : k.1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let b := (P.interval i).leftBoundary
      have hplain : (σ, P.interval i, ⟦c ↦ᶜ 0⟧.apply α) ⊨ᵢ
          IntervalPredicate.plain (□[(I : TimeInterval)] φ) := by
        have h' : (σ, P.interval ⟨k.1, hk⟩, α) ⊨ᵢ
            IntervalPredicate.plain (□[(I : TimeInterval)] φ) := by
          change (if hp : k.1 < P.size then
            (σ, P.interval ⟨k.1, hp⟩, α) ⊨ᵢ
              IntervalPredicate.plain (□[(I : TimeInterval)] φ)
            else False) at h
          simpa only [dif_pos hk] using h
        simpa [i, IntervalPredicate.Satisfies] using h'
      have hJ : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ht⟩
      have hupper := (IntervalPredicate.satisfies_plain_always_iff_upper_of_zero
        σ (P.interval i) (⟦c ↦ᶜ 0⟧.apply α) c b I φ
        (by simp) rfl (P.nonempty i) hJ).1 hplain
      refine ⟨b, ?_⟩
      change
        (if hp : k.1 < P.size then
          (σ, P.interval ⟨k.1, hp⟩, ⟦c ↦ᶜ 0⟧.apply α) ⊨ᵢ
            (↑[c, b] □[I] φ)
        else False) ∧
          (if hp : k.1 < P.size then
            (P.interval ⟨k.1, hp⟩).leftBoundary = b
          else b = ●)
      simp only [dif_pos hk]
      exact ⟨hupper, rfl⟩
    · simp [Satisfies, hk] at h
  · exact reset_upper_always_implies_plain σ P α k c I φ

/-- Part (1), with the marker fixed before the semantic context. -/
theorem satisfies_plain_always_iff_reset_upper_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c : Clock) (m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary) :
    ((σ,P,α,k) ⊨ⱼ (Judgement.predicate (.plain (□[(I : TimeInterval)] φ)))) ↔
    ((σ,P,α,k) ⊨ⱼ (⟦c ↦ᶜ 0⟧ ·ⱼ
      ((↑[c,m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m]))) := by
  rw [satisfies_plain_always_iff_reset_upper]
  constructor
  · rintro ⟨b, hb⟩
    have heq : (P.interval ⟨k.1, hk⟩).leftBoundary = b := by
      simpa only [Satisfies, dif_pos hk] using hb.2
    simpa only [hm.trans heq] using hb
  · intro h
    exact ⟨m, h⟩

/-- Fixed-marker judgement equivalence. The same marker test is included
on the left, so this is an unrestricted `Equivalent`, not an existential
choice of a marker after the context has been selected. -/
theorem plain_eventually_fixed_marker_equiv [DecidableEq Clock]
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain (◇[(I : TimeInterval)] φ)) ∧ⱼ lty[m]) ≡ⱼ
      (⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) := by
  intro σ P α k
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_plain_eventually_iff_reset_upper_of_marker
        σ P α k hk c m I φ hm
      simpa only [Satisfies, dif_pos hk, hm, and_true] using h
    · simp [Satisfies, hk, Ne.symm hm]
  · simp [Satisfies, hk]

theorem plain_always_fixed_marker_equiv [DecidableEq Clock]
    (c : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Judgement.predicate (.plain (□[(I : TimeInterval)] φ)) ∧ⱼ lty[m]) ≡ⱼ
      (⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) := by
  intro σ P α k
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_plain_always_iff_reset_upper_of_marker
        σ P α k hk c m I φ hm
      simpa only [Satisfies, dif_pos hk, hm, and_true] using h
    · simp [Satisfies, hk, Ne.symm hm]
  · simp [Satisfies, hk]

/-- Split a predicate for eventually in the `↑` form into an `↑↓` predicate
and an unclocked predicate for the current interval. The judgement
`lty[m]` selects the current marker. -/
theorem satisfies_upper_eventually_iff_reset_bounded_and_plain
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hmarker : (α c : ℝ) = 0 →
      (P.interval ⟨k.1, hk⟩).leftBoundary.Includes → b.Includes) :
    ((σ, P, α, k) ⊨ⱼ
      ((↑[c, b] ◇[I] φ : IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ m : Marker,
      ((σ, P, α, k) ⊨ⱼ
        ((⟦d ↦ᶜ 0⟧ ·ⱼ
          ((↑↓[c, d, b, ¬ₘ m] ◇[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
          (IntervalPredicate.plain (◇[(I : TimeInterval)] φ) :
            IntervalPredicate Clock Var))) := by
  let i : Fin P.size := ⟨k.1, hk⟩
  let J := P.interval i
  let β := ⟦d ↦ᶜ 0⟧.apply α
  have hβc : β c = α c := by
    exact ClockResetSet.apply_singleton_of_ne (c := d) (d := c) 0 α hcd
  have hDomain : J.carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hUpper : ((σ, J, α) ⊨ᵢ (↑[c, b] ◇[I] φ)) ↔
      ((σ, J, β) ⊨ᵢ (↑[c, b] ◇[I] φ)) := by
    apply predicate_satisfies_congr
    intro e he
    have : e = c := by simpa [predicateClocks] using he
    subst e
    exact hβc.symm
  have hcore := IntervalPredicate.satisfies_upper_eventually_iff_bounded_and_plain
    σ J β c d b I φ (by simp [β]) (P.nonempty i)
    (by
      intro hc hm
      apply hmarker
      · simpa [hβc] using hc
      · exact hm)
    hDomain
  simp only [Satisfies, dif_pos hk]
  dsimp [i, J] at hUpper hcore ⊢
  constructor
  · intro h
    obtain ⟨hbounded, hplain⟩ := hcore.1 (hUpper.1 h)
    refine ⟨(P.interval ⟨k.1, hk⟩).leftBoundary, ?_⟩
    exact ⟨⟨hbounded, rfl⟩, hplain⟩
  · rintro ⟨m, ⟨⟨hbounded, hm⟩, hplain⟩⟩
    subst m
    exact hUpper.2 (hcore.2 ⟨hbounded, hplain⟩)

/-- Split a predicate for always in the `↑` form into an `↑↓` predicate
and an unclocked predicate for the current interval. -/
theorem satisfies_upper_always_iff_reset_bounded_and_plain
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hmarker : (α c : ℝ) = 0 →
      (P.interval ⟨k.1, hk⟩).leftBoundary.Includes → b.Includes) :
    ((σ, P, α, k) ⊨ⱼ
      ((↑[c, b] □[I] φ : IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ∃ m : Marker,
      ((σ, P, α, k) ⊨ⱼ
        ((⟦d ↦ᶜ 0⟧ ·ⱼ
          ((↑↓[c, d, b, ¬ₘ m] □[I] φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
          (IntervalPredicate.plain (□[(I : TimeInterval)] φ) :
            IntervalPredicate Clock Var))) := by
  let i : Fin P.size := ⟨k.1, hk⟩
  let J := P.interval i
  let β := ⟦d ↦ᶜ 0⟧.apply α
  have hβc : β c = α c := by
    exact ClockResetSet.apply_singleton_of_ne (c := d) (d := c) 0 α hcd
  have hDomain : J.carrier ⊆ σ.domain := by
    intro t ht
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ht⟩
  have hUpper : ((σ, J, α) ⊨ᵢ (↑[c, b] □[I] φ)) ↔
      ((σ, J, β) ⊨ᵢ (↑[c, b] □[I] φ)) := by
    apply predicate_satisfies_congr
    intro e he
    have : e = c := by simpa [predicateClocks] using he
    subst e
    exact hβc.symm
  have hcore := IntervalPredicate.satisfies_upper_always_iff_bounded_and_plain
    σ J β c d b I φ (by simp [β]) (P.nonempty i)
    (by
      intro hc hm
      apply hmarker
      · simpa [hβc] using hc
      · exact hm)
    hDomain
  simp only [Satisfies, dif_pos hk]
  dsimp [i, J] at hUpper hcore ⊢
  constructor
  · intro h
    obtain ⟨hbounded, hplain⟩ := hcore.1 (hUpper.1 h)
    refine ⟨(P.interval ⟨k.1, hk⟩).leftBoundary, ?_⟩
    exact ⟨⟨hbounded, rfl⟩, hplain⟩
  · rintro ⟨m, ⟨⟨hbounded, hm⟩, hplain⟩⟩
    subst m
    exact hUpper.2 (hcore.2 ⟨hbounded, hplain⟩)

/-- Split the `↑` form into `↑↓` and unclocked predicates at a fixed current
marker, assuming endpoint compatibility. -/
theorem satisfies_upper_eventually_iff_reset_bounded_and_plain_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hmarker : (α c : ℝ) = 0 → m.Includes → b.Includes) :
    ((σ,P,α,k) ⊨ⱼ ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ((σ,P,α,k) ⊨ⱼ ((⟦d ↦ᶜ 0⟧ ·ⱼ
      ((↑↓[c,d,b,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
      (IntervalPredicate.plain (◇[(I : TimeInterval)] φ) : IntervalPredicate Clock Var))) := by
  rw [satisfies_upper_eventually_iff_reset_bounded_and_plain
    σ P α k hk c d b I φ hcd (by simpa only [← hm] using hmarker)]
  constructor
  · rintro ⟨q, hq⟩
    have heq : (P.interval ⟨k.1, hk⟩).leftBoundary = q := by
      simpa only [Satisfies, dif_pos hk] using hq.1.2
    simpa only [hm.trans heq] using hq
  · intro h
    exact ⟨m, h⟩

/-- Split the `↑` form into `↑↓` and unclocked predicates at a fixed current
marker, assuming endpoint compatibility. -/
theorem satisfies_upper_always_iff_reset_bounded_and_plain_of_marker
    [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Position P) (hk : k.1 < P.size) (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary)
    (hmarker : (α c : ℝ) = 0 → m.Includes → b.Includes) :
    ((σ,P,α,k) ⊨ⱼ ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var)) ↔
    ((σ,P,α,k) ⊨ⱼ ((⟦d ↦ᶜ 0⟧ ·ⱼ
      ((↑↓[c,d,b,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
      (IntervalPredicate.plain (□[(I : TimeInterval)] φ) : IntervalPredicate Clock Var))) := by
  rw [satisfies_upper_always_iff_reset_bounded_and_plain
    σ P α k hk c d b I φ hcd (by simpa only [← hm] using hmarker)]
  constructor
  · rintro ⟨q, hq⟩
    have heq : (P.interval ⟨k.1, hk⟩).leftBoundary = q := by
      simpa only [Satisfies, dif_pos hk] using hq.1.2
    simpa only [hm.trans heq] using hq
  · intro h
    exact ⟨m, h⟩

/-- Split the `↑` form into `↑↓` and unclocked predicates with a current-marker
test. See `upper_split_equiv` for the split with matching stored markers. -/
theorem upper_eventually_fixed_marker_equiv [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) :
    EquivalentUnder (Clock := Clock) (Var := Var) (fun α => (α c : ℝ) = 0 → m.Includes → b.Includes)
      ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])
      ((⟦d ↦ᶜ 0⟧ ·ⱼ
        ((↑↓[c,d,b,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
        (IntervalPredicate.plain (◇[(I : TimeInterval)] φ) : IntervalPredicate Clock Var)) := by
  intro σ P α k hmarker
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_upper_eventually_iff_reset_bounded_and_plain_of_marker
        σ P α k hk c d b m I φ hcd hm hmarker
      simpa only [Satisfies, dif_pos hk, hm, and_true] using h
    · simp [Satisfies, hk, Ne.symm hm]
  · simp [Satisfies, hk]

/-- Split the `↑` form into `↑↓` and unclocked predicates with a current-marker
test. See `upper_split_equiv` for the split with matching stored markers. -/
theorem upper_always_fixed_marker_equiv [DecidableEq Clock]
    (c d : Clock) (b m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) :
    EquivalentUnder (Clock := Clock) (Var := Var) (fun α => (α c : ℝ) = 0 → m.Includes → b.Includes)
      ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])
      ((⟦d ↦ᶜ 0⟧ ·ⱼ
        ((↑↓[c,d,b,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m])) ∧ⱼ
        (IntervalPredicate.plain (□[(I : TimeInterval)] φ) : IntervalPredicate Clock Var)) := by
  intro σ P α k hmarker
  by_cases hk : k.1 < P.size
  · by_cases hm : m = (P.interval ⟨k.1, hk⟩).leftBoundary
    · have h := satisfies_upper_always_iff_reset_bounded_and_plain_of_marker
        σ P α k hk c d b m I φ hcd hm hmarker
      simpa only [Satisfies, dif_pos hk, hm, and_true] using h
    · simp [Satisfies, hk, Ne.symm hm]
  · simp [Satisfies, hk]

/-- Eventuality case of Lemma 3.11 (1), at a valid
partition position, including singleton pieces. -/
theorem satisfies_bounded_eventually_of_upper_at
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (hk : k.1 < P.size)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (σ,P,α,k)⊨ⱼ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) :
        Judgement Clock Var) := by
  simp only [Satisfies, dif_pos hk] at h ⊢
  exact IntervalPredicate.satisfies_bounded_eventually_of_upper
    σ (P.interval ⟨k.1, hk⟩) α c d b b' I φ (P.nonempty _) h

/-- Always case of Lemma 3.11 (1), at a valid
partition position, including singleton pieces. -/
theorem satisfies_bounded_always_of_upper_at
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (hk : k.1 < P.size)
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (σ,P,α,k)⊨ⱼ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,b']□[I]φ : IntervalPredicate Clock Var) :
        Judgement Clock Var) := by
  simp only [Satisfies, dif_pos hk] at h ⊢
  exact IntervalPredicate.satisfies_bounded_always_of_upper
    σ (P.interval ⟨k.1, hk⟩) α c d b b' I φ (P.nonempty _) h

/-- Lemma 3.11(2) at consecutive partition intervals. Satisfaction of the next
eventually predicate in the `↑` form entails satisfaction of the same
predicate at the current position. -/
theorem satisfies_upper_eventually_of_next_at
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (hkNext : k.1 + 1 < P.size) (c : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (σ,P,α,k)⊨ⱼ(Xⱼ
      ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var))) :
    (σ,P,α,k)⊨ⱼ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hkNext⟩
  let β := ClockResetSet.elapse α (duration P i)
  have hadj : (P.interval i).right = (P.interval j).left := by
    simpa [i, j] using P.adjacent_right_eq_left i (by simpa [i] using hkNext)
  have hleft : (P.interval i).left - (α c : ℝ) =
      (P.interval j).left - (β c : ℝ) := by
    exact (next_left_sub_elapse_eq P α i (by simpa [i] using hkNext) c).symm
  have hm : (P.interval i).rightBoundary =
      Marker.complement (P.interval j).leftBoundary :=
    P.adjacent_rightBoundary_eq_complement_leftBoundary i hkNext
  simp only [Satisfies, dif_pos hk, dif_pos hkNext] at h ⊢
  exact IntervalPredicate.satisfies_upper_eventually_of_adjacent
    σ (P.interval i) (P.interval j) α β c b I φ
    (P.nonempty i) (P.nonempty j) hadj hm hleft h

/-- Lemma 3.11 (3) at consecutive partition positions,
including singleton pieces. Both clock-shifted endpoints are preserved. -/
theorem satisfies_bounded_eventually_of_next_at
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (hkNext : k.1 + 1 < P.size) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (σ,P,α,k)⊨ⱼ(Xⱼ
      ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var))) :
    (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hkNext⟩
  let β := ClockResetSet.elapse α (duration P i)
  have hadj : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i hkNext
  have hc : (P.interval i).left - (α c : ℝ) =
      (P.interval j).left - (β c : ℝ) :=
    (next_left_sub_elapse_eq P α i hkNext c).symm
  have hd : (P.interval i).left - (α d : ℝ) =
      (P.interval j).left - (β d : ℝ) :=
    (next_left_sub_elapse_eq P α i hkNext d).symm
  simp only [Satisfies, dif_pos hk, dif_pos hkNext] at h ⊢
  exact IntervalPredicate.satisfies_bounded_eventually_of_next
    σ (P.interval i) (P.interval j) α β c d b b' I φ hc hd
    (fun _ ht => IntervalPredicate.inCurrentSuffix_of_adjacent
      (P.interval i) (P.interval j) (P.nonempty i) hadj ht) h

/-- The unconditional judgement implication in
Lemma 3.11 (3). At terminal positions the premise is false. -/
theorem next_bounded_eventually_implies_bounded
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Xⱼ ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) ⇒ⱼ
      ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hkNext : k.1 + 1 < P.size
  · exact satisfies_bounded_eventually_of_next_at σ P α k hkNext c d b b' I φ h
  · by_cases hk : k.1 < P.size
    · simp only [Satisfies, dif_pos hk, dif_neg hkNext] at h
    · simp only [Satisfies, dif_neg hk] at h

/-- The full judgement implication of Lemma 3.11 (2),
including singleton intervals and terminal positions. -/
theorem next_upper_eventually_implies_upper
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (Xⱼ ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) ⇒ⱼ
      ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hkNext : k.1 + 1 < P.size
  · exact satisfies_upper_eventually_of_next_at σ P α k hkNext c b I φ h
  · by_cases hk : k.1 < P.size
    · simp only [Satisfies, dif_pos hk, dif_neg hkNext] at h
    · simp only [Satisfies, dif_neg hk] at h

/-- Lemma 3.11 (4), with freshness of the reset clock
explicit. The marker is fixed in the judgement and checked by `lty[m]`. -/
theorem next_reset_bounded_eventually_implies_upper
    [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    (Xⱼ (⟦d ↦ᶜ 0⟧ ·ⱼ
      ((↑↓[c,d,b,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m]))) ⇒ⱼ
      ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      let γ := ClockResetSet.elapse α (duration P i)
      let β := (⟦d ↦ᶜ 0⟧).apply γ
      have hβc : β c = γ c :=
        ClockResetSet.apply_singleton_of_ne 0 γ hcd
      have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hc : (P.interval i).left - (α c : ℝ) =
          (P.interval j).left - (β c : ℝ) := by
        rw [hβc]
        exact (next_left_sub_elapse_eq P α i hn c).symm
      have hd : (P.interval i).right = (P.interval j).left - (β d : ℝ) := by
        simpa only [hβd, NNReal.coe_zero, sub_zero] using hadj
      simp only [Satisfies, dif_pos hk, dif_pos hn] at h ⊢
      have hm : (P.interval i).rightBoundary = Marker.complement m := by
        have hboundary := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
        exact hboundary.trans (congrArg Marker.complement h.2)
      exact IntervalPredicate.satisfies_upper_eventually_of_bounded_next
        σ (P.interval i) (P.interval j) α β c d b (¬ₘ m) I φ hc hd hm
        (fun _ ht => IntervalPredicate.inCurrentSuffix_of_adjacent
          (P.interval i) (P.interval j) (P.nonempty i) hadj ht) h.1
    · simp [Satisfies, hk, hn] at h
  · simp only [Satisfies, dif_neg hk] at h

/-- Transfer an always predicate in the `↑↓` form between consecutive partition
intervals. The next interval can be a singleton. -/
theorem satisfies_next_bounded_always_of_current_at
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (hn : k.1 + 1 < P.size) (c d : Clock) (b b' : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (h : (σ,P,α,k)⊨ⱼ((↑↓[c,d,b,b']□[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) :
    (σ,P,α,k)⊨ⱼ(Xⱼ
      ((↑↓[c,d,b,b']□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var)) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let β := ClockResetSet.elapse α (duration P i)
  have hadj : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i hn
  have hc : (P.interval i).left - (α c : ℝ) =
      (P.interval j).left - (β c : ℝ) :=
    (next_left_sub_elapse_eq P α i hn c).symm
  have hd : (P.interval i).left - (α d : ℝ) =
      (P.interval j).left - (β d : ℝ) :=
    (next_left_sub_elapse_eq P α i hn d).symm
  simp only [Satisfies, dif_pos hk, dif_pos hn] at h ⊢
  exact IntervalPredicate.satisfies_bounded_always_next_of_current
    σ (P.interval i) (P.interval j) α β c d b b' I φ hc hd
    (fun _ ht => IntervalPredicate.inCurrentSuffix_of_adjacent
      (P.interval i) (P.interval j) (P.nonempty i) hadj ht) h

/-- Satisfaction-level form of the always-transition lemma in the supplementary proof (1).
The next interval exists, the reset clock is fresh, and the next marker is
existentially selected rather than fixed outside all semantic contexts. -/
theorem satisfies_next_reset_bounded_always_of_upper_at
    [DecidableEq Clock] (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (hn : k.1 + 1 < P.size) (c d : Clock) (b : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (h : (σ,P,α,k)⊨ⱼ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) :
      Judgement Clock Var)) :
    ∃ m : Marker, (σ,P,α,k)⊨ⱼ(Xⱼ (⟦d ↦ᶜ 0⟧ ·ⱼ
      ((↑↓[c,d,b,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[m]))) := by
  have hk : k.1 < P.size := by omega
  let i : Fin P.size := ⟨k.1, hk⟩
  let j : Fin P.size := ⟨k.1 + 1, hn⟩
  let γ := ClockResetSet.elapse α (duration P i)
  let β := (⟦d ↦ᶜ 0⟧).apply γ
  have hβc : β c = γ c := ClockResetSet.apply_singleton_of_ne 0 γ hcd
  have hβd : β d = 0 := ClockResetSet.apply_singleton_self d 0 γ
  have hadj : (P.interval i).right = (P.interval j).left :=
    P.adjacent_right_eq_left i hn
  have hc : (P.interval i).left - (α c : ℝ) =
      (P.interval j).left - (β c : ℝ) := by
    rw [hβc]
    exact (next_left_sub_elapse_eq P α i hn c).symm
  have hd : (P.interval i).right = (P.interval j).left - (β d : ℝ) := by
    simpa only [hβd, NNReal.coe_zero, sub_zero] using hadj
  have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
  refine ⟨(P.interval j).leftBoundary, ?_⟩
  simp only [Satisfies, dif_pos hk, dif_pos hn] at h ⊢
  refine ⟨?_, rfl⟩
  exact IntervalPredicate.satisfies_bounded_always_next_of_upper
    σ (P.interval i) (P.interval j) α β c d b
    (¬ₘ (P.interval j).leftBoundary) I φ hc hd hm
    (fun _ ht => IntervalPredicate.inCurrentSuffix_of_adjacent
      (P.interval i) (P.interval j) (P.nonempty i) hadj ht) h

/-- Full eventuality case of Lemma 3.11 (1). -/
theorem upper_eventually_implies_bounded
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((↑[c,b]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) ⇒ⱼ
      ((↑↓[c,d,b,b']◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · exact satisfies_bounded_eventually_of_upper_at σ P α k hk c d b b' I φ h
  · simp only [Satisfies, dif_neg hk] at h

/-- Full always case of Lemma 3.11 (1). -/
theorem upper_always_implies_bounded
    (c d : Clock) (b b' : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    ((↑[c,b]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) ⇒ⱼ
      ((↑↓[c,d,b,b']□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · exact satisfies_bounded_always_of_upper_at σ P α k hk c d b b' I φ h
  · simp only [Satisfies, dif_neg hk] at h

/-- Judgement-level eventually case of Lemma 3.12, including terminal positions. -/
theorem satisfies_eventually_merge_iff
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    ((σ,P,α,k)⊨ⱼ
      ((↑↓[c₁,d₁,b₁,q₁]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ
        (↑[c₂,b₂]◇[I]φ : IntervalPredicate Clock Var))) ↔
      ((σ,P,α,k)⊨ⱼ((↑[c₁,b₁]◇[I]φ : IntervalPredicate Clock Var) :
        Judgement Clock Var)) := by
  by_cases hk : k.1 < P.size
  · simp only [Satisfies, dif_pos hk]
    exact IntervalPredicate.satisfies_eventually_merge_iff
      σ (P.interval ⟨k.1, hk⟩) α c₁ d₁ c₂ b₁ q₁ b₂ I φ
      (P.nonempty _) hleft hjoin
  · simp [Satisfies, hk]

/-- Judgement-level always case of Lemma 3.12, including terminal positions. -/
theorem satisfies_always_merge_iff
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (I : BoundedTimeInterval) (φ : Formula Var)
    (hleft : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)))
    (hjoin : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes))) :
    ((σ,P,α,k)⊨ⱼ
      ((↑↓[c₁,d₁,b₁,q₁]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ
        (↑[c₂,b₂]□[I]φ : IntervalPredicate Clock Var))) ↔
      ((σ,P,α,k)⊨ⱼ((↑[c₁,b₁]□[I]φ : IntervalPredicate Clock Var) :
        Judgement Clock Var)) := by
  by_cases hk : k.1 < P.size
  · simp only [Satisfies, dif_pos hk]
    exact IntervalPredicate.satisfies_always_merge_iff
      σ (P.interval ⟨k.1, hk⟩) α c₁ d₁ c₂ b₁ q₁ b₂ I φ
      (P.nonempty _) hleft hjoin
  · simp [Satisfies, hk]

/-- Under residual satisfaction, a predicate in the `↑` form splits into `↑↓`
and `↑` predicates with the same stored left marker. The reset uses a
distinct clock. -/
theorem upper_split_equiv [DecidableEq Clock]
    (c d : Clock) (m : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    (Judgement.predicate (.upper c m kind I φ)) ≡ⱼ
      (⟦d ↦ᶜ 0⟧ ·ⱼ
        ((Judgement.predicate (.bounded c d m (¬ₘ m) kind I φ)) ∧ⱼ
         (Judgement.predicate (.upper d m kind I φ)))) := by
  intro σ P α k
  let β := (⟦d ↦ᶜ 0⟧).apply α
  have hc : β c = α c := ClockResetSet.apply_singleton_of_ne 0 α hcd
  have hd : β d = 0 := ClockResetSet.apply_singleton_self d 0 α
  have hleft : (β d : ℝ) < β c ∨
      ((β d : ℝ) = β c ∧ (m.Includes → m.Includes)) := by
    rw [hd]
    rcases (β c).coe_nonneg.eq_or_lt with h | h
    · exact Or.inr ⟨h, id⟩
    · exact Or.inl h
  have hjoin : (β d : ℝ) < β d ∨
      ((β d : ℝ) = β d ∧ ((¬ₘ m).Includes ∨ m.Includes)) := by
    right
    refine ⟨rfl, ?_⟩
    cases m <;> simp
  change Judgement.Satisfies σ P α k (.predicate (.upper c m kind I φ)) ↔
    Judgement.Satisfies σ P β k
      ((.predicate (.bounded c d m (¬ₘ m) kind I φ)) ∧ⱼ
       (.predicate (.upper d m kind I φ)))
  have hkeep : Judgement.Satisfies σ P α k (.predicate (.upper c m kind I φ)) ↔
      Judgement.Satisfies σ P β k (.predicate (.upper c m kind I φ)) := by
    apply Judgement.satisfies_congr_of_agree
    intro e he
    have hec : e = c := by
      simpa [Judgement.freeClocks, Judgement.predicateClocks] using he
    subst e
    exact hc.symm
  rw [hkeep]
  cases kind with
  | always =>
      exact (Judgement.satisfies_always_merge_iff
        σ P β k c d d m (¬ₘ m) m I φ hleft hjoin).symm
  | eventually =>
      exact (Judgement.satisfies_eventually_merge_iff
        σ P β k c d d m (¬ₘ m) m I φ hleft hjoin).symm

/-- Eventually instance of Proposition 3.10 (2). -/
theorem upper_eventually_split_equiv [DecidableEq Clock]
    (c d : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) :
    ((↑[c,m]◇[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) ≡ⱼ
      (⟦d ↦ᶜ 0⟧ ·ⱼ
        ((↑↓[c,d,m,¬ₘ m]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ
         (↑[d,m]◇[I]φ : IntervalPredicate Clock Var))) :=
  upper_split_equiv c d m .eventually I φ hcd

/-- Always instance of Proposition 3.10 (2). -/
theorem upper_always_split_equiv [DecidableEq Clock]
    (c d : Clock) (m : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hcd : c ≠ d) :
    ((↑[c,m]□[I]φ : IntervalPredicate Clock Var) : Judgement Clock Var) ≡ⱼ
      (⟦d ↦ᶜ 0⟧ ·ⱼ
        ((↑↓[c,d,m,¬ₘ m]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ
         (↑[d,m]□[I]φ : IntervalPredicate Clock Var))) :=
  upper_split_equiv c d m .always I φ hcd

end Judgement

end STLTableau
