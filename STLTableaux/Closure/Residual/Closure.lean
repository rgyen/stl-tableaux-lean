/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Rules.Catalogue.ClockedExpansion

/-!
# Transition forms and closures

Transition forms, syntactic subsumption, and closure for residual satisfaction.
A transition form has the six components of Definition 4.1.
-/

namespace STLTableau

open scoped STL

namespace Formula

variable {Var : Type*}

/-- Definition 4.10 for STL formulas. Negation does not increase
the measure; Boolean binary and temporal operators contribute two. This also
gives the stated equations for the derived `∨`, `R`, `◇`, and `□`
operators despite their definitional encoding in the core syntax. -/
def complexity : Formula Var → ℕ
  | .truth | .atom _ => 0
  | .neg φ => complexity φ
  | .and φ ψ | .until _ φ ψ => complexity φ + complexity ψ + 2

@[simp] theorem complexity_neg (φ : Formula Var) :
    complexity (¬ₛ φ) = complexity φ := rfl

@[simp] theorem complexity_and (φ ψ : Formula Var) :
    complexity (φ ∧ₛ ψ) = complexity φ + complexity ψ + 2 := rfl

@[simp] theorem complexity_or (φ ψ : Formula Var) :
    complexity (Formula.or φ ψ) = complexity φ + complexity ψ + 2 := by
  simp [Formula.or, complexity, Nat.add_comm]

@[simp] theorem complexity_until (I : TimeInterval) (φ ψ : Formula Var) :
    complexity (φ U[I] ψ) = complexity φ + complexity ψ + 2 := rfl

@[simp] theorem complexity_release (I : TimeInterval) (φ ψ : Formula Var) :
    complexity (φ R[I] ψ) = complexity φ + complexity ψ + 2 := by
  simp [Formula.release, complexity]

@[simp] theorem complexity_eventually (I : TimeInterval) (φ : Formula Var) :
    complexity (◇[I] φ) = complexity φ + 2 := by
  simp [Formula.eventually, complexity]

@[simp] theorem complexity_always (I : TimeInterval) (φ : Formula Var) :
    complexity (□[I] φ) = complexity φ + 2 := by
  simp [Formula.always]

end Formula

namespace IntervalPredicate

variable {Clock Var : Type*}

/-- Definition 4.10 for interval predicates. Clocked predicate
constructors contribute one beyond the complexity of their operand. -/
def complexity : IntervalPredicate Clock Var → ℕ
  | .plain φ => φ.complexity
  | .upper _ _ _ _ φ | .bounded _ _ _ _ _ _ φ => φ.complexity + 1

@[simp] theorem complexity_plain (φ : Formula Var) :
    complexity (.plain φ : IntervalPredicate Clock Var) = φ.complexity := rfl

@[simp] theorem complexity_upper (c : Clock) (b : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    complexity (.upper c b kind I φ) = φ.complexity + 1 := rfl

@[simp] theorem complexity_bounded (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) :
    complexity (.bounded c d b q kind I φ) = φ.complexity + 1 := rfl

end IntervalPredicate

namespace Judgement

variable {Clock Var : Type*}

/-- Interval predicates occurring in the current part of a branch. Resets do
not change the syntactic position; `next` cuts off the traversal. -/
def currentPredicates : Judgement Clock Var → Set (IntervalPredicate Clock Var)
  | .predicate p => {p}
  | .reset _ Ψ => currentPredicates Ψ
  | .conj Φ Ψ => currentPredicates Φ ∪ currentPredicates Ψ
  | .terminal | .clock _ _ _ | .leftMarker _ | .next _ => ∅

end Judgement

namespace ExpansionRule

variable {Clock Var : Type*}

/-- Lemma 4.11 as a property of one concrete expansion
rule. -/
def ComplexityReduced (R : ExpansionRule Clock Var) : Prop :=
  ∀ Ψ ∈ R.branches, ∀ q ∈ Ψ.currentPredicates,
    q.complexity < R.source.complexity

theorem plainAnd_complexityReduced (φ ψ : Formula Var) :
    (plainAnd (Clock := Clock) φ ψ).ComplexityReduced := by
  simp [ComplexityReduced, plainAnd, Judgement.currentPredicates]
  omega

theorem plainOr_complexityReduced (φ ψ : Formula Var) :
    (plainOr (Clock := Clock) φ ψ).ComplexityReduced := by
  simp [ComplexityReduced, plainOr, Judgement.currentPredicates]
  omega

theorem plainUntil_complexityReduced (φ ψ : Formula Var) :
    (plainUntil (Clock := Clock) φ ψ).ComplexityReduced := by
  simp [ComplexityReduced, plainUntil, Formula.untimedUntil,
    Judgement.currentPredicates]
  omega

theorem plainRelease_complexityReduced (φ ψ : Formula Var) :
    (plainRelease (Clock := Clock) φ ψ).ComplexityReduced := by
  simp [ComplexityReduced, plainRelease, Judgement.currentPredicates]
  omega

theorem openEventually_complexityReduced [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (openEventually c I φ).ComplexityReduced := by
  simp [ComplexityReduced, openEventually, Judgement.currentPredicates]

theorem openAlways_complexityReduced [DecidableEq Clock] (c : Clock)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (openAlways c I φ).ComplexityReduced := by
  simp [ComplexityReduced, openAlways, Judgement.currentPredicates]

theorem upperAlways_complexityReduced [DecidableEq Clock] (c d : Clock)
    (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (upperAlways c d b I φ).ComplexityReduced := by
  simp [ComplexityReduced, upperAlways, upperAlways_defer, upperAlways_check,
    Judgement.currentPredicates]

theorem boundedAlways_complexityReduced [DecidableEq Clock] (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedAlways c d b q I φ).ComplexityReduced := by
  simp [ComplexityReduced, boundedAlways, boundedAlways_defer, boundedAlways_check,
    boundedAlways_finish, Judgement.currentPredicates]

theorem boundedEventually_complexityReduced [DecidableEq Clock] (c d : Clock)
    (b q : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedEventually c d b q I φ).ComplexityReduced := by
  simp [ComplexityReduced, boundedEventually, boundedEventually_defer,
    boundedEventually_check, boundedEventually_finish, Judgement.currentPredicates]

theorem upperEventually_complexityReduced [DecidableEq Clock] (c d : Clock)
    (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) :
    (upperEventually c d b I φ).ComplexityReduced := by
  classical
  by_cases h : I.lower = 0
  · simp [ComplexityReduced, upperEventually, h, upperEventually_defer,
      Judgement.currentPredicates]
  · simp [ComplexityReduced, upperEventually, h, upperEventually_defer,
      upperEventually_check, Judgement.currentPredicates]

end ExpansionRule

/-- A clock constraint occurring in the `C` component of a state form. -/
structure ClockConstraint (Clock : Type*) where
  clock : Clock
  relation : ClockRelation
  value : NNReal

namespace ClockConstraint

variable {Clock Var : Type*}

/-- Interpret a clock constraint at a valuation. -/
def Satisfies (α : ClockValuation Clock) (g : ClockConstraint Clock) : Prop :=
  g.relation.Holds (α g.clock) g.value

/-- The judgement denoted by a clock constraint. -/
def judgement (g : ClockConstraint Clock) : Judgement Clock Var :=
  .clock g.clock g.relation g.value

end ClockConstraint

namespace Judgement

variable {Clock Var : Type*}

/-- Judgements allowed in the local component `L` of a state form. -/
def IsLocal : Judgement Clock Var → Prop
  | .terminal | .leftMarker _ | .predicate _ => True
  | _ => False

end Judgement

/-- A state form `C, Λ.L`.  The set representation makes exchange,
contraction, and associativity of conjunction structural rather than lemmas
about a chosen binary-conjunction tree. -/
structure StateForm (Clock Var : Type*) where
  constraints : Set (ClockConstraint Clock)
  constraints_finite : constraints.Finite
  resets : ClockResetSet Clock
  locals : Set (Judgement Clock Var)
  locals_finite : locals.Finite
  locals_are_local : ∀ Ψ ∈ locals, Ψ.IsLocal

namespace StateForm

variable {Clock Var : Type*}

/-- Number of finite syntactic components of a state form. -/
noncomputable def componentCount (S : StateForm Clock Var) : ℕ :=
  S.constraints.ncard + S.resets.clocks.ncard + S.locals.ncard

/-- Componentwise union of state forms. Reset union is left-biased;
semantic uses require consistency, as in Proposition 3.9. -/
def union (S T : StateForm Clock Var) : StateForm Clock Var where
  constraints := S.constraints ∪ T.constraints
  constraints_finite := S.constraints_finite.union T.constraints_finite
  resets := S.resets.union T.resets
  locals := S.locals ∪ T.locals
  locals_finite := S.locals_finite.union T.locals_finite
  locals_are_local := by
    intro Ψ hΨ
    exact hΨ.elim (S.locals_are_local Ψ) (T.locals_are_local Ψ)

@[simp] theorem constraints_union (S T : StateForm Clock Var) :
    (S.union T).constraints = S.constraints ∪ T.constraints := rfl

@[simp] theorem resets_union (S T : StateForm Clock Var) :
    (S.union T).resets = S.resets.union T.resets := rfl

@[simp] theorem locals_union (S T : StateForm Clock Var) :
    (S.union T).locals = S.locals ∪ T.locals := rfl

/-- Satisfaction of `C, Λ.L` at one partition position. -/
def Satisfies (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  (∀ g ∈ S.constraints, g.Satisfies α) ∧
    ∀ Ψ ∈ S.locals, (σ, P, S.resets.apply α, k) ⊨ⱼ Ψ

def NonPredicateSatisfies (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  (∀ g ∈ S.constraints, g.Satisfies α) ∧
    ∀ Ψ ∈ S.locals, Judgement.NonPredicateSatisfies σ P (S.resets.apply α) k Ψ

/-- Clocks whose incoming values can affect satisfaction of a state form.
Reset-bound occurrences are not free. -/
def freeClocks (S : StateForm Clock Var) : Set Clock :=
  (ClockConstraint.clock '' S.constraints) ∪
    (⋃ Ψ ∈ S.locals, Ψ.freeClocks \ S.resets.clocks)

/-- State-form satisfaction depends only on its free clocks. -/
theorem satisfies_congr_of_agree (S : StateForm Clock Var)
    {α β : ClockValuation Clock} (h : ∀ c ∈ S.freeClocks, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) :
    S.Satisfies σ P α k ↔ S.Satisfies σ P β k := by
  have forward : ∀ {γ δ : ClockValuation Clock},
      (∀ c ∈ S.freeClocks, γ c = δ c) →
      S.Satisfies σ P γ k → S.Satisfies σ P δ k := by
    intro γ δ hagree hs
    refine ⟨?_, ?_⟩
    · intro g hg
      simpa [ClockConstraint.Satisfies, hagree g.clock
        (Or.inl ⟨g, hg, rfl⟩)] using hs.1 g hg
    · intro Ψ hΨ
      apply (Judgement.satisfies_congr_of_agree (σ := σ) (P := P) (k := k) ?_).1
        (hs.2 Ψ hΨ)
      intro c hc
      cases hr : S.resets.value c with
      | some a => simp [ClockResetSet.apply, hr]
      | none =>
          have hcn : c ∉ S.resets.clocks := by
            rintro ⟨a, ha⟩
            rw [hr] at ha
            cases ha
          unfold ClockResetSet.apply
          rw [hr]
          exact hagree c (Or.inr (Set.mem_iUnion.2 ⟨Ψ,
            Set.mem_iUnion.2 ⟨hΨ, ⟨hc, hcn⟩⟩⟩))
  exact ⟨forward h, forward (fun c hc => (h c hc).symm)⟩

theorem nonPredicateSatisfies_congr_of_agree (S : StateForm Clock Var)
    {α β : ClockValuation Clock} (h : ∀ c ∈ S.freeClocks, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) :
    S.NonPredicateSatisfies σ P α k ↔ S.NonPredicateSatisfies σ P β k := by
  have forward : ∀ {γ δ : ClockValuation Clock},
      (∀ c ∈ S.freeClocks, γ c = δ c) →
      S.NonPredicateSatisfies σ P γ k → S.NonPredicateSatisfies σ P δ k := by
    intro γ δ hagree hs
    refine ⟨?_, ?_⟩
    · intro g hg
      simpa [ClockConstraint.Satisfies, hagree g.clock
        (Or.inl ⟨g, hg, rfl⟩)] using hs.1 g hg
    · intro Ψ hΨ
      apply (Judgement.nonPredicateSatisfies_congr_of_agree (σ := σ) (P := P) (k := k) ?_).1
        (hs.2 Ψ hΨ)
      intro c hc
      cases hr : S.resets.value c with
      | some a => simp [ClockResetSet.apply, hr]
      | none =>
          have hcn : c ∉ S.resets.clocks := by
            rintro ⟨a, ha⟩
            rw [hr] at ha
            cases ha
          unfold ClockResetSet.apply
          rw [hr]
          exact hagree c (Or.inr (Set.mem_iUnion.2 ⟨Ψ,
            Set.mem_iUnion.2 ⟨hΨ, ⟨hc, hcn⟩⟩⟩))
  exact ⟨forward h, forward (fun c hc => (h c hc).symm)⟩

/-- Extensionality of state forms; locality proofs are proof-irrelevant. -/
theorem ext {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints = S₂.constraints)
    (hΛ : S₁.resets = S₂.resets) (hL : S₁.locals = S₂.locals) : S₁ = S₂ := by
  cases S₁
  cases S₂
  simp_all

end StateForm

/-- Transition form with a current state and an optional next state. -/
structure TransitionForm (Clock Var : Type*) where
  current : StateForm Clock Var
  nextPart : Option (StateForm Clock Var)

namespace TransitionForm

variable {Clock Var : Type*}

/-- Number of finite syntactic components of a transition form. The extra
one distinguishes an existing next component from `none`. -/
noncomputable def componentCount (Φ : TransitionForm Clock Var) : ℕ :=
  Φ.current.componentCount + match Φ.nextPart with
    | none => 0
    | some N => N.componentCount + 1

/-- Merge optional next components, treating an absent next part as the
identity. -/
def unionNext : Option (StateForm Clock Var) → Option (StateForm Clock Var) →
    Option (StateForm Clock Var)
  | none, N | N, none => N
  | some S, some T => some (S.union T)

/-- The transition form constructed in the proof of Lemma 4.13:
all six corresponding components are united. -/
def union (Φ Ψ : TransitionForm Clock Var) : TransitionForm Clock Var where
  current := Φ.current.union Ψ.current
  nextPart := unionNext Φ.nextPart Ψ.nextPart

@[simp] theorem current_union (Φ Ψ : TransitionForm Clock Var) :
    (Φ.union Ψ).current = Φ.current.union Ψ.current := rfl

@[simp] theorem nextPart_union (Φ Ψ : TransitionForm Clock Var) :
    (Φ.union Ψ).nextPart = unionNext Φ.nextPart Ψ.nextPart := rfl

/-- Satisfaction of `C, Λ.(L, X(C', Λ'.L'))`. -/
def Satisfies (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  (∀ g ∈ Φ.current.constraints, g.Satisfies α) ∧
  (∀ Ψ ∈ Φ.current.locals,
    (σ, P, Φ.current.resets.apply α, k) ⊨ⱼ Ψ) ∧
  match Φ.nextPart with
  | none => True
  | some N =>
      if h : k.1 < P.size then
        let β := ClockResetSet.elapse (Φ.current.resets.apply α)
          (Judgement.duration P ⟨k.1, h⟩)
        N.Satisfies σ P β ⟨k.1 + 1, by omega⟩
      else False

def NonPredicateSatisfies (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  (∀ g ∈ Φ.current.constraints, g.Satisfies α) ∧
  (∀ Ψ ∈ Φ.current.locals,
    Judgement.NonPredicateSatisfies σ P (Φ.current.resets.apply α) k Ψ) ∧
  match Φ.nextPart with
  | none => True
  | some N =>
      if h : k.1 < P.size then
        let β := ClockResetSet.elapse (Φ.current.resets.apply α)
          (Judgement.duration P ⟨k.1, h⟩)
        N.NonPredicateSatisfies σ P β ⟨k.1 + 1, by omega⟩
      else False

/-- A state form is a transition form with an empty next part. -/
def ofState (S : StateForm Clock Var) : TransitionForm Clock Var :=
  ⟨S, none⟩

@[simp] theorem satisfies_ofState (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    (ofState S).Satisfies σ P α k ↔ S.Satisfies σ P α k := by
  simp [ofState, TransitionForm.Satisfies, StateForm.Satisfies]

end TransitionForm

namespace ClockResetSet

variable {Clock : Type*}

/-- Inclusion of reset graphs; in particular, common clocks have the same
assigned value.  This is the `Λ₁ ⊆ Λ₂` used in syntactic subsumption. -/
def Subset (Λ₁ Λ₂ : ClockResetSet Clock) : Prop :=
  ∀ c a, Λ₁.value c = some a → Λ₂.value c = some a

@[refl] theorem subset_refl (Λ : ClockResetSet Clock) : Λ.Subset Λ := by
  intro c a h
  exact h

theorem Subset.trans {Λ₁ Λ₂ Λ₃ : ClockResetSet Clock}
    (h₁₂ : Λ₁.Subset Λ₂) (h₂₃ : Λ₂.Subset Λ₃) : Λ₁.Subset Λ₃ := by
  intro c a h
  exact h₂₃ c a (h₁₂ c a h)

theorem Subset.antisymm {Λ₁ Λ₂ : ClockResetSet Clock}
    (h₁₂ : Λ₁.Subset Λ₂) (h₂₁ : Λ₂.Subset Λ₁) : Λ₁ = Λ₂ := by
  cases Λ₁ with
  | mk value₁ finite₁ =>
      cases Λ₂ with
      | mk value₂ finite₂ =>
          change (∀ c a, value₁ c = some a → value₂ c = some a) at h₁₂
          change (∀ c a, value₂ c = some a → value₁ c = some a) at h₂₁
          have hv : value₁ = value₂ := by
            funext c
            cases h₁ : value₁ c with
            | none =>
                cases h₂ : value₂ c with
                | none => rfl
                | some a =>
                    have ha := h₂₁ c a h₂
                    rw [h₁] at ha
                    cases ha
            | some a => exact (h₁₂ c a h₁).symm
          subst value₂
          rfl

theorem subset_union_left (Λ₁ Λ₂ : ClockResetSet Clock) :
    Λ₁.Subset (Λ₁.union Λ₂) := by
  intro c a h
  simp [union, h]

theorem subset_union_right (Λ₁ Λ₂ : ClockResetSet Clock)
    (hcon : Λ₁.Consistent Λ₂) : Λ₂.Subset (Λ₁.union Λ₂) := by
  intro c b h₂
  cases h₁ : Λ₁.value c with
  | none =>
      change (match Λ₁.value c with
        | some a => some a
        | none => Λ₂.value c) = some b
      rw [h₁]
      exact h₂
  | some a =>
      have hab := hcon c a b h₁ h₂
      change (match Λ₁.value c with
        | some a => some a
        | none => Λ₂.value c) = some b
      rw [h₁, hab]

theorem clocks_union (Λ₁ Λ₂ : ClockResetSet Clock) :
    (Λ₁.union Λ₂).clocks = Λ₁.clocks ∪ Λ₂.clocks := by
  ext c
  constructor
  · rintro ⟨a, ha⟩
    cases h₁ : Λ₁.value c with
    | some b => exact Or.inl ⟨b, h₁⟩
    | none =>
        right
        refine ⟨a, ?_⟩
        change (match Λ₁.value c with
          | some a => some a
          | none => Λ₂.value c) = some a at ha
        rw [h₁] at ha
        exact ha
  · rintro (hc | hc)
    · obtain ⟨a, ha⟩ := hc
      refine ⟨a, ?_⟩
      change (match Λ₁.value c with
        | some a => some a
        | none => Λ₂.value c) = some a
      rw [ha]
    · obtain ⟨a, ha⟩ := hc
      cases h₁ : Λ₁.value c with
      | some b =>
          refine ⟨b, ?_⟩
          change (match Λ₁.value c with
            | some a => some a
            | none => Λ₂.value c) = some b
          rw [h₁]
      | none =>
          refine ⟨a, ?_⟩
          change (match Λ₁.value c with
            | some a => some a
            | none => Λ₂.value c) = some a
          rw [h₁]
          exact ha

theorem clocks_mono {Λ₁ Λ₂ : ClockResetSet Clock} (h : Λ₁.Subset Λ₂) :
    Λ₁.clocks ⊆ Λ₂.clocks := by
  rintro c ⟨a, ha⟩
  exact ⟨a, h c a ha⟩

/-- Extending a reset set changes only clocks in the graph difference. -/
theorem apply_eq_of_subset_of_not_extra {Λ₁ Λ₂ : ClockResetSet Clock}
    (hsub : Λ₁.Subset Λ₂) (α : ClockValuation Clock) {c : Clock}
    (hc : c ∉ Λ₂.clocks \ Λ₁.clocks) :
    Λ₂.apply α c = Λ₁.apply α c := by
  cases h₁ : Λ₁.value c with
  | some a =>
      have h₂ := hsub c a h₁
      simp [apply, h₁, h₂]
  | none =>
      cases h₂ : Λ₂.value c with
      | none => simp [apply, h₁, h₂]
      | some a =>
          exfalso
          apply hc
          constructor
          · exact ⟨a, h₂⟩
          · rintro ⟨b, hb⟩
            rw [h₁] at hb
            cases hb

/-- Applying one reset set preserves equality at a clock whenever either the
reset supplies its value or the incoming valuations agree there. -/
theorem apply_eq_apply_of_agree_outside (Λ : ClockResetSet Clock)
    (α β : ClockValuation Clock) (c : Clock)
    (hagree : c ∉ Λ.clocks → α c = β c) :
    Λ.apply α c = Λ.apply β c := by
  cases h : Λ.value c with
  | some a => simp [apply, h]
  | none =>
      simp only [apply, h]
      apply hagree
      rintro ⟨a, ha⟩
      rw [h] at ha
      cases ha

end ClockResetSet

variable {Clock Var : Type*}

namespace TransitionForm

/-- Free clocks in the body under the outer reset of a transition form:
`fvar(Λ.(L, X(C′, Λ′.L′)))` from Definition 4.3. -/
def bodyFreeClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  ((⋃ Ψ ∈ Φ.current.locals, Ψ.freeClocks) ∪
    match Φ.nextPart with
    | none => ∅
    | some N => N.freeClocks) \ Φ.current.resets.clocks

end TransitionForm

/-- Residual form of Definition 4.3 (syntactic subsumption). If the source
has a next component, the target must also have one. -/
structure SyntacticallySubsumed (Y : Set Clock)
    (Φ₁ Φ₂ : TransitionForm Clock Var) : Prop where
  requiredResets : Y ⊆ Φ₁.current.resets.clocks
  currentConstraints : Φ₁.current.constraints ⊆ Φ₂.current.constraints
  currentResets : Φ₁.current.resets.Subset Φ₂.current.resets
  currentLocals : Φ₁.current.locals ⊆ Φ₂.current.locals
  nextShape : Φ₁.nextPart.isSome = true → Φ₂.nextPart.isSome = true
  nextConstraints : ∀ N₁ N₂, Φ₁.nextPart = some N₁ → Φ₂.nextPart = some N₂ →
    N₁.constraints ⊆ N₂.constraints
  nextResets : ∀ N₁ N₂, Φ₁.nextPart = some N₁ → Φ₂.nextPart = some N₂ →
    N₁.resets.Subset N₂.resets
  nextLocals : ∀ N₁ N₂, Φ₁.nextPart = some N₁ → Φ₂.nextPart = some N₂ →
    N₁.locals ⊆ N₂.locals
  outerFresh : Disjoint
    (Φ₂.current.resets.clocks \ Φ₁.current.resets.clocks)
    Φ₁.bodyFreeClocks
  nextFresh : ∀ N₁ N₂, Φ₁.nextPart = some N₁ → Φ₂.nextPart = some N₂ →
    Disjoint (N₂.resets.clocks \ N₁.resets.clocks)
      (⋃ Ψ ∈ N₁.locals, Ψ.freeClocks \ N₁.resets.clocks)

/-- Syntactic subsumption with required reset clocks `Y`. -/
scoped[STL] notation:50 Φ₁ " ⊑[" Y "] " Φ₂ =>
  STLTableau.SyntacticallySubsumed Y Φ₁ Φ₂

/-- Syntactic subsumption with an empty set of required reset clocks. -/
scoped[STL] notation:50 Φ₁ " ⊑ " Φ₂ =>
  STLTableau.SyntacticallySubsumed (∅ : Set _) Φ₁ Φ₂

open scoped STL

theorem StateForm.componentCount_le
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints ⊆ S₂.constraints)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals) :
    S₁.componentCount ≤ S₂.componentCount := by
  have hCf := Set.ncard_le_ncard hC S₂.constraints_finite
  have hΛf : S₂.resets.clocks.Finite := by
    simpa [ClockResetSet.clocks] using S₂.resets.finite_domain
  have hΛc := Set.ncard_le_ncard (ClockResetSet.clocks_mono hΛ) hΛf
  have hLf := Set.ncard_le_ncard hL S₂.locals_finite
  simp only [StateForm.componentCount]
  omega

theorem SyntacticallySubsumed.componentCount_le
    {Y : Set Clock} {Φ₁ Φ₂ : TransitionForm Clock Var}
    (h : Φ₁ ⊑[Y] Φ₂) : Φ₁.componentCount ≤ Φ₂.componentCount := by
  have hcurrent := StateForm.componentCount_le
    h.currentConstraints h.currentResets h.currentLocals
  cases h₁ : Φ₁.nextPart with
  | none =>
      cases h₂ : Φ₂.nextPart <;>
        simp [TransitionForm.componentCount, h₁, h₂] <;> omega
  | some N₁ =>
      have hsome₂ : Φ₂.nextPart.isSome = true :=
        h.nextShape (by simp [h₁])
      obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
      have hnext := StateForm.componentCount_le
        (h.nextConstraints N₁ N₂ h₁ h₂)
        (h.nextResets N₁ N₂ h₁ h₂)
        (h.nextLocals N₁ N₂ h₁ h₂)
      simp [TransitionForm.componentCount, h₁, h₂]
      omega

theorem ClockResetSet.eq_of_subset_of_clocks_eq
    {Λ₁ Λ₂ : ClockResetSet Clock} (hsub : Λ₁.Subset Λ₂)
    (hclocks : Λ₁.clocks = Λ₂.clocks) : Λ₁ = Λ₂ := by
  cases Λ₁ with
  | mk value₁ finite₁ =>
      cases Λ₂ with
      | mk value₂ finite₂ =>
          congr 1
          funext c
          cases h₁ : value₁ c with
          | some a =>
              exact (hsub c a h₁).symm
          | none =>
              cases h₂ : value₂ c with
              | none => rfl
              | some a =>
                  exfalso
                  have hc₂ : c ∈ (ClockResetSet.mk value₂ finite₂).clocks := ⟨a, h₂⟩
                  have hc₁ : c ∈ (ClockResetSet.mk value₁ finite₁).clocks := by
                    rw [hclocks]
                    exact hc₂
                  obtain ⟨b, hb⟩ := hc₁
                  change value₁ c = some b at hb
                  rw [h₁] at hb
                  cases hb

theorem StateForm.eq_of_componentCount_eq
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints ⊆ S₂.constraints)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals)
    (hcount : S₁.componentCount = S₂.componentCount) : S₁ = S₂ := by
  have hCf := Set.ncard_le_ncard hC S₂.constraints_finite
  have hΛ₂f : S₂.resets.clocks.Finite := by
    simpa [ClockResetSet.clocks] using S₂.resets.finite_domain
  have hΛc := Set.ncard_le_ncard (ClockResetSet.clocks_mono hΛ) hΛ₂f
  have hLf := Set.ncard_le_ncard hL S₂.locals_finite
  have hCcard : S₁.constraints.ncard = S₂.constraints.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hΛcard : S₁.resets.clocks.ncard = S₂.resets.clocks.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hLcard : S₁.locals.ncard = S₂.locals.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hCeq := Set.eq_of_subset_of_ncard_le hC hCcard.ge S₂.constraints_finite
  have hΛeqClocks := Set.eq_of_subset_of_ncard_le
    (ClockResetSet.clocks_mono hΛ) hΛcard.ge hΛ₂f
  have hΛeq := ClockResetSet.eq_of_subset_of_clocks_eq hΛ hΛeqClocks
  have hLeq := Set.eq_of_subset_of_ncard_le hL hLcard.ge S₂.locals_finite
  exact StateForm.ext hCeq hΛeq hLeq

theorem SyntacticallySubsumed.eq_of_componentCount_eq
    {Y : Set Clock} {Φ₁ Φ₂ : TransitionForm Clock Var}
    (h : Φ₁ ⊑[Y] Φ₂) (hcount : Φ₁.componentCount = Φ₂.componentCount) :
    Φ₁ = Φ₂ := by
  have hcurrentLe := StateForm.componentCount_le
    h.currentConstraints h.currentResets h.currentLocals
  cases h₁ : Φ₁.nextPart with
  | none =>
      cases h₂ : Φ₂.nextPart with
      | none =>
          have hc : Φ₁.current.componentCount = Φ₂.current.componentCount := by
            simpa [TransitionForm.componentCount, h₁, h₂] using hcount
          have := StateForm.eq_of_componentCount_eq
            h.currentConstraints h.currentResets h.currentLocals hc
          cases Φ₁
          cases Φ₂
          simp_all
      | some N₂ =>
          have hpos : 0 < N₂.componentCount + 1 := by omega
          simp [TransitionForm.componentCount, h₁, h₂] at hcount
          omega
  | some N₁ =>
      have hsome₂ := h.nextShape (by simp [h₁])
      obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
      have hnextLe := StateForm.componentCount_le
        (h.nextConstraints N₁ N₂ h₁ h₂)
        (h.nextResets N₁ N₂ h₁ h₂)
        (h.nextLocals N₁ N₂ h₁ h₂)
      have hc : Φ₁.current.componentCount = Φ₂.current.componentCount := by
        simp [TransitionForm.componentCount, h₁, h₂] at hcount
        omega
      have hn : N₁.componentCount = N₂.componentCount := by
        simp [TransitionForm.componentCount, h₁, h₂] at hcount
        omega
      have hcurrentEq := StateForm.eq_of_componentCount_eq
        h.currentConstraints h.currentResets h.currentLocals hc
      have hnextEq := StateForm.eq_of_componentCount_eq
        (h.nextConstraints N₁ N₂ h₁ h₂)
        (h.nextResets N₁ N₂ h₁ h₂)
        (h.nextLocals N₁ N₂ h₁ h₂) hn
      cases Φ₁
      cases Φ₂
      simp_all

/-- Existing current predicate invariants survive a syntactically fresh reset
extension. -/
theorem SyntacticallySubsumed.currentInvariant_of_source
    {Y : Set Clock} {Φ₁ Φ₂ : TransitionForm Clock Var}
    (hsub : Φ₁ ⊑[Y] Φ₂) (J : MarkedInterval) (α : ClockValuation Clock)
    (hinv : Judgement.SetInvariant J (Φ₁.current.resets.apply α)
      Φ₁.current.locals)
    {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ Φ₁.current.locals) :
    IntervalPredicate.Invariant J (Φ₂.current.resets.apply α) p := by
  apply (IntervalPredicate.invariant_congr J
    (Φ₁.current.resets.apply α) (Φ₂.current.resets.apply α) p ?_).mp
    (hinv p hp)
  intro c hc
  symm
  apply ClockResetSet.apply_eq_of_subset_of_not_extra hsub.currentResets α
  intro hextra
  apply Set.disjoint_left.1 hsub.outerFresh hextra
  refine ⟨?_, hextra.2⟩
  apply Or.inl
  apply Set.mem_iUnion.2
  refine ⟨Judgement.predicate p, Set.mem_iUnion.2 ⟨hp, ?_⟩⟩
  change c ∈ Judgement.predicateClocks p
  simpa [Judgement.predicateClocks] using hc

/-- Extending the outer reset preserves the next state's incoming valuation
on its free clocks after the same amount of time elapses. -/
private theorem SyntacticallySubsumed.next_incoming_agree
    {Y : Set Clock} {Φ Ψ : TransitionForm Clock Var}
    (h : Φ ⊑[Y] Ψ) {N : StateForm Clock Var} (hn : Φ.nextPart = some N)
    (α : ClockValuation Clock) (δ : NNReal) :
    Set.EqOn (ClockResetSet.elapse (Ψ.current.resets.apply α) δ)
      (ClockResetSet.elapse (Φ.current.resets.apply α) δ) N.freeClocks := by
  intro c hc
  apply congrArg (fun x => x + δ)
  apply ClockResetSet.apply_eq_of_subset_of_not_extra h.currentResets α
  intro hextra
  exact Set.disjoint_left.1 h.outerFresh hextra
    ⟨Or.inr (by simpa only [hn] using hc), hextra.2⟩

/-- Existing next predicate invariants survive both the fresh outer-reset
extension and the fresh extension of the next component's reset set. -/
theorem SyntacticallySubsumed.nextInvariant_of_source
    {Y : Set Clock} {σ : FiniteSignal Var} {Φ₁ Φ₂ : TransitionForm Clock Var}
    (hsub : Φ₁ ⊑[Y] Φ₂) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hnext : k.1 + 1 < P.size)
    {N₁ N₂ : StateForm Clock Var} (hN₁ : Φ₁.nextPart = some N₁)
    (hN₂ : Φ₂.nextPart = some N₂)
    (hinv : Judgement.SetInvariant (P.interval ⟨k.1 + 1, by omega⟩)
      (N₁.resets.apply (ClockResetSet.elapse (Φ₁.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) N₁.locals)
    {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ N₁.locals) :
    IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, by omega⟩)
      (N₂.resets.apply (ClockResetSet.elapse (Φ₂.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) p := by
  have hk : k.1 < P.size := by omega
  let β₁ := ClockResetSet.elapse (Φ₁.current.resets.apply α)
    (Judgement.duration P ⟨k.1, hk⟩)
  let β₂ := ClockResetSet.elapse (Φ₂.current.resets.apply α)
    (Judgement.duration P ⟨k.1, hk⟩)
  apply (IntervalPredicate.invariant_congr (P.interval ⟨k.1 + 1, by omega⟩)
    (N₁.resets.apply β₁) (N₂.resets.apply β₂) p ?_).mp
  · simpa [β₁] using hinv p hp
  · intro c hc
    calc
      N₁.resets.apply β₁ c = N₁.resets.apply β₂ c := by
        apply ClockResetSet.apply_eq_apply_of_agree_outside
        intro hcN₁
        symm
        apply hsub.next_incoming_agree hN₁ α (Judgement.duration P ⟨k.1, hk⟩)
        apply Or.inr
        apply Set.mem_iUnion.2
        refine ⟨Judgement.predicate p, Set.mem_iUnion.2 ⟨hp, ?_⟩⟩
        refine ⟨?_, hcN₁⟩
        change c ∈ Judgement.predicateClocks p
        simpa [Judgement.predicateClocks] using hc
      _ = N₂.resets.apply β₂ c := by
        symm
        apply ClockResetSet.apply_eq_of_subset_of_not_extra
          (hsub.nextResets N₁ N₂ hN₁ hN₂) β₂
        intro hextra
        apply Set.disjoint_left.1 (hsub.nextFresh N₁ N₂ hN₁ hN₂) hextra
        apply Set.mem_iUnion.2
        refine ⟨Judgement.predicate p, Set.mem_iUnion.2 ⟨hp, ?_⟩⟩
        refine ⟨?_, hextra.2⟩
        change c ∈ Judgement.predicateClocks p
        simpa [Judgement.predicateClocks] using hc

/-- Free clocks are monotone under a fresh state-form extension. -/
theorem StateForm.freeClocks_mono
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints ⊆ S₂.constraints)
    (_hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals)
    (hfresh : Disjoint (S₂.resets.clocks \ S₁.resets.clocks)
      (⋃ Ψ ∈ S₁.locals, Ψ.freeClocks \ S₁.resets.clocks)) :
    S₁.freeClocks ⊆ S₂.freeClocks := by
  intro c hc
  rcases hc with hc | hc
  · obtain ⟨g, hg, rfl⟩ := hc
    exact Or.inl ⟨g, hC hg, rfl⟩
  · obtain ⟨Ψ, hΨ, hc, hc₁⟩ := Set.mem_iUnion₂.1 hc
    have hc₂ : c ∉ S₂.resets.clocks := by
      intro hc₂
      exact Set.disjoint_left.1 hfresh ⟨hc₂, hc₁⟩
        (Set.mem_iUnion₂.2 ⟨Ψ, hΨ, ⟨hc, hc₁⟩⟩)
    exact Or.inr (Set.mem_iUnion₂.2 ⟨Ψ, hL hΨ, ⟨hc, hc₂⟩⟩)

/-- The state-form fragment of semantic subsumption.  This is also useful
independently for the current and next components of a transition form. -/
theorem StateForm.satisfies_of_extension
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints ⊆ S₂.constraints)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals)
    (hfresh : Disjoint (S₂.resets.clocks \ S₁.resets.clocks)
      (⋃ Ψ ∈ S₁.locals, Ψ.freeClocks \ S₁.resets.clocks))
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (h₂ : S₂.Satisfies σ P α k) : S₁.Satisfies σ P α k := by
  refine ⟨fun g hg => h₂.1 g (hC hg), ?_⟩
  intro Ψ hΨ
  have hsat₂ := h₂.2 Ψ (hL hΨ)
  apply (Judgement.satisfies_congr_of_agree (σ := σ) (P := P) (k := k) ?_).1 hsat₂
  intro c hc
  apply ClockResetSet.apply_eq_of_subset_of_not_extra hΛ α
  intro hextra
  exact Set.disjoint_left.1 hfresh hextra
    (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, ⟨hc, hextra.2⟩⟩⟩)

theorem StateForm.nonPredicateSatisfies_of_extension
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.constraints ⊆ S₂.constraints)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals)
    (hfresh : Disjoint (S₂.resets.clocks \ S₁.resets.clocks)
      (⋃ Ψ ∈ S₁.locals, Ψ.freeClocks \ S₁.resets.clocks))
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (h₂ : S₂.NonPredicateSatisfies σ P α k) : S₁.NonPredicateSatisfies σ P α k := by
  refine ⟨fun g hg => h₂.1 g (hC hg), ?_⟩
  intro Ψ hΨ
  have hsat₂ := h₂.2 Ψ (hL hΨ)
  apply (Judgement.nonPredicateSatisfies_congr_of_agree (σ := σ) (P := P) (k := k) ?_).1 hsat₂
  intro c hc
  apply ClockResetSet.apply_eq_of_subset_of_not_extra hΛ α
  intro hextra
  exact Set.disjoint_left.1 hfresh hextra
    (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, ⟨hc, hextra.2⟩⟩⟩)

/-- Satisfaction of two compatible state forms combines into satisfaction
of their componentwise union. -/
theorem StateForm.satisfies_union_of (S T : StateForm Clock Var)
    (hcon : S.resets.Consistent T.resets)
    (hfreshS : Disjoint (T.resets.clocks \ S.resets.clocks)
      (⋃ l ∈ S.locals, l.freeClocks \ S.resets.clocks))
    (hfreshT : Disjoint (S.resets.clocks \ T.resets.clocks)
      (⋃ l ∈ T.locals, l.freeClocks \ T.resets.clocks))
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hS : S.Satisfies σ P α k) (hT : T.Satisfies σ P α k) :
    (S.union T).Satisfies σ P α k := by
  refine ⟨?_, ?_⟩
  · intro g hg
    exact hg.elim (hS.1 g) (hT.1 g)
  · intro l hl
    rcases hl with hl | hl
    · have hs := hS.2 l hl
      apply (Judgement.satisfies_congr_of_agree
        (σ := σ) (P := P) (k := k) ?_).2 hs
      intro c hc
      apply ClockResetSet.apply_eq_of_subset_of_not_extra
        (ClockResetSet.subset_union_left S.resets T.resets) α
      intro hextra
      have hcT : c ∈ T.resets.clocks := by
        rw [ClockResetSet.clocks_union] at hextra
        exact hextra.1.resolve_left hextra.2
      exact Set.disjoint_left.1 hfreshS ⟨hcT, hextra.2⟩
        (Set.mem_iUnion₂.2 ⟨l, hl, ⟨hc, hextra.2⟩⟩)
    · have ht := hT.2 l hl
      apply (Judgement.satisfies_congr_of_agree
        (σ := σ) (P := P) (k := k) ?_).2 ht
      intro c hc
      by_cases hcT : c ∈ T.resets.clocks
      · exact ClockResetSet.apply_union_eq_right_of_consistent
          S.resets T.resets hcon α hcT
      · have hcS : c ∉ S.resets.clocks := by
          intro hcS
          exact Set.disjoint_left.1 hfreshT ⟨hcS, hcT⟩
            (Set.mem_iUnion₂.2 ⟨l, hl, ⟨hc, hcT⟩⟩)
        exact ClockResetSet.apply_union_eq_right_of_not_mem
          S.resets T.resets α hcS

theorem syntacticallySubsumed_refl (Y : Set Clock) (Φ : TransitionForm Clock Var)
    (hY : Y ⊆ Φ.current.resets.clocks) : Φ ⊑[Y] Φ := by
  refine ⟨hY, fun _ h => h, ClockResetSet.subset_refl _, fun _ h => h, fun h => h,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro N₁ N₂ h₁ h₂
    rw [h₁] at h₂
    cases h₂
    exact fun _ h => h
  · intro N₁ N₂ h₁ h₂
    rw [h₁] at h₂
    cases h₂
    exact ClockResetSet.subset_refl _
  · intro N₁ N₂ h₁ h₂
    rw [h₁] at h₂
    cases h₂
    exact fun _ h => h
  · simp
  · intro N₁ N₂ h₁ h₂
    rw [h₁] at h₂
    cases h₂
    simp

/-- Lemma C.13: subsumption preserves free clocks in the
body beneath the outer reset. -/
theorem SyntacticallySubsumed.bodyFreeClocks_mono
    {Y : Set Clock} {Φ₁ Φ₂ : TransitionForm Clock Var}
    (h : Φ₁ ⊑[Y] Φ₂) : Φ₁.bodyFreeClocks ⊆ Φ₂.bodyFreeClocks := by
  intro c hc
  obtain ⟨hc, hc₁⟩ := hc
  have hc₂ : c ∉ Φ₂.current.resets.clocks := by
    intro hc₂
    exact Set.disjoint_left.1 h.outerFresh ⟨hc₂, hc₁⟩ ⟨hc, hc₁⟩
  refine ⟨?_, hc₂⟩
  rcases hc with hc | hc
  · left
    obtain ⟨Ψ, hΨ, hc⟩ := Set.mem_iUnion₂.1 hc
    exact Set.mem_iUnion₂.2 ⟨Ψ, h.currentLocals hΨ, hc⟩
  · right
    cases h₁ : Φ₁.nextPart with
    | none => simp [h₁] at hc
    | some N₁ =>
      have hsome₂ : Φ₂.nextPart.isSome = true := by
        exact h.nextShape (by simp [h₁])
      obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
      have hmono : N₁.freeClocks ⊆ N₂.freeClocks :=
        StateForm.freeClocks_mono
          (h.nextConstraints N₁ N₂ h₁ h₂)
          (h.nextResets N₁ N₂ h₁ h₂)
          (h.nextLocals N₁ N₂ h₁ h₂)
          (h.nextFresh N₁ N₂ h₁ h₂)
      simpa [h₂] using hmono (by simpa [h₁] using hc)

/-- Transitivity part of Proposition C.14. -/
theorem SyntacticallySubsumed.trans
    {Y Z : Set Clock} {Φ₁ Φ₂ Φ₃ : TransitionForm Clock Var}
    (h₁₂ : Φ₁ ⊑[Y] Φ₂) (h₂₃ : Φ₂ ⊑[Z] Φ₃) : Φ₁ ⊑[Y] Φ₃ := by
  refine
    { requiredResets := h₁₂.requiredResets
      currentConstraints := h₁₂.currentConstraints.trans h₂₃.currentConstraints
      currentResets := h₁₂.currentResets.trans h₂₃.currentResets
      currentLocals := h₁₂.currentLocals.trans h₂₃.currentLocals
      nextShape := fun h => h₂₃.nextShape (h₁₂.nextShape h)
      nextConstraints := ?_
      nextResets := ?_
      nextLocals := ?_
      outerFresh := ?_
      nextFresh := ?_ }
  · intro N₁ N₃ h₁ h₃
    have hsome₂ : Φ₂.nextPart.isSome = true := by
      exact h₁₂.nextShape (by simp [h₁])
    obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
    exact (h₁₂.nextConstraints N₁ N₂ h₁ h₂).trans
      (h₂₃.nextConstraints N₂ N₃ h₂ h₃)
  · intro N₁ N₃ h₁ h₃
    have hsome₂ : Φ₂.nextPart.isSome = true := by
      exact h₁₂.nextShape (by simp [h₁])
    obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
    exact (h₁₂.nextResets N₁ N₂ h₁ h₂).trans
      (h₂₃.nextResets N₂ N₃ h₂ h₃)
  · intro N₁ N₃ h₁ h₃
    have hsome₂ : Φ₂.nextPart.isSome = true := by
      exact h₁₂.nextShape (by simp [h₁])
    obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
    exact (h₁₂.nextLocals N₁ N₂ h₁ h₂).trans
      (h₂₃.nextLocals N₂ N₃ h₂ h₃)
  · rw [Set.disjoint_left]
    intro c hc₃₁ hfree₁
    by_cases hc₂ : c ∈ Φ₂.current.resets.clocks
    · exact Set.disjoint_left.1 h₁₂.outerFresh ⟨hc₂, hc₃₁.2⟩ hfree₁
    · exact Set.disjoint_left.1 h₂₃.outerFresh ⟨hc₃₁.1, hc₂⟩
        (h₁₂.bodyFreeClocks_mono hfree₁)
  · intro N₁ N₃ h₁ h₃
    have hsome₂ : Φ₂.nextPart.isSome = true := by
      exact h₁₂.nextShape (by simp [h₁])
    obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
    rw [Set.disjoint_left]
    intro c hc₃₁ hfree₁
    by_cases hc₂ : c ∈ N₂.resets.clocks
    · exact Set.disjoint_left.1 (h₁₂.nextFresh N₁ N₂ h₁ h₂)
        ⟨hc₂, hc₃₁.2⟩ hfree₁
    · apply Set.disjoint_left.1 (h₂₃.nextFresh N₂ N₃ h₂ h₃)
        ⟨hc₃₁.1, hc₂⟩
      obtain ⟨Ψ, hΨ, hc, _⟩ := Set.mem_iUnion₂.1 hfree₁
      exact Set.mem_iUnion₂.2 ⟨Ψ, h₁₂.nextLocals N₁ N₂ h₁ h₂ hΨ, ⟨hc, hc₂⟩⟩

/-- Antisymmetry part of Proposition C.14. -/
theorem SyntacticallySubsumed.antisymm
    {Φ₁ Φ₂ : TransitionForm Clock Var}
    (h₁₂ : Φ₁ ⊑ Φ₂) (h₂₁ : Φ₂ ⊑ Φ₁) : Φ₁ = Φ₂ := by
  have hcurrent : Φ₁.current = Φ₂.current := StateForm.ext
    (Set.Subset.antisymm h₁₂.currentConstraints h₂₁.currentConstraints)
    (h₁₂.currentResets.antisymm h₂₁.currentResets)
    (Set.Subset.antisymm h₁₂.currentLocals h₂₁.currentLocals)
  have hnext : Φ₁.nextPart = Φ₂.nextPart := by
    cases h₁ : Φ₁.nextPart with
    | none =>
        cases h₂ : Φ₂.nextPart with
        | none => rfl
        | some N₂ =>
            have hs : False := by
              have := h₂₁.nextShape (by simp [h₂])
              simp [h₁] at this
            exact hs.elim
    | some N₁ =>
        have hsome₂ : Φ₂.nextPart.isSome = true := by
          exact h₁₂.nextShape (by simp [h₁])
        obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hsome₂
        rw [h₂]
        congr 1
        apply StateForm.ext
        · exact Set.Subset.antisymm
            (h₁₂.nextConstraints N₁ N₂ h₁ h₂)
            (h₂₁.nextConstraints N₂ N₁ h₂ h₁)
        · exact (h₁₂.nextResets N₁ N₂ h₁ h₂).antisymm
            (h₂₁.nextResets N₂ N₁ h₂ h₁)
        · exact Set.Subset.antisymm
            (h₁₂.nextLocals N₁ N₂ h₁ h₂)
            (h₂₁.nextLocals N₂ N₁ h₂ h₁)
  cases Φ₁
  cases Φ₂
  simp_all

/-- The original transition form is subsumed by its componentwise union with
a branch, provided the branch's newly bound clocks satisfy the two
freshness conditions. This is the extension half of the transition-form extension argument. -/
theorem TransitionForm.subsumed_union_left (Φ Ψ : TransitionForm Clock Var)
    (houter : Disjoint
      ((Φ.union Ψ).current.resets.clocks \ Φ.current.resets.clocks)
      Φ.bodyFreeClocks)
    (hnext : ∀ N₁ N₃, Φ.nextPart = some N₁ →
      (Φ.union Ψ).nextPart = some N₃ →
      Disjoint (N₃.resets.clocks \ N₁.resets.clocks)
        (⋃ l ∈ N₁.locals, l.freeClocks \ N₁.resets.clocks)) :
    Φ ⊑ Φ.union Ψ := by
  refine
    { requiredResets := Set.empty_subset _
      currentConstraints := Set.subset_union_left
      currentResets := ClockResetSet.subset_union_left _ _
      currentLocals := Set.subset_union_left
      nextShape := ?_
      nextConstraints := ?_
      nextResets := ?_
      nextLocals := ?_
      outerFresh := houter
      nextFresh := hnext }
  · intro hs
    obtain ⟨N₁, h₁⟩ := Option.isSome_iff_exists.mp hs
    cases h₂ : Ψ.nextPart <;> simp [TransitionForm.union, unionNext, h₁, h₂]
  · intro N₁ N₃ h₁ h₃
    cases h₂ : Ψ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₁ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact fun _ h => h
    | some N₂ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact Set.subset_union_left
  · intro N₁ N₃ h₁ h₃
    cases h₂ : Ψ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₁ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact ClockResetSet.subset_refl _
    | some N₂ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact ClockResetSet.subset_union_left _ _
  · intro N₁ N₃ h₁ h₃
    cases h₂ : Ψ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₁ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact fun _ h => h
    | some N₂ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact Set.subset_union_left

/-- The branch transition form is also subsumed by the normalized union.
Unlike the left-extension direction, this uses consistency because reset
union is left-biased. This is the branch-coverage half of
the transition-form extension argument. -/
theorem TransitionForm.subsumed_union_right (Φ Ψ : TransitionForm Clock Var)
    (hcurrentCon : Φ.current.resets.Consistent Ψ.current.resets)
    (hnextCon : ∀ N₁ N₂, Φ.nextPart = some N₁ → Ψ.nextPart = some N₂ →
      N₁.resets.Consistent N₂.resets)
    (houter : Disjoint
      ((Φ.union Ψ).current.resets.clocks \ Ψ.current.resets.clocks)
      Ψ.bodyFreeClocks)
    (hnext : ∀ N₂ N₃, Ψ.nextPart = some N₂ →
      (Φ.union Ψ).nextPart = some N₃ →
      Disjoint (N₃.resets.clocks \ N₂.resets.clocks)
        (⋃ l ∈ N₂.locals, l.freeClocks \ N₂.resets.clocks)) :
    Ψ ⊑ Φ.union Ψ := by
  refine
    { requiredResets := Set.empty_subset _
      currentConstraints := Set.subset_union_right
      currentResets := ClockResetSet.subset_union_right _ _ hcurrentCon
      currentLocals := Set.subset_union_right
      nextShape := ?_
      nextConstraints := ?_
      nextResets := ?_
      nextLocals := ?_
      outerFresh := houter
      nextFresh := hnext }
  · intro hs
    obtain ⟨N₂, h₂⟩ := Option.isSome_iff_exists.mp hs
    cases h₁ : Φ.nextPart <;> simp [TransitionForm.union, unionNext, h₁, h₂]
  · intro N₂ N₃ h₂ h₃
    cases h₁ : Φ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₂ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact fun _ h => h
    | some N₁ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact Set.subset_union_right
  · intro N₂ N₃ h₂ h₃
    cases h₁ : Φ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₂ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact ClockResetSet.subset_refl _
    | some N₁ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact ClockResetSet.subset_union_right _ _ (hnextCon N₁ N₂ h₁ h₂)
  · intro N₂ N₃ h₂ h₃
    cases h₁ : Φ.nextPart with
    | none =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some N₂ = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact fun _ h => h
    | some N₁ =>
        rw [TransitionForm.nextPart_union, h₁, h₂] at h₃
        change some (N₁.union N₂) = some N₃ at h₃
        injection h₃ with hN
        subst N₃
        exact Set.subset_union_right

/-- Residual form of Lemma 4.5: syntactic subsumption is semantically
sound.  The required-reset parameter does not affect this direction. -/
theorem transitionForm_subsumption_sound {Y : Set Clock}
    {Φ₁ Φ₂ : TransitionForm Clock Var} (hsub : Φ₁ ⊑[Y] Φ₂)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (h₂ : Φ₂.Satisfies σ P α k) : Φ₁.Satisfies σ P α k := by
  have hcurrentFresh : Disjoint
      (Φ₂.current.resets.clocks \ Φ₁.current.resets.clocks)
      (⋃ Ψ ∈ Φ₁.current.locals,
        Ψ.freeClocks \ Φ₁.current.resets.clocks) := by
    apply hsub.outerFresh.mono_right
    rintro c hc
    obtain ⟨Ψ, hΨ, hc, hcr⟩ := Set.mem_iUnion₂.1 hc
    exact ⟨Or.inl (Set.mem_iUnion₂.2 ⟨Ψ, hΨ, hc⟩), hcr⟩
  have hstate₁ : Φ₁.current.Satisfies σ P α k :=
    StateForm.satisfies_of_extension hsub.currentConstraints hsub.currentResets
      hsub.currentLocals hcurrentFresh ⟨h₂.1, h₂.2.1⟩
  refine ⟨hstate₁.1, hstate₁.2, ?_⟩
  cases h₁ : Φ₁.nextPart with
  | none => simp
  | some N₁ =>
      have hsome₂ : Φ₂.nextPart.isSome = true := by
        exact hsub.nextShape (by simp [h₁])
      obtain ⟨N₂, h₂next⟩ := Option.isSome_iff_exists.mp hsome₂
      simp only [TransitionForm.Satisfies, h₂next] at h₂
      simp only
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at h₂ ⊢
        let δ := Judgement.duration P ⟨k.1, hk⟩
        let β₁ := ClockResetSet.elapse (Φ₁.current.resets.apply α) δ
        let β₂ := ClockResetSet.elapse (Φ₂.current.resets.apply α) δ
        have hN₂ : N₂.Satisfies σ P β₂ ⟨k.1 + 1, by omega⟩ := by
          simpa [β₂, δ] using h₂.2.2
        have hN₁₂ : N₁.Satisfies σ P β₂ ⟨k.1 + 1, by omega⟩ :=
          StateForm.satisfies_of_extension
            (hsub.nextConstraints N₁ N₂ h₁ h₂next)
            (hsub.nextResets N₁ N₂ h₁ h₂next)
            (hsub.nextLocals N₁ N₂ h₁ h₂next)
            (hsub.nextFresh N₁ N₂ h₁ h₂next) hN₂
        have hagree : ∀ c ∈ N₁.freeClocks, β₂ c = β₁ c :=
          fun _ hc => hsub.next_incoming_agree h₁ α δ hc
        exact (StateForm.satisfies_congr_of_agree N₁ hagree σ P
          ⟨k.1 + 1, by omega⟩).1 hN₁₂
      · simp only [dif_neg hk] at h₂
        exact False.elim h₂.2.2

theorem transitionForm_nonPredicate_subsumption_sound {Y : Set Clock}
    {Φ₁ Φ₂ : TransitionForm Clock Var} (hsub : Φ₁ ⊑[Y] Φ₂)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (h₂ : Φ₂.NonPredicateSatisfies σ P α k) : Φ₁.NonPredicateSatisfies σ P α k := by
  have hcurrentFresh : Disjoint
      (Φ₂.current.resets.clocks \ Φ₁.current.resets.clocks)
      (⋃ Ψ ∈ Φ₁.current.locals,
        Ψ.freeClocks \ Φ₁.current.resets.clocks) := by
    apply hsub.outerFresh.mono_right
    rintro c hc
    obtain ⟨Ψ, hΨ, hc, hcr⟩ := Set.mem_iUnion₂.1 hc
    exact ⟨Or.inl (Set.mem_iUnion₂.2 ⟨Ψ, hΨ, hc⟩), hcr⟩
  have hstate₁ : Φ₁.current.NonPredicateSatisfies σ P α k :=
    StateForm.nonPredicateSatisfies_of_extension hsub.currentConstraints hsub.currentResets
      hsub.currentLocals hcurrentFresh ⟨h₂.1, h₂.2.1⟩
  refine ⟨hstate₁.1, hstate₁.2, ?_⟩
  cases h₁ : Φ₁.nextPart with
  | none => simp
  | some N₁ =>
      have hsome₂ : Φ₂.nextPart.isSome = true := by
        exact hsub.nextShape (by simp [h₁])
      obtain ⟨N₂, h₂next⟩ := Option.isSome_iff_exists.mp hsome₂
      simp only [TransitionForm.NonPredicateSatisfies, h₂next] at h₂
      simp only
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at h₂ ⊢
        let δ := Judgement.duration P ⟨k.1, hk⟩
        let β₁ := ClockResetSet.elapse (Φ₁.current.resets.apply α) δ
        let β₂ := ClockResetSet.elapse (Φ₂.current.resets.apply α) δ
        have hN₂ : N₂.NonPredicateSatisfies σ P β₂ ⟨k.1 + 1, by omega⟩ := by
          simpa [β₂, δ] using h₂.2.2
        have hN₁₂ : N₁.NonPredicateSatisfies σ P β₂ ⟨k.1 + 1, by omega⟩ :=
          StateForm.nonPredicateSatisfies_of_extension
            (hsub.nextConstraints N₁ N₂ h₁ h₂next)
            (hsub.nextResets N₁ N₂ h₁ h₂next)
            (hsub.nextLocals N₁ N₂ h₁ h₂next)
            (hsub.nextFresh N₁ N₂ h₁ h₂next) hN₂
        have hagree : ∀ c ∈ N₁.freeClocks, β₂ c = β₁ c :=
          fun _ hc => hsub.next_incoming_agree h₁ α δ hc
        exact (StateForm.nonPredicateSatisfies_congr_of_agree N₁ hagree σ P
          ⟨k.1 + 1, by omega⟩).1 hN₁₂
      · simp only [dif_neg hk] at h₂
        exact False.elim h₂.2.2

/-- Judgement implication form of Lemma 4.5. -/
theorem transitionForm_subsumption_implies {Φ₁ Φ₂ : TransitionForm Clock Var}
    (hsub : Φ₁ ⊑ Φ₂) :
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      Φ₂.Satisfies σ P α k → Φ₁.Satisfies σ P α k := by
  intro σ P α k h
  exact transitionForm_subsumption_sound hsub h

/-- Semantic projection from a normalized union to both of its inputs. The
two subsumption witnesses package precisely the consistency/freshness side
conditions established during alpha-conversion. -/
theorem TransitionForm.satisfies_left_and_right_of_union
    {Φ Ψ : TransitionForm Clock Var}
    (hleft : Φ ⊑ Φ.union Ψ) (hright : Ψ ⊑ Φ.union Ψ)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (h : (Φ.union Ψ).Satisfies σ P α k) :
    Φ.Satisfies σ P α k ∧ Ψ.Satisfies σ P α k :=
  ⟨transitionForm_subsumption_sound hleft h,
    transitionForm_subsumption_sound hright h⟩

/-- Converse semantic merge for transition forms. The subsumption witnesses
carry outer/next freshness; reset consistency is used by the state-form union
at both levels. -/
theorem TransitionForm.satisfies_union_of
    (Φ Ψ : TransitionForm Clock Var)
    (hleft : Φ ⊑ Φ.union Ψ) (hright : Ψ ⊑ Φ.union Ψ)
    (hcurrentCon : Φ.current.resets.Consistent Ψ.current.resets)
    (hnextCon : ∀ N₁ N₂, Φ.nextPart = some N₁ → Ψ.nextPart = some N₂ →
      N₁.resets.Consistent N₂.resets)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hΦ : Φ.Satisfies σ P α k) (hΨ : Ψ.Satisfies σ P α k) :
    (Φ.union Ψ).Satisfies σ P α k := by
  have hfreshΦ : Disjoint
      (Ψ.current.resets.clocks \ Φ.current.resets.clocks)
      (⋃ l ∈ Φ.current.locals, l.freeClocks \ Φ.current.resets.clocks) := by
    apply hleft.outerFresh.mono
    · intro c hc
      change c ∈ (Φ.current.resets.union Ψ.current.resets).clocks \
        Φ.current.resets.clocks
      rw [ClockResetSet.clocks_union]
      exact ⟨Or.inr hc.1, hc.2⟩
    · rintro c hc
      obtain ⟨l, hl, hc, hcr⟩ := Set.mem_iUnion₂.1 hc
      exact ⟨Or.inl (Set.mem_iUnion₂.2 ⟨l, hl, hc⟩), hcr⟩
  have hfreshΨ : Disjoint
      (Φ.current.resets.clocks \ Ψ.current.resets.clocks)
      (⋃ l ∈ Ψ.current.locals, l.freeClocks \ Ψ.current.resets.clocks) := by
    apply hright.outerFresh.mono
    · intro c hc
      change c ∈ (Φ.current.resets.union Ψ.current.resets).clocks \
        Ψ.current.resets.clocks
      rw [ClockResetSet.clocks_union]
      exact ⟨Or.inl hc.1, hc.2⟩
    · rintro c hc
      obtain ⟨l, hl, hc, hcr⟩ := Set.mem_iUnion₂.1 hc
      exact ⟨Or.inl (Set.mem_iUnion₂.2 ⟨l, hl, hc⟩), hcr⟩
  have hcurrent := StateForm.satisfies_union_of Φ.current Ψ.current
    hcurrentCon hfreshΦ hfreshΨ ⟨hΦ.1, hΦ.2.1⟩ ⟨hΨ.1, hΨ.2.1⟩
  refine ⟨hcurrent.1, hcurrent.2, ?_⟩
  cases h₁ : Φ.nextPart with
  | none =>
      cases h₂ : Ψ.nextPart with
      | none => simp [TransitionForm.union, unionNext, h₁, h₂]
      | some N₂ =>
          simp only [TransitionForm.Satisfies, h₂] at hΨ
          simp only [TransitionForm.union, unionNext, h₁, h₂]
          by_cases hk : k.1 < P.size
          · simp only [dif_pos hk] at hΨ ⊢
            exact (StateForm.satisfies_congr_of_agree N₂
              (fun _ hc => hright.next_incoming_agree h₂ α
                (Judgement.duration P ⟨k.1, hk⟩) hc) σ P
              ⟨k.1 + 1, by omega⟩).2 hΨ.2.2
          · simp only [dif_neg hk] at hΨ
            exact hΨ.2.2.elim
  | some N₁ =>
      cases h₂ : Ψ.nextPart with
      | none =>
          simp only [TransitionForm.Satisfies, h₁] at hΦ
          simp only [TransitionForm.union, unionNext, h₁, h₂]
          by_cases hk : k.1 < P.size
          · simp only [dif_pos hk] at hΦ ⊢
            exact (StateForm.satisfies_congr_of_agree N₁
              (fun _ hc => hleft.next_incoming_agree h₁ α
                (Judgement.duration P ⟨k.1, hk⟩) hc) σ P
              ⟨k.1 + 1, by omega⟩).2 hΦ.2.2
          · simp only [dif_neg hk] at hΦ
            exact hΦ.2.2.elim
      | some N₂ =>
          simp only [TransitionForm.Satisfies, h₁] at hΦ
          simp only [TransitionForm.Satisfies, h₂] at hΨ
          simp only [TransitionForm.union, unionNext, h₁, h₂]
          by_cases hk : k.1 < P.size
          · simp only [dif_pos hk] at hΦ hΨ ⊢
            let δ := Judgement.duration P ⟨k.1, hk⟩
            let β := ClockResetSet.elapse
              ((Φ.current.union Ψ.current).resets.apply α) δ
            have hN₁ : N₁.Satisfies σ P β ⟨k.1 + 1, by omega⟩ := by
              exact (StateForm.satisfies_congr_of_agree N₁
                (fun _ hc => hleft.next_incoming_agree h₁ α δ hc) σ P
                ⟨k.1 + 1, by omega⟩).2 hΦ.2.2
            have hN₂ : N₂.Satisfies σ P β ⟨k.1 + 1, by omega⟩ := by
              exact (StateForm.satisfies_congr_of_agree N₂
                (fun _ hc => hright.next_incoming_agree h₂ α δ hc) σ P
                ⟨k.1 + 1, by omega⟩).2 hΨ.2.2
            exact StateForm.satisfies_union_of N₁ N₂
              (hnextCon N₁ N₂ h₁ h₂)
              ((hleft.nextFresh N₁ (N₁.union N₂) h₁ (by
                simp [TransitionForm.union, unionNext, h₁, h₂])).mono_left (by
                  intro c hc
                  change c ∈ (N₁.resets.union N₂.resets).clocks \ N₁.resets.clocks
                  rw [ClockResetSet.clocks_union]
                  exact ⟨Or.inr hc.1, hc.2⟩))
              ((hright.nextFresh N₂ (N₁.union N₂) h₂ (by
                simp [TransitionForm.union, unionNext, h₁, h₂])).mono_left (by
                  intro c hc
                  change c ∈ (N₁.resets.union N₂.resets).clocks \ N₂.resets.clocks
                  rw [ClockResetSet.clocks_union]
                  exact ⟨Or.inl hc.1, hc.2⟩))
              hN₁ hN₂
          · simp only [dif_neg hk] at hΦ
            exact hΦ.2.2.elim

/-- Semantic equivalence of the normalized transition union with conjunction
of its two inputs, under the alpha-conversion side conditions. -/
theorem TransitionForm.satisfies_union_iff
    (Φ Ψ : TransitionForm Clock Var)
    (hleft : Φ ⊑ Φ.union Ψ) (hright : Ψ ⊑ Φ.union Ψ)
    (hcurrentCon : Φ.current.resets.Consistent Ψ.current.resets)
    (hnextCon : ∀ N₁ N₂, Φ.nextPart = some N₁ → Ψ.nextPart = some N₂ →
      N₁.resets.Consistent N₂.resets)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (Φ.union Ψ).Satisfies σ P α k ↔
      Φ.Satisfies σ P α k ∧ Ψ.Satisfies σ P α k := by
  constructor
  · exact Φ.satisfies_left_and_right_of_union hleft hright
  · rintro ⟨hΦ, hΨ⟩
    exact Φ.satisfies_union_of Ψ hleft hright hcurrentCon hnextCon hΦ hΨ

/-- All side conditions for normalizing the conjunction of two transition
forms after alpha-converting their reset-bound clocks. -/
structure TransitionForm.UnionCompatible
    (Φ Ψ : TransitionForm Clock Var) : Prop where
  leftSubsumed : Φ ⊑ Φ.union Ψ
  rightSubsumed : Ψ ⊑ Φ.union Ψ
  currentConsistent : Φ.current.resets.Consistent Ψ.current.resets
  nextConsistent : ∀ N₁ N₂, Φ.nextPart = some N₁ → Ψ.nextPart = some N₂ →
    N₁.resets.Consistent N₂.resets

/-- Semantic meaning of placing both transition forms in the same expanded
branch. -/
def TransitionForm.ConjoinedSatisfies (Φ Ψ : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) : Prop :=
  Φ.Satisfies σ P α k ∧ Ψ.Satisfies σ P α k

/-- Residual transition-form existence under the compatibility conditions of Lemma 4.13.
The witness is exactly the six-component union displayed in the appendix. -/
theorem TransitionForm.normalization_exists
    (Φ Ψ : TransitionForm Clock Var) (h : Φ.UnionCompatible Ψ) :
    ∃ Φhat : TransitionForm Clock Var,
      Φhat = Φ.union Ψ ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : Judgement.Position P),
        Φhat.Satisfies σ P α k ↔ Φ.ConjoinedSatisfies Ψ σ P α k := by
  refine ⟨Φ.union Ψ, rfl, ?_⟩
  intro σ P α k
  exact Φ.satisfies_union_iff Ψ h.leftSubsumed h.rightSubsumed
    h.currentConsistent h.nextConsistent σ P α k

/-- The normalized result extends both the
original transition form and the selected branch form. -/
theorem TransitionForm.normalization_subsumptions
    (Φ Ψ : TransitionForm Clock Var) (h : Φ.UnionCompatible Ψ) :
    (Φ ⊑ Φ.union Ψ) ∧ (Ψ ⊑ Φ.union Ψ) :=
  ⟨h.leftSubsumed, h.rightSubsumed⟩

/-- Extra resets disjoint from a branch's unbound free clocks preserve its
valuation. This is the reset-agreement step used in rule-closure monotonicity. -/
theorem ClockResetSet.apply_agree_of_fresh_extension
    {Λ₁ Λ₂ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    (hsub : Λ₁.Subset Λ₂)
    (hfresh : Disjoint (Λ₂.clocks \ Λ₁.clocks) (Ψ.freeClocks \ Λ₁.clocks))
    (α : ClockValuation Clock) :
    ∀ c ∈ Ψ.freeClocks, Λ₁.apply α c = Λ₂.apply α c := by
  intro c hc
  symm
  apply ClockResetSet.apply_eq_of_subset_of_not_extra hsub α
  intro hextra
  exact Set.disjoint_left.1 hfresh hextra ⟨hc, hextra.2⟩

/-- The branch and its non-predicate part both retain their meaning under
an irrelevant extension of the enclosing reset set. -/
theorem Judgement.equivalent_of_fresh_reset_extension
    {Λ₁ Λ₂ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    (hsub : Λ₁.Subset Λ₂)
    (hfresh : Disjoint (Λ₂.clocks \ Λ₁.clocks) (Ψ.freeClocks \ Λ₁.clocks))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (Judgement.Satisfies σ P (Λ₁.apply α) k Ψ ↔
      Judgement.Satisfies σ P (Λ₂.apply α) k Ψ) ∧
    (Judgement.NonPredicateSatisfies σ P (Λ₁.apply α) k Ψ ↔
      Judgement.NonPredicateSatisfies σ P (Λ₂.apply α) k Ψ) := by
  have h := ClockResetSet.apply_agree_of_fresh_extension hsub hfresh α
  exact ⟨Judgement.satisfies_congr_of_agree h σ P k,
    Judgement.nonPredicateSatisfies_congr_of_agree h σ P k⟩

/-- The expansion information needed by closure construction.  `rule` is a
relation because clocked rules choose fresh clock names. `branchTransitionForm`
records the alpha-conversion and reset merging described at
`app:expansion-branch-clocks`; its final argument is the resulting transition
form to which syntactic subsumption applies. -/
structure ExpansionRules (Clock Var : Type*) where
  rule : IntervalPredicate Clock Var → ExpansionRule Clock Var → Prop
  branchTransitionForm : ClockResetSet Clock → Judgement Clock Var →
    TransitionForm Clock Var → Prop
  branchTransitionForm_mono : ∀ {Λ₁ Λ₂ Ψ B}, Λ₁.Subset Λ₂ →
    Disjoint (Λ₂.clocks \ Λ₁.clocks) (Ψ.freeClocks \ Λ₁.clocks) →
    branchTransitionForm Λ₁ Ψ B → branchTransitionForm Λ₂ Ψ B
  branchFreeClocks : ∀ {p R Ψ}, rule p R → Ψ ∈ R.branches →
    Ψ.freeClocks ⊆ p.clockSet
  branchTransitionForm_reduced : ∀ {p R Ψ Λ B q}, rule p R → Ψ ∈ R.branches →
    branchTransitionForm Λ Ψ B → Judgement.predicate q ∈ B.current.locals →
      q.complexity < p.complexity
  /-- Transition-form representation combines the enclosing reset set with the branch's resets
  without changing branch satisfaction. This includes the alpha-conversion
  convention from `app:expansion-branch-clocks`. -/
  branchTransitionForm_satisfies_iff : ∀ {Ψ Λ B}, branchTransitionForm Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      B.Satisfies σ P α k ↔
        Judgement.Satisfies σ P (Λ.apply α) k Ψ
  branchTransitionForm_nonPredicateSatisfies_iff : ∀ {Ψ Λ B}, branchTransitionForm Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      B.NonPredicateSatisfies σ P α k ↔
        Judgement.NonPredicateSatisfies σ P (Λ.apply α) k Ψ
  /-- Recursive invariant evaluation of the raw branch supplies the direct
  current-local invariant of its anchored transition form. -/
  branchTransitionForm_currentInvariant : ∀ {Ψ Λ B}, branchTransitionForm Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P)
      (hk : k.1 < P.size),
      Judgement.EvaluatedInvariant σ P (Λ.apply α) k Ψ →
      Judgement.SetInvariant (P.interval ⟨k.1, hk⟩)
        (B.current.resets.apply α) B.current.locals
  /-- The same transition-form representation contract for the optional next-local component. -/
  branchTransitionForm_nextInvariant : ∀ {Ψ Λ B}, branchTransitionForm Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P)
      (hnext : k.1 + 1 < P.size) (N : StateForm Clock Var),
      B.nextPart = some N →
      Judgement.EvaluatedInvariant σ P (Λ.apply α) k Ψ →
      Judgement.SetInvariant (P.interval ⟨k.1 + 1, hnext⟩)
        (N.resets.apply (ClockResetSet.elapse (B.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))) N.locals

namespace ExpansionRules

variable {Clock Var : Type*}

/-- Whether the rule family assigns an expansion rule to `p`. -/
def HasRule (E : ExpansionRules Clock Var) (p : IntervalPredicate Clock Var) : Prop :=
  ∃ R, E.rule p R

/-- Definition 4.6.  The branch transition-form relation
encapsulates the equivalent revised presentation using a compatible
subset `Γ` of the enclosing reset set. -/
def RuleClosedFor (E : ExpansionRules Clock Var) (Φ : TransitionForm Clock Var)
    (p : IntervalPredicate Clock Var) : Prop :=
  Judgement.predicate p ∈ Φ.current.locals ∧
    (¬ E.HasRule p ∨
      ∃ R, E.rule p R ∧
        ∃ Ψ ∈ R.branches, ∃ B,
          E.branchTransitionForm Φ.current.resets Ψ B ∧ B ⊑ Φ)

/-- A transition form is closed when every interval predicate in its current
local component is rule-closed. -/
def IsClosed (E : ExpansionRules Clock Var) (Φ : TransitionForm Clock Var) : Prop :=
  ∀ p, Judgement.predicate p ∈ Φ.current.locals → E.RuleClosedFor Φ p

/-- Single-predicate expansion. A nontrivial expansion is a minimal
rule-closed extension for the selected current interval predicate. -/
def PExpansion (E : ExpansionRules Clock Var) (p : IntervalPredicate Clock Var)
    (Φ Φ' : TransitionForm Clock Var) : Prop :=
  Judgement.predicate p ∈ Φ.current.locals ∧
    ((E.RuleClosedFor Φ p ∧ Φ' = Φ) ∨
      (¬ E.RuleClosedFor Φ p ∧ (Φ ⊑ Φ') ∧ E.RuleClosedFor Φ' p ∧
        ∀ Θ : TransitionForm Clock Var,
          (Φ ⊑ Θ) → E.RuleClosedFor Θ p → (Θ ⊑ Φ') → (Φ' ⊑ Θ)))

end ExpansionRules

namespace TransitionForm

/-- Remove one current local judgement without changing constraints, resets,
or the optional next component. -/
def eraseCurrentLocal (J : Judgement Clock Var)
    (Φ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  { current :=
      { constraints := Φ.current.constraints
        constraints_finite := Φ.current.constraints_finite
        resets := Φ.current.resets
        locals := Φ.current.locals \ {J}
        locals_finite := Φ.current.locals_finite.sdiff
        locals_are_local := fun K hK => Φ.current.locals_are_local K hK.1 }
    nextPart := Φ.nextPart }

/-- Remove one judgement from the optional next component, leaving an absent
next component absent. -/
def eraseStateLocal (J : Judgement Clock Var) (S : StateForm Clock Var) :
    StateForm Clock Var :=
  { constraints := S.constraints
    constraints_finite := S.constraints_finite
    resets := S.resets
    locals := S.locals \ {J}
    locals_finite := S.locals_finite.sdiff
    locals_are_local := fun K hK => S.locals_are_local K hK.1 }

def eraseNextLocal (J : Judgement Clock Var)
    (Φ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  { current := Φ.current
    nextPart := Φ.nextPart.map (eraseStateLocal J) }

theorem subsumed_eraseCurrentLocal
    (J : Judgement Clock Var) (Φ : TransitionForm Clock Var) :
    Φ.eraseCurrentLocal J ⊑ Φ := by
  refine ⟨by intro c hc; exact hc.elim, fun _ h => h,
    ClockResetSet.subset_refl _, fun _ h => h.1, fun h => h,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro N₁ N₂ h₁ h₂
    have h₁' : Φ.nextPart = some N₁ := by simpa [eraseCurrentLocal] using h₁
    rw [h₂] at h₁'
    cases h₁'
    exact fun _ h => h
  · intro N₁ N₂ h₁ h₂
    have h₁' : Φ.nextPart = some N₁ := by simpa [eraseCurrentLocal] using h₁
    rw [h₂] at h₁'
    cases h₁'
    exact ClockResetSet.subset_refl _
  · intro N₁ N₂ h₁ h₂
    have h₁' : Φ.nextPart = some N₁ := by simpa [eraseCurrentLocal] using h₁
    rw [h₂] at h₁'
    cases h₁'
    exact fun _ h => h
  · simp [eraseCurrentLocal]
  · intro N₁ N₂ h₁ h₂
    have h₁' : Φ.nextPart = some N₁ := by simpa [eraseCurrentLocal] using h₁
    rw [h₂] at h₁'
    cases h₁'
    simp

theorem source_subsumed_eraseCurrentLocal
    {J : Judgement Clock Var} {Φ Φ' : TransitionForm Clock Var}
    (hsub : Φ ⊑ Φ') (hJ : J ∉ Φ.current.locals) :
    Φ ⊑ Φ'.eraseCurrentLocal J := by
  refine ⟨hsub.requiredResets, hsub.currentConstraints, hsub.currentResets,
    ?_, hsub.nextShape, ?_, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact ⟨hsub.currentLocals hK, fun hEq => hJ (hEq ▸ hK)⟩
  · simpa [eraseCurrentLocal] using hsub.nextConstraints
  · simpa [eraseCurrentLocal] using hsub.nextResets
  · simpa [eraseCurrentLocal] using hsub.nextLocals
  · simpa [eraseCurrentLocal] using hsub.outerFresh
  · simpa [eraseCurrentLocal] using hsub.nextFresh

theorem not_subsumed_eraseCurrentLocal
    {J : Judgement Clock Var} {Φ : TransitionForm Clock Var}
    (hJ : J ∈ Φ.current.locals) : ¬ (Φ ⊑ Φ.eraseCurrentLocal J) := by
  intro hsub
  exact (hsub.currentLocals hJ).2 rfl

theorem subsumed_eraseNextLocal
    (J : Judgement Clock Var) (Φ : TransitionForm Clock Var) :
    Φ.eraseNextLocal J ⊑ Φ := by
  refine ⟨by intro c hc; exact hc.elim, fun _ h => h,
    ClockResetSet.subset_refl _, fun _ h => h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hΦ : Φ.nextPart <;> simp [eraseNextLocal, hΦ]
  · intro N₁ N₂ h₁ h₂
    cases hΦ : Φ.nextPart with
    | none => simp [eraseNextLocal, hΦ] at h₁
    | some S =>
        have h₁' : eraseStateLocal J S = N₁ := by
          simpa [eraseNextLocal, hΦ] using h₁
        have h₂' : S = N₂ := Option.some.inj (hΦ.symm.trans h₂)
        subst N₁; subst N₂
        exact fun _ h => h
  · intro N₁ N₂ h₁ h₂
    cases hΦ : Φ.nextPart with
    | none => simp [eraseNextLocal, hΦ] at h₁
    | some S =>
        have h₁' : eraseStateLocal J S = N₁ := by
          simpa [eraseNextLocal, hΦ] using h₁
        have h₂' : S = N₂ := Option.some.inj (hΦ.symm.trans h₂)
        subst N₁; subst N₂
        exact ClockResetSet.subset_refl _
  · intro N₁ N₂ h₁ h₂
    cases hΦ : Φ.nextPart with
    | none => simp [eraseNextLocal, hΦ] at h₁
    | some S =>
        have h₁' : eraseStateLocal J S = N₁ := by
          simpa [eraseNextLocal, hΦ] using h₁
        have h₂' : S = N₂ := Option.some.inj (hΦ.symm.trans h₂)
        subst N₁; subst N₂
        exact fun _ h => h.1
  · simp [eraseNextLocal]
  · intro N₁ N₂ h₁ h₂
    cases hΦ : Φ.nextPart with
    | none => simp [eraseNextLocal, hΦ] at h₁
    | some S =>
        have h₁' : eraseStateLocal J S = N₁ := by
          simpa [eraseNextLocal, hΦ] using h₁
        have h₂' : S = N₂ := Option.some.inj (hΦ.symm.trans h₂)
        subst N₁; subst N₂
        simp [eraseStateLocal]

theorem source_subsumed_eraseNextLocal
    {J : Judgement Clock Var} {Φ Φ' : TransitionForm Clock Var}
    {N N' : StateForm Clock Var} (hsub : Φ ⊑ Φ')
    (hN : Φ.nextPart = some N) (hN' : Φ'.nextPart = some N')
    (hJ : J ∉ N.locals) : Φ ⊑ Φ'.eraseNextLocal J := by
  refine ⟨hsub.requiredResets, hsub.currentConstraints, hsub.currentResets,
    hsub.currentLocals, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eraseNextLocal, hN']
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextConstraints
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextResets
  · intro A B hA hB
    have hB' : B = eraseStateLocal J N' := by
      have : some (eraseStateLocal J N') = some B := by
        simpa [eraseNextLocal, hN'] using hB
      exact (Option.some.inj this).symm
    subst B
    have hA' : A = N := by
      rw [hN] at hA
      exact (Option.some.inj hA).symm
    subst A
    intro K hK
    refine ⟨hsub.nextLocals N N' hN hN' hK, ?_⟩
    intro hKJ
    exact hJ (hKJ ▸ hK)
  · simpa [eraseNextLocal] using hsub.outerFresh
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextFresh

/-- A source still subsumes a target after deleting a next-local judgement when
that judgement is absent from every next state carried by the source.  This
also covers a source with no next component. -/
theorem source_subsumed_eraseNextLocal_of_absent
    {J : Judgement Clock Var} {Φ Φ' : TransitionForm Clock Var}
    {N' : StateForm Clock Var} (hsub : Φ ⊑ Φ')
    (hN' : Φ'.nextPart = some N')
    (hJ : ∀ N, Φ.nextPart = some N → J ∉ N.locals) :
    Φ ⊑ Φ'.eraseNextLocal J := by
  refine ⟨hsub.requiredResets, hsub.currentConstraints, hsub.currentResets,
    hsub.currentLocals, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eraseNextLocal, hN']
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextConstraints
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextResets
  · intro A B hA hB
    have hB' : B = eraseStateLocal J N' := by
      have : some (eraseStateLocal J N') = some B := by
        simpa [eraseNextLocal, hN'] using hB
      exact (Option.some.inj this).symm
    subst B
    intro K hK
    refine ⟨hsub.nextLocals A N' hA hN' hK, ?_⟩
    intro hKJ
    exact hJ A hA (hKJ ▸ hK)
  · simpa [eraseNextLocal] using hsub.outerFresh
  · simpa [eraseNextLocal, eraseStateLocal, hN'] using hsub.nextFresh

theorem not_subsumed_eraseNextLocal
    {J : Judgement Clock Var} {Φ : TransitionForm Clock Var}
    {N : StateForm Clock Var} (hN : Φ.nextPart = some N)
    (hJ : J ∈ N.locals) : ¬ (Φ ⊑ Φ.eraseNextLocal J) := by
  intro hsub
  have hshape : (Φ.eraseNextLocal J).nextPart = some (eraseStateLocal J N) := by
    simp [eraseNextLocal, hN]
  exact (hsub.nextLocals N _ hN hshape hJ).2 rfl

end TransitionForm

namespace ExpansionRules

theorem PExpansion.refl_of_ruleClosed {E : ExpansionRules Clock Var}
    {p : IntervalPredicate Clock Var} {Φ : TransitionForm Clock Var}
    (h : E.RuleClosedFor Φ p) : E.PExpansion p Φ Φ := by
  exact ⟨h.1, Or.inl ⟨h, rfl⟩⟩

theorem PExpansion.extension {E : ExpansionRules Clock Var}
    {p : IntervalPredicate Clock Var} {Φ Φ' : TransitionForm Clock Var}
    (h : E.PExpansion p Φ Φ') : Φ ⊑ Φ' := by
  rcases h.2 with ⟨_, rfl⟩ | h
  · exact syntacticallySubsumed_refl (∅ : Set Clock) _
      (by intro c hc; exact hc.elim)
  · exact h.2.1

theorem PExpansion.target_ruleClosed {E : ExpansionRules Clock Var}
    {p : IntervalPredicate Clock Var} {Φ Φ' : TransitionForm Clock Var}
    (h : E.PExpansion p Φ Φ') : E.RuleClosedFor Φ' p := by
  rcases h.2 with ⟨hc, rfl⟩ | h
  · exact hc
  · exact h.2.2.1

/-- A rule-closed satisfied form supplies a satisfied branch transition form whenever
the selected predicate has a rule. This is the semantic bridge needed by the
rule-specific evaluated-invariant theorems. -/
theorem RuleClosedFor.exists_satisfied_witness
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ : TransitionForm Clock Var} (hclosed : E.RuleClosedFor Φ p)
    (hhas : E.HasRule p) {σ : FiniteSignal Var}
    {P : IntervalPartition σ.domain} {α : ClockValuation Clock}
    {k : Judgement.Position P} (hΦ : Φ.Satisfies σ P α k) :
    ∃ R, E.rule p R ∧ ∃ Ψ ∈ R.branches, ∃ B,
      E.branchTransitionForm Φ.current.resets Ψ B ∧ (B ⊑ Φ) ∧
        B.Satisfies σ P α k := by
  rcases hclosed.2 with hnone | ⟨R, hR, Ψ, hΨ, B, hB, hBsub⟩
  · exact (hnone hhas).elim
  · exact ⟨R, hR, Ψ, hΨ, B, hB, hBsub,
      transitionForm_subsumption_sound hBsub hΦ⟩

theorem PExpansion.eq_of_source_ruleClosed {E : ExpansionRules Clock Var}
    {p : IntervalPredicate Clock Var} {Φ Φ' : TransitionForm Clock Var}
    (h : E.PExpansion p Φ Φ') (hc : E.RuleClosedFor Φ p) : Φ' = Φ := by
  rcases h.2 with h | h
  · exact h.2
  · exact (h.1 hc).elim

/-- The complexity part of the local expansion shape argument, once a newly added
predicate has been located in the branch witnessing rule-closure. -/
theorem RuleClosedFor.branch_predicate_reduced
    {E : ExpansionRules Clock Var} {p q : IntervalPredicate Clock Var}
    {Φ : TransitionForm Clock Var}
    (hclosed : E.RuleClosedFor Φ p) (hrule : E.HasRule p)
    (hsupported : ∀ {R Ψ B}, E.rule p R → Ψ ∈ R.branches →
      E.branchTransitionForm Φ.current.resets Ψ B → (B ⊑ Φ) →
        Judgement.predicate q ∈ B.current.locals) :
    q.complexity < p.complexity := by
  rcases hclosed with ⟨_, hnorule | ⟨R, hR, Ψ, hΨ, B, hB, hsub⟩⟩
  · exact (hnorule hrule).elim
  · exact E.branchTransitionForm_reduced hR hΨ hB
      (hsupported hR hΨ hB hsub)

/-- Every current interval predicate
introduced by a nontrivial `p`-expansion has lower complexity than `p`. -/
theorem PExpansion.localExpansionShape
    {E : ExpansionRules Clock Var} {p q : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ')
    (hq' : Judgement.predicate q ∈ Φ'.current.locals)
    (hq : Judgement.predicate q ∉ Φ.current.locals) :
    q.complexity < p.complexity := by
  rcases hexp with ⟨hp, hid | hnontrivial⟩
  · exact (hopen hid.1).elim
  · rcases hnontrivial with ⟨_, hsub, hclosed, hminimal⟩
    rcases hclosed with ⟨hp', hnorule | ⟨R, hR, Ψ, hΨ, B, hB, hBsub⟩⟩
    · exact (hopen ⟨hp, Or.inl hnorule⟩).elim
    · apply E.branchTransitionForm_reduced hR hΨ hB
      by_contra hqB
      let Θ := Φ'.eraseCurrentLocal (Judgement.predicate q)
      have hΦΘ : Φ ⊑ Θ :=
        TransitionForm.source_subsumed_eraseCurrentLocal hsub hq
      have hBΘ : B ⊑ Θ :=
        TransitionForm.source_subsumed_eraseCurrentLocal hBsub hqB
      have hp_ne_q : Judgement.predicate p ≠ Judgement.predicate q := by
        intro hpq
        exact hq (hpq ▸ hp)
      have hclosedΘ : E.RuleClosedFor Θ p := by
        refine ⟨⟨hp', ?_⟩, Or.inr ⟨R, hR, Ψ, hΨ, B, hB, hBΘ⟩⟩
        exact fun hpq => hp_ne_q hpq
      have hΘΦ' : Θ ⊑ Φ' :=
        TransitionForm.subsumed_eraseCurrentLocal _ _
      have hΦ'Θ : Φ' ⊑ Θ := hminimal Θ hΦΘ hclosedΘ hΘΦ'
      exact TransitionForm.not_subsumed_eraseCurrentLocal hq' hΦ'Θ

/-- The structural core of the local expansion shape argument: every newly added
current predicate occurs in any branch transition form witnessing target
rule-closure for the expanded predicate. -/
theorem PExpansion.newPredicate_mem_witnessBranch
    {E : ExpansionRules Clock Var} {p q : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ')
    (hq' : Judgement.predicate q ∈ Φ'.current.locals)
    (hq : Judgement.predicate q ∉ Φ.current.locals)
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var}
    (hR : E.rule p R) (hΨ : Ψ ∈ R.branches)
    (hB : E.branchTransitionForm Φ'.current.resets Ψ B) (hBsub : B ⊑ Φ') :
    Judgement.predicate q ∈ B.current.locals := by
  by_contra hqB
  rcases hexp.2 with hid | hnontrivial
  · exact hopen hid.1
  · rcases hnontrivial with ⟨_, hsub, _, hminimal⟩
    let Θ := Φ'.eraseCurrentLocal (Judgement.predicate q)
    have hΦΘ : Φ ⊑ Θ :=
      TransitionForm.source_subsumed_eraseCurrentLocal hsub hq
    have hBΘ : B ⊑ Θ :=
      TransitionForm.source_subsumed_eraseCurrentLocal hBsub hqB
    have hp_ne_q : Judgement.predicate p ≠ Judgement.predicate q := by
      intro hpq
      exact hq (hpq ▸ hexp.1)
    have hclosedΘ : E.RuleClosedFor Θ p := by
      refine ⟨⟨hexp.target_ruleClosed.1, ?_⟩,
        Or.inr ⟨R, hR, Ψ, hΨ, B, hB, hBΘ⟩⟩
      exact fun hpq => hp_ne_q hpq
    have hΘΦ' : Θ ⊑ Φ' := TransitionForm.subsumed_eraseCurrentLocal _ _
    have hΦ'Θ : Φ' ⊑ Θ := hminimal Θ hΦΘ hclosedΘ hΘΦ'
    exact TransitionForm.not_subsumed_eraseCurrentLocal hq' hΦ'Θ

/-- Every newly added predicate in the next component occurs in any anchored
branch witnessing target rule-closure.  As in the current-component case,
otherwise deleting that occurrence would contradict expansion minimality. -/
theorem PExpansion.newNextPredicate_mem_witnessBranch
    {E : ExpansionRules Clock Var} {p q : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var} {N N' : StateForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ')
    (hN : Φ.nextPart = some N) (hN' : Φ'.nextPart = some N')
    (hq' : Judgement.predicate q ∈ N'.locals)
    (hq : Judgement.predicate q ∉ N.locals)
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var}
    (hR : E.rule p R) (hΨ : Ψ ∈ R.branches)
    (hB : E.branchTransitionForm Φ'.current.resets Ψ B) (hBsub : B ⊑ Φ') :
    ∃ NB, B.nextPart = some NB ∧ Judgement.predicate q ∈ NB.locals := by
  by_contra hqB
  rcases hexp.2 with hid | hnontrivial
  · exact hopen hid.1
  · rcases hnontrivial with ⟨_, hsub, _, hminimal⟩
    let Θ := Φ'.eraseNextLocal (Judgement.predicate q)
    have hΦΘ : Φ ⊑ Θ :=
      TransitionForm.source_subsumed_eraseNextLocal hsub hN hN' hq
    have hBΘ : B ⊑ Θ :=
      TransitionForm.source_subsumed_eraseNextLocal_of_absent hBsub hN' (by
        intro NB hBN hqNB
        exact hqB ⟨NB, hBN, hqNB⟩)
    have hclosedΘ : E.RuleClosedFor Θ p := by
      refine ⟨hexp.target_ruleClosed.1,
        Or.inr ⟨R, hR, Ψ, hΨ, B, hB, hBΘ⟩⟩
    have hΘΦ' : Θ ⊑ Φ' := TransitionForm.subsumed_eraseNextLocal _ _
    have hΦ'Θ : Φ' ⊑ Θ := hminimal Θ hΦΘ hclosedΘ hΘΦ'
    exact TransitionForm.not_subsumed_eraseNextLocal hN' hq' hΦ'Θ

/-- Variant of `newNextPredicate_mem_witnessBranch` for an expansion which
introduces the entire next component. -/
theorem PExpansion.newNextPredicate_mem_witnessBranch_of_source_absent
    {E : ExpansionRules Clock Var} {p q : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var} {N' : StateForm Clock Var}
    (hexp : E.PExpansion p Φ Φ')
    (hnone : Φ.nextPart = none) (hN' : Φ'.nextPart = some N')
    (hq' : Judgement.predicate q ∈ N'.locals)
    {R : ExpansionRule Clock Var} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var}
    (hR : E.rule p R) (hΨ : Ψ ∈ R.branches)
    (hB : E.branchTransitionForm Φ'.current.resets Ψ B) (hBsub : B ⊑ Φ') :
    ∃ NB, B.nextPart = some NB ∧ Judgement.predicate q ∈ NB.locals := by
  by_contra hqB
  rcases hexp.2 with hid | hnontrivial
  · rw [hid.2, hnone] at hN'
    cases hN'
  · rcases hnontrivial with ⟨_, hsub, _, hminimal⟩
    let Θ := Φ'.eraseNextLocal (Judgement.predicate q)
    have hΦΘ : Φ ⊑ Θ :=
      TransitionForm.source_subsumed_eraseNextLocal_of_absent hsub hN' (by
        intro N hN
        rw [hnone] at hN
        cases hN)
    have hBΘ : B ⊑ Θ :=
      TransitionForm.source_subsumed_eraseNextLocal_of_absent hBsub hN' (by
        intro NB hBN hqNB
        exact hqB ⟨NB, hBN, hqNB⟩)
    have hclosedΘ : E.RuleClosedFor Θ p := by
      refine ⟨hexp.target_ruleClosed.1,
        Or.inr ⟨R, hR, Ψ, hΨ, B, hB, hBΘ⟩⟩
    have hΘΦ' : Θ ⊑ Φ' := TransitionForm.subsumed_eraseNextLocal _ _
    have hΦ'Θ : Φ' ⊑ Θ := hminimal Θ hΦΘ hclosedΘ hΘΦ'
    exact TransitionForm.not_subsumed_eraseNextLocal hN' hq' hΦ'Θ

/-- A predicate property holds for all direct current predicates. This
abstracts the valuation-dependent invariant while isolating the structural
expansion argument. -/
def AllCurrentPredicates
    (Φ : TransitionForm Clock Var) (Property : IntervalPredicate Clock Var → Prop) : Prop :=
  ∀ p, Judgement.predicate p ∈ Φ.current.locals → Property p

/-- Every predicate contributed by an rule branch in transition form has `Property`. -/
def BranchesPreserve
    (E : ExpansionRules Clock Var) (p : IntervalPredicate Clock Var)
    (Φ : TransitionForm Clock Var)
    (Property : IntervalPredicate Clock Var → Prop) : Prop :=
  ∀ {R Ψ B}, E.rule p R → Ψ ∈ R.branches →
    E.branchTransitionForm Φ.current.resets Ψ B → (B ⊑ Φ) →
      ∀ q, Judgement.predicate q ∈ B.current.locals → Property q

/-- Every predicate in the next component contributed by an anchored rule
branch has `Property`. -/
def NextBranchesPreserve
    (E : ExpansionRules Clock Var) (p : IntervalPredicate Clock Var)
    (Φ : TransitionForm Clock Var)
    (Property : IntervalPredicate Clock Var → Prop) : Prop :=
  ∀ {R Ψ B NB}, E.rule p R → Ψ ∈ R.branches →
    E.branchTransitionForm Φ.current.resets Ψ B → (B ⊑ Φ) → B.nextPart = some NB →
      ∀ q, Judgement.predicate q ∈ NB.locals → Property q

/-- Branch invariant condition for the residual form of Proposition 3.14.
It is stated for an arbitrary incoming valuation so it can be instantiated
after the enclosing transition-form resets have been applied. -/
def PreservesEvaluatedInvariant (E : ExpansionRules Clock Var) : Prop :=
  ∀ {p R Ψ}, E.rule p R → Ψ ∈ R.branches →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (β : ClockValuation Clock) (k : Judgement.Position P),
      (∀ hk : k.1 < P.size,
        IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) β p) →
      Judgement.NonPredicateSatisfies σ P β k Ψ →
      Judgement.EvaluatedInvariant σ P β k Ψ

/-- Concrete current-branch obligation obtained from rule-level invariant
preservation and satisfaction of the expanded target form. -/
theorem PreservesEvaluatedInvariant.currentBranches
    {E : ExpansionRules Clock Var} (hrules : E.PreservesEvaluatedInvariant)
    {p : IntervalPredicate Clock Var} {σ : FiniteSignal Var}
    {Φ : TransitionForm Clock Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hk : k.1 < P.size) (hΦ : Φ.NonPredicateSatisfies σ P α k)
    (hp : IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩)
      (Φ.current.resets.apply α) p) :
    E.BranchesPreserve p Φ
      (IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩)
        (Φ.current.resets.apply α)) := by
  intro R Ψ B hR hΨ hB hBsub q hq
  have hBs : B.NonPredicateSatisfies σ P α k :=
    transitionForm_nonPredicate_subsumption_sound hBsub hΦ
  have hraw : Judgement.NonPredicateSatisfies σ P (Φ.current.resets.apply α) k Ψ :=
    (E.branchTransitionForm_nonPredicateSatisfies_iff hB σ P α k).1 hBs
  have heval : Judgement.EvaluatedInvariant σ P
      (Φ.current.resets.apply α) k Ψ :=
    hrules hR hΨ σ P (Φ.current.resets.apply α) k
      (fun hk' => by simpa using hp) hraw
  have hBinv := E.branchTransitionForm_currentInvariant hB σ P α k hk heval
  exact hBsub.currentInvariant_of_source (P.interval ⟨k.1, hk⟩) α hBinv hq

/-- Concrete next-branch obligation obtained from the same rule-level theorem.
The final transport accounts for both outer and inner reset extensions. -/
theorem PreservesEvaluatedInvariant.nextBranches
    {E : ExpansionRules Clock Var} (hrules : E.PreservesEvaluatedInvariant)
    {p : IntervalPredicate Clock Var} {σ : FiniteSignal Var}
    {Φ : TransitionForm Clock Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hnext : k.1 + 1 < P.size) (hΦ : Φ.NonPredicateSatisfies σ P α k)
    (hp : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩)
      (Φ.current.resets.apply α) p) {N' : StateForm Clock Var}
    (hN' : Φ.nextPart = some N') :
    E.NextBranchesPreserve p Φ
      (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hnext⟩)
        (N'.resets.apply (ClockResetSet.elapse (Φ.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩)))) := by
  intro R Ψ B NB hR hΨ hB hBsub hBN q hq
  have hBs : B.NonPredicateSatisfies σ P α k :=
    transitionForm_nonPredicate_subsumption_sound hBsub hΦ
  have hraw : Judgement.NonPredicateSatisfies σ P (Φ.current.resets.apply α) k Ψ :=
    (E.branchTransitionForm_nonPredicateSatisfies_iff hB σ P α k).1 hBs
  have heval : Judgement.EvaluatedInvariant σ P
      (Φ.current.resets.apply α) k Ψ :=
    hrules hR hΨ σ P (Φ.current.resets.apply α) k
      (fun hk => by simpa using hp) hraw
  have hBinv := E.branchTransitionForm_nextInvariant hB σ P α k hnext NB hBN heval
  exact hBsub.nextInvariant_of_source P α k hnext hBN hN' hBinv hq

/-- Structural form of Proposition 4.16: any predicate property
preserved by rule branches is preserved by a `p`-expansion. -/
theorem PExpansion.preservesAllCurrentPredicates
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    {Property : IntervalPredicate Clock Var → Prop}
    (hexp : E.PExpansion p Φ Φ')
    (hΦ : AllCurrentPredicates Φ Property)
    (hbranches : E.BranchesPreserve p Φ' Property) :
    AllCurrentPredicates Φ' Property := by
  intro q hq'
  by_cases hq : Judgement.predicate q ∈ Φ.current.locals
  · exact hΦ q hq
  · rcases hexp.2 with ⟨_, rfl⟩ | hnontrivial
    · exact (hq hq').elim
    · rcases hnontrivial.2.2.1.2 with
        hnorule | ⟨R, hR, Ψ, hΨ, B, hB, hBsub⟩
      · exact (hnontrivial.1 ⟨hexp.1, Or.inl hnorule⟩).elim
      · apply hbranches hR hΨ hB hBsub q
        exact hexp.newPredicate_mem_witnessBranch hnontrivial.1 hq' hq
          hR hΨ hB hBsub

/-- Current-part specialization of Proposition 4.16. Existing
predicates use subsumption freshness; newly introduced predicates use the
branch transition form invariant theorem. -/
theorem PExpansion.preservesCurrentInvariant
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (J : MarkedInterval)
    (α : ClockValuation Clock)
    (hinv : Judgement.SetInvariant J (Φ.current.resets.apply α)
      Φ.current.locals)
    (hbranches : E.BranchesPreserve p Φ'
      (IntervalPredicate.Invariant J (Φ'.current.resets.apply α))) :
    Judgement.SetInvariant J (Φ'.current.resets.apply α)
      Φ'.current.locals := by
  have hold : AllCurrentPredicates Φ
      (IntervalPredicate.Invariant J (Φ'.current.resets.apply α)) := by
    intro q hq
    exact hexp.extension.currentInvariant_of_source J α hinv hq
  exact hexp.preservesAllCurrentPredicates hold hbranches

/-- Next-part specialization of Proposition 4.16. Existing next
predicates are transported through the two fresh reset extensions; a newly
introduced predicate is supplied by the branch transition form witnessing closure. -/
theorem PExpansion.preservesNextInvariant
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {σ : FiniteSignal Var} {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hnext : k.1 + 1 < P.size)
    {N N' : StateForm Clock Var} (hN : Φ.nextPart = some N)
    (hN' : Φ'.nextPart = some N')
    (hinv : Judgement.SetInvariant (P.interval ⟨k.1 + 1, by omega⟩)
      (N.resets.apply (ClockResetSet.elapse (Φ.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) N.locals)
    (hbranches : E.NextBranchesPreserve p Φ'
      (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, by omega⟩)
        (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))))) :
    Judgement.SetInvariant (P.interval ⟨k.1 + 1, by omega⟩)
      (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) N'.locals := by
  intro q hq'
  by_cases hq : Judgement.predicate q ∈ N.locals
  · exact hexp.extension.nextInvariant_of_source P α k hnext hN hN' hinv hq
  · rcases hexp.2 with ⟨_, rfl⟩ | hnontrivial
    · have hNN' : N = N' := Option.some.inj (hN.symm.trans hN')
      subst N'
      exact (hq hq').elim
    · rcases hnontrivial.2.2.1.2 with
        hnorule | ⟨R, hR, Ψ, hΨ, B, hB, hBsub⟩
      · exact (hnontrivial.1 ⟨hexp.1, Or.inl hnorule⟩).elim
      · obtain ⟨NB, hBN, hqNB⟩ :=
          hexp.newNextPredicate_mem_witnessBranch hnontrivial.1 hN hN'
            hq' hq hR hΨ hB hBsub
        exact hbranches hR hΨ hB hBsub hBN q hqNB

/-- If an expansion introduces the whole next component, all of its predicate
invariants come from the branch transition form; there are no inherited next-local
obligations. -/
theorem PExpansion.preservesNextInvariant_of_source_absent
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {σ : FiniteSignal Var} {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hnext : k.1 + 1 < P.size) (hnone : Φ.nextPart = none)
    {N' : StateForm Clock Var} (hN' : Φ'.nextPart = some N')
    (hbranches : E.NextBranchesPreserve p Φ'
      (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, by omega⟩)
        (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))))) :
    Judgement.SetInvariant (P.interval ⟨k.1 + 1, by omega⟩)
      (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) N'.locals := by
  intro q hq'
  rcases hexp.2 with ⟨_, rfl⟩ | hnontrivial
  · simp [hnone] at hN'
  · rcases hnontrivial.2.2.1.2 with
      hnorule | ⟨R, hR, Ψ, hΨ, B, hB, hBsub⟩
    · exact (hnontrivial.1 ⟨hexp.1, Or.inl hnorule⟩).elim
    · obtain ⟨NB, hBN, hqNB⟩ :=
        hexp.newNextPredicate_mem_witnessBranch_of_source_absent
          hnone hN' hq' hR hΨ hB hBsub
      exact hbranches hR hΨ hB hBsub hBN q hqNB

/-- Invariant obligation of the optional next component at a nonterminal
partition position. -/
def _root_.STLTableau.TransitionForm.NextInvariantAt {σ : FiniteSignal Var}
    (Φ : TransitionForm Clock Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hnext : k.1 + 1 < P.size) : Prop :=
  ∀ N, Φ.nextPart = some N →
    Judgement.SetInvariant (P.interval ⟨k.1 + 1, hnext⟩)
      (N.resets.apply (ClockResetSet.elapse (Φ.current.resets.apply α)
        (Judgement.duration P ⟨k.1, by omega⟩))) N.locals

/-- Unified next-component preservation, covering both an inherited next
state and a next state introduced by the expansion. -/
theorem PExpansion.preservesNextInvariantAt
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {σ : FiniteSignal Var} {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hnext : k.1 + 1 < P.size)
    (hinv : Φ.NextInvariantAt P α k hnext)
    (hbranches : ∀ N', Φ'.nextPart = some N' → E.NextBranchesPreserve p Φ'
      (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hnext⟩)
        (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))))) :
    Φ'.NextInvariantAt P α k hnext := by
  intro N' hN'
  cases hN : Φ.nextPart with
  | none =>
      exact hexp.preservesNextInvariant_of_source_absent P α k hnext hN hN'
        (hbranches N' hN')
  | some N =>
      exact hexp.preservesNextInvariant P α k hnext hN hN'
        (hinv N hN) (hbranches N' hN')

/-- The current and optional-next invariant asserted by
Proposition 4.16 at a nonterminal position. -/
def _root_.STLTableau.TransitionForm.InvariantAt {σ : FiniteSignal Var}
    (Φ : TransitionForm Clock Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hk : k.1 < P.size) : Prop :=
  Judgement.SetInvariant (P.interval ⟨k.1, by omega⟩)
      (Φ.current.resets.apply α) Φ.current.locals ∧
    ∀ hnext : k.1 + 1 < P.size, Φ.NextInvariantAt P α k hnext

/-- Proposition 4.16 at the transition-form abstraction
boundary. Rule-specific work is isolated in the two branch hypotheses. -/
theorem PExpansion.preservesInvariantAt
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {σ : FiniteSignal Var} {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hk : k.1 < P.size) (hinv : Φ.InvariantAt P α k hk)
    (hcurrent : E.BranchesPreserve p Φ'
      (IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩)
        (Φ'.current.resets.apply α)))
    (hnextBranches : ∀ (hnext : k.1 + 1 < P.size) N', Φ'.nextPart = some N' →
      E.NextBranchesPreserve p Φ'
      (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hnext⟩)
        (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))))) :
    Φ'.InvariantAt P α k hk := by
  exact ⟨hexp.preservesCurrentInvariant (P.interval ⟨k.1, by omega⟩) α
      hinv.1 hcurrent,
    fun hnext => hexp.preservesNextInvariantAt P α k hnext
      (hinv.2 hnext) (hnextBranches hnext)⟩

/-- Proposition 4.16 with its branch obligations
discharged by the rule family's rule-level theorem. Satisfaction of the
expanded form supplies satisfaction of every subsumed witness branch. -/
theorem PExpansion.preservesInvariantAt_of_ruleInvariant
    {E : ExpansionRules Clock Var} (hrules : E.PreservesEvaluatedInvariant)
    {p : IntervalPredicate Clock Var} {σ : FiniteSignal Var}
    {Φ Φ' : TransitionForm Clock Var} (hexp : E.PExpansion p Φ Φ')
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hΦ' : Φ'.NonPredicateSatisfies σ P α k) (hinv : Φ.InvariantAt P α k hk) :
    Φ'.InvariantAt P α k hk := by
  have hp : IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩)
      (Φ'.current.resets.apply α) p :=
    hexp.extension.currentInvariant_of_source
      (P.interval ⟨k.1, by omega⟩) α hinv.1 hexp.1
  apply hexp.preservesInvariantAt P α k hk hinv
  · exact hrules.currentBranches (by omega) hΦ' hp
  · intro hnext N' hN'
    exact hrules.nextBranches hnext hΦ' hp hN'

/-- Monotonicity of rule closure. -/
theorem RuleClosedFor.mono {E : ExpansionRules Clock Var}
    {Φ Φ' : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hclosed : E.RuleClosedFor Φ p) (hsub : Φ ⊑ Φ') :
    E.RuleClosedFor Φ' p := by
  refine ⟨hsub.currentLocals hclosed.1, ?_⟩
  rcases hclosed.2 with hn | hbranch
  · exact Or.inl hn
  · right
    obtain ⟨R, hR, Ψ, hΨ, B, hB, hBΦ⟩ := hbranch
    exact ⟨R, hR, Ψ, hΨ, B,
      E.branchTransitionForm_mono hsub.currentResets (by
        apply Set.disjoint_left.2
        intro c hextra hfree
        apply Set.disjoint_left.1 hsub.outerFresh hextra
        refine ⟨Or.inl (Set.mem_iUnion₂.2 ⟨Judgement.predicate p, hclosed.1, ?_⟩), hfree.2⟩
        exact E.branchFreeClocks hR hΨ hfree.1) hB,
      hBΦ.trans hsub⟩

/-- The optional rank contribution of one local judgement. Only unclosed
interval predicates contribute, exactly as in the multiset rank on open predicates. -/
noncomputable def rankEntry (E : ExpansionRules Clock Var)
    (Φ : TransitionForm Clock Var) (J : Judgement Clock Var) : Option ℕ := by
  classical
  cases J with
  | predicate p =>
      exact if E.RuleClosedFor Φ p then none else some p.complexity
  | terminal | clock | leftMarker | next | reset | conj => exact none

/-- The rank is the finite multiset of complexities of the
currently unclosed interval predicates. -/
noncomputable def rank (E : ExpansionRules Clock Var)
    (Φ : TransitionForm Clock Var) : Multiset ℕ :=
  Multiset.filterMap (rankEntry E Φ) Φ.current.locals_finite.toFinset.1

/-- Local judgement occurrences contributing the value `n` to the rank. -/
noncomputable def rankSupport (E : ExpansionRules Clock Var)
    (Φ : TransitionForm Clock Var) (n : ℕ) : Finset (Judgement Clock Var) := by
  classical
  exact Φ.current.locals_finite.toFinset.filter
    (fun J => rankEntry E Φ J = some n)

private theorem count_filterMap_eq_countP [DecidableEq β]
    (f : α → Option β) (s : Multiset α) (b : β) :
    (Multiset.filterMap f s).count b = s.countP (fun a => f a = some b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      cases hfa : f a with
      | none => simp [Multiset.filterMap_cons_none a s hfa, hfa, ih]
      | some c =>
          by_cases hcb : c = b
          · subst c
            simp [Multiset.filterMap_cons_some f a s hfa, hfa, ih]
          · have hbc : b ≠ c := Ne.symm hcb
            simp [Multiset.filterMap_cons_some f a s hfa, hfa, ih, hcb, hbc]

/-- Number of occurrences of one complexity in the rank, expressed as the
cardinality of the corresponding finite set of local judgements. -/
theorem count_rank (E : ExpansionRules Clock Var)
    (Φ : TransitionForm Clock Var) (n : ℕ) :
    (E.rank Φ).count n = (E.rankSupport Φ n).card := by
  classical
  rw [rank, count_filterMap_eq_countP, Multiset.countP_eq_card_filter,
    rankSupport]
  rfl

theorem mem_rank_iff {E : ExpansionRules Clock Var}
    {Φ : TransitionForm Clock Var} {n : ℕ} :
    n ∈ E.rank Φ ↔ ∃ p, Judgement.predicate p ∈ Φ.current.locals ∧
      ¬ E.RuleClosedFor Φ p ∧ p.complexity = n := by
  classical
  rw [rank, Multiset.mem_filterMap]
  constructor
  · rintro ⟨J, hJ, hentry⟩
    have hJ' : J ∈ Φ.current.locals :=
      Φ.current.locals_finite.mem_toFinset.mp hJ
    cases J with
    | predicate p =>
        simp only [rankEntry] at hentry
        split at hentry
        · contradiction
        · simp only [Option.some.injEq] at hentry
          exact ⟨p, hJ', by assumption, hentry⟩
    | terminal | clock | leftMarker | next | reset | conj =>
        simp [rankEntry] at hentry
  · rintro ⟨p, hp, hopen, rfl⟩
    have hp' : Judgement.predicate p ∈ Φ.current.locals_finite.toFinset :=
      Φ.current.locals_finite.mem_toFinset.mpr hp
    refine ⟨Judgement.predicate p, hp', ?_⟩
    simp [rankEntry, hopen]

theorem rank_eq_zero_iff_closed {E : ExpansionRules Clock Var}
    {Φ : TransitionForm Clock Var} : E.rank Φ = 0 ↔ E.IsClosed Φ := by
  constructor
  · intro hrank p hp
    by_contra hopen
    have hmem : p.complexity ∈ E.rank Φ :=
      mem_rank_iff.mpr ⟨p, hp, hopen, rfl⟩
    rw [hrank] at hmem
    simp at hmem
  · intro hclosed
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro n hmem
    obtain ⟨p, hp, hopen, _⟩ := mem_rank_iff.mp hmem
    exact hopen (hclosed p hp)

theorem PExpansion.source_complexity_mem_rank
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ') :
    p.complexity ∈ E.rank Φ :=
  mem_rank_iff.mpr ⟨p, hexp.1, hopen, rfl⟩

theorem PExpansion.target_predicate_closed
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var} (hexp : E.PExpansion p Φ Φ') :
    E.RuleClosedFor Φ' p :=
  hexp.target_ruleClosed

/-- The elementwise core of the multiset rank-decrease argument: every rank contribution
after expansion either already occurred before expansion, or is strictly
smaller than than the removed contribution of `p`. -/
theorem PExpansion.rank_member_classification
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ')
    {n : ℕ} (hn : n ∈ E.rank Φ') :
    n ∈ E.rank Φ ∨ n < p.complexity := by
  obtain ⟨q, hq', hqopen, hqcomp⟩ := mem_rank_iff.mp hn
  by_cases hq : Judgement.predicate q ∈ Φ.current.locals
  · left
    apply mem_rank_iff.mpr
    refine ⟨q, hq, ?_, hqcomp⟩
    intro hqclosed
    exact hqopen (hqclosed.mono hexp.extension)
  · right
    rw [← hqcomp]
    exact hexp.localExpansionShape hopen hq' hq

theorem PExpansion.rankSupport_subset
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hexp : E.PExpansion p Φ Φ') (hopen : ¬ E.RuleClosedFor Φ p)
    {n : ℕ} (hn : p.complexity ≤ n) :
    E.rankSupport Φ' n ⊆ E.rankSupport Φ n := by
  classical
  intro J hJ
  simp only [rankSupport, Finset.mem_filter] at hJ ⊢
  rcases hJ with ⟨hJ', hentry'⟩
  have hJset' : J ∈ Φ'.current.locals :=
    Φ'.current.locals_finite.mem_toFinset.mp hJ'
  cases J with
  | predicate q =>
      have hqopen' : ¬ E.RuleClosedFor Φ' q := by
        intro hclosed
        simp [rankEntry, hclosed] at hentry'
      have hqcomp : q.complexity = n := by
        simp only [rankEntry] at hentry'
        split at hentry'
        · contradiction
        · exact Option.some.inj hentry'
      have hq : Judgement.predicate q ∈ Φ.current.locals := by
        by_contra hq
        have hlt := hexp.localExpansionShape hopen hJset' hq
        omega
      refine ⟨Φ.current.locals_finite.mem_toFinset.mpr hq, ?_⟩
      have hqopen : ¬ E.RuleClosedFor Φ q := by
        intro hclosed
        exact hqopen' (hclosed.mono hexp.extension)
      simp [rankEntry, hqopen, hqcomp]
  | terminal | clock | leftMarker | next | reset | conj =>
      simp [rankEntry] at hentry'

/-- At and above the expanded complexity, no new multiplicity can appear in
the rank. This is the count-sensitive strengthening needed because distinct
predicates may have equal complexity. -/
theorem PExpansion.count_rank_le_of_complexity_le
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ')
    {n : ℕ} (hn : p.complexity ≤ n) :
    (E.rank Φ').count n ≤ (E.rank Φ).count n := by
  classical
  rw [count_rank, count_rank]
  exact Finset.card_le_card (hexp.rankSupport_subset hopen hn)

/-- The occurrence of the expanded predicate makes the count inequality
strict at its own complexity. -/
theorem PExpansion.count_rank_lt_at_complexity
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ') :
    (E.rank Φ').count p.complexity < (E.rank Φ).count p.complexity := by
  classical
  rw [count_rank, count_rank]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hexp.rankSupport_subset hopen (le_refl _), ?_⟩
  intro heq
  have hpSource : Judgement.predicate p ∈ E.rankSupport Φ p.complexity := by
    simp [rankSupport, Φ.current.locals_finite.mem_toFinset, rankEntry,
      hexp.1, hopen]
  have hpTarget : Judgement.predicate p ∉ E.rankSupport Φ' p.complexity := by
    simp [rankSupport, rankEntry, hexp.target_ruleClosed]
  apply hpTarget
  rw [heq]
  exact hpSource

/-- The strict multiset order `≺ᵐ` on predicate ranks. -/
def RankLT (M N : Multiset ℕ) : Prop :=
  Multiset.IsDershowitzMannaLT M N

theorem rankLT_wellFounded : WellFounded RankLT :=
  Multiset.wellFounded_isDershowitzMannaLT

/-- The exact decomposition principle used in the final combinatorial step
of the multiset rank-decrease argument: `Z` contains removed obligations and is nonempty,
while every newly introduced obligation in `Y` is smaller than one of them. -/
theorem rankLT_of_decomposition {M N : Multiset ℕ}
    (h : ∃ X Y Z,
      Z ≠ 0 ∧ M = X + Y ∧ N = X + Z ∧
        ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    RankLT M N :=
  h

/-- A nontrivial expansion replaces the
occurrence belonging to `p` by finitely many strictly smaller occurrences,
possibly removing further occurrences as predicates become rule-closed. -/
theorem PExpansion.rankDecrease
    {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Φ' : TransitionForm Clock Var}
    (hopen : ¬ E.RuleClosedFor Φ p) (hexp : E.PExpansion p Φ Φ') :
    RankLT (E.rank Φ') (E.rank Φ) := by
  classical
  let M := E.rank Φ'
  let N := E.rank Φ
  have hpZ : p.complexity ∈ N - M := by
    rw [← Multiset.count_pos, Multiset.count_sub, Nat.sub_pos_iff_lt]
    exact hexp.count_rank_lt_at_complexity hopen
  apply rankLT_of_decomposition
  refine ⟨M ∩ N, M - N, N - M, ?_, ?_, ?_, ?_⟩
  · intro hzero
    rw [hzero] at hpZ
    simp at hpZ
  · simpa [add_comm] using (Multiset.sub_add_inter M N).symm
  · simpa [add_comm, Multiset.inter_comm] using
      (Multiset.sub_add_inter N M).symm
  · intro y hy
    refine ⟨p.complexity, hpZ, ?_⟩
    by_contra hlt
    have hle : p.complexity ≤ y := Nat.le_of_not_gt hlt
    have hcount := hexp.count_rank_le_of_complexity_le hopen hle
    have hypos : 0 < (M - N).count y := Multiset.count_pos.mpr hy
    rw [Multiset.count_sub, Nat.sub_pos_iff_lt] at hypos
    exact (Nat.not_lt_of_ge hcount hypos)

/-- Definition 4.8: a minimal closed extension of `Φ`.  Minimality
is stated order-theoretically, without choosing an equality test for syntax. -/
structure IsClosure (E : ExpansionRules Clock Var)
    (Φ Φc : TransitionForm Clock Var) : Prop where
  extension : Φ ⊑ Φc
  closed : E.IsClosed Φc
  minimal : ∀ (Θ : TransitionForm Clock Var),
    (Φ ⊑ Θ) → E.IsClosed Θ → (Θ ⊑ Φc) → (Φc ⊑ Θ)

theorem IsClosure.ruleClosedFor {E : ExpansionRules Clock Var}
    {Φ Φc : TransitionForm Clock Var} (h : E.IsClosure Φ Φc)
    {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ Φc.current.locals) :
    E.RuleClosedFor Φc p :=
  h.closed p hp

/-- Every proper intermediate extension below a closure still has an
unclosed current interval predicate. This is the first step of
the finite expansion sequence argument. -/
theorem IsClosure.exists_not_ruleClosed_of_between_ne
    {E : ExpansionRules Clock Var} {Φ Φc Θ : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc) (hΦΘ : Φ ⊑ Θ) (hΘc : Θ ⊑ Φc)
    (hne : Θ ≠ Φc) :
    ∃ p, Judgement.predicate p ∈ Θ.current.locals ∧
      ¬ E.RuleClosedFor Θ p := by
  classical
  have hnclosed : ¬ E.IsClosed Θ := by
    intro hclosed
    have hcΘ : Φc ⊑ Θ := hclosure.minimal Θ hΦΘ hclosed hΘc
    exact hne (hΘc.antisymm hcΘ)
  rw [IsClosed] at hnclosed
  obtain ⟨p, hp⟩ := not_forall.mp hnclosed
  exact ⟨p, Classical.not_imp.mp hp⟩

/-- A minimal rule-closed member of the finite interval between `Θ` and a
fixed upper transition form. -/
structure MinimalRuleClosedBetween (E : ExpansionRules Clock Var)
    (Θ Φc : TransitionForm Clock Var) (p : IntervalPredicate Clock Var) where
  form : TransitionForm Clock Var
  extension : Θ ⊑ form
  ruleClosed : E.RuleClosedFor form p
  upper : form ⊑ Φc
  minimal : ∀ Ξ : TransitionForm Clock Var,
    (Θ ⊑ Ξ) → E.RuleClosedFor Ξ p → (Ξ ⊑ Φc) →
      (Ξ ⊑ form) → (form ⊑ Ξ)

theorem MinimalRuleClosedBetween.pExpansion
    {E : ExpansionRules Clock Var} {Θ Φc : TransitionForm Clock Var}
    {p : IntervalPredicate Clock Var}
    (hmin : E.MinimalRuleClosedBetween Θ Φc p)
    (hp : Judgement.predicate p ∈ Θ.current.locals)
    (hopen : ¬ E.RuleClosedFor Θ p) :
    E.PExpansion p Θ hmin.form := by
  refine ⟨hp, Or.inr ⟨hopen, hmin.extension, hmin.ruleClosed, ?_⟩⟩
  intro Ξ hΘΞ hclosed hΞform
  exact hmin.minimal Ξ hΘΞ hclosed (hΞform.trans hmin.upper) hΞform

/-- A finite sequence of nontrivial single-predicate expansions. The
inductive presentation is equivalent to the list in
the finite expansion sequence argument, while making finiteness structural. -/
inductive ExpansionPath (E : ExpansionRules Clock Var) :
    TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | refl (Φ) : ExpansionPath E Φ Φ
  | step {p : IntervalPredicate Clock Var} {Φ₀ Φ₁ Φ₂}
      (openAtSource : ¬ E.RuleClosedFor Φ₀ p)
      (expansion : E.PExpansion p Φ₀ Φ₁)
      (tail : ExpansionPath E Φ₁ Φ₂) :
      ExpansionPath E Φ₀ Φ₂

/-- Any property preserved by one nontrivial expansion is preserved along a
finite expansion path. This is the induction used by
Corollary C.16. -/
theorem ExpansionPath.preserve
    {E : ExpansionRules Clock Var} {Property : TransitionForm Clock Var → Prop}
    (hstep : ∀ {p : IntervalPredicate Clock Var} {Φ Φ'},
      (¬ E.RuleClosedFor Φ p) → E.PExpansion p Φ Φ' →
        Property Φ → Property Φ')
    {Φ₀ Φ₁ : TransitionForm Clock Var}
    (hpath : E.ExpansionPath Φ₀ Φ₁) (hΦ₀ : Property Φ₀) : Property Φ₁ := by
  induction hpath with
  | refl => exact hΦ₀
  | step hopen hexp _ ih => exact ih (hstep hopen hexp hΦ₀)

/-- Residual invariant preservation along a finite expansion path.
The two hypotheses are precisely the rule-specific current and next branch
obligations needed at each target form. -/
theorem ExpansionPath.preservesInvariantAt
    {E : ExpansionRules Clock Var} {σ : FiniteSignal Var}
    {Φ₀ Φ₁ : TransitionForm Clock Var}
    (hpath : E.ExpansionPath Φ₀ Φ₁) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hk : k.1 < P.size)
    (hcurrent : ∀ {p : IntervalPredicate Clock Var} {Φ Φ'},
      (¬ E.RuleClosedFor Φ p) → E.PExpansion p Φ Φ' →
      E.BranchesPreserve p Φ'
        (IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩)
          (Φ'.current.resets.apply α)))
    (hnextBranches : ∀ {p : IntervalPredicate Clock Var} {Φ Φ'},
      (¬ E.RuleClosedFor Φ p) → E.PExpansion p Φ Φ' →
      ∀ (hnext : k.1 + 1 < P.size) N', Φ'.nextPart = some N' → E.NextBranchesPreserve p Φ'
        (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hnext⟩)
          (N'.resets.apply (ClockResetSet.elapse (Φ'.current.resets.apply α)
            (Judgement.duration P ⟨k.1, by omega⟩)))))
    (hinv : Φ₀.InvariantAt P α k hk) :
    Φ₁.InvariantAt P α k hk := by
  apply hpath.preserve (Property := fun Φ => Φ.InvariantAt P α k hk) ?_ hinv
  intro p Φ Φ' hopen hexp hΦ
  exact hexp.preservesInvariantAt P α k hk hΦ
    (hcurrent hopen hexp) (hnextBranches hopen hexp)

/-- Every form on an expansion sequence is subsumed by its endpoint. -/
theorem ExpansionPath.subsumed {E : ExpansionRules Clock Var}
    {Φ Φ' : TransitionForm Clock Var} (hpath : E.ExpansionPath Φ Φ') : Φ ⊑ Φ' := by
  induction hpath with
  | refl => exact syntacticallySubsumed_refl ∅ _ (by simp)
  | step _ hexp _ ih => exact hexp.extension.trans ih

/-- Guard-only invariant preservation along a complete expansion sequence,
including the last interval of the partition. -/
theorem ExpansionPath.preservesInvariantAt_of_ruleInvariant
    {E : ExpansionRules Clock Var} (hrules : E.PreservesEvaluatedInvariant)
    {σ : FiniteSignal Var} {Φ Φ' : TransitionForm Clock Var}
    (hpath : E.ExpansionPath Φ Φ') (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (hΦ' : Φ'.NonPredicateSatisfies σ P α k) (hinv : Φ.InvariantAt P α k hk) :
    Φ'.InvariantAt P α k hk := by
  induction hpath with
  | refl => exact hinv
  | step _ hexp tail ih =>
      apply ih hΦ'
      exact hexp.preservesInvariantAt_of_ruleInvariant hrules P α k hk
        (transitionForm_nonPredicate_subsumption_sound tail.subsumed hΦ') hinv

/-- One expansion step that remains below a chosen closure. -/
structure ClosureStep (E : ExpansionRules Clock Var)
    (Φc Θ : TransitionForm Clock Var) where
  predicate : IntervalPredicate Clock Var
  target : TransitionForm Clock Var
  openAtSource : ¬ E.RuleClosedFor Θ predicate
  expansion : E.PExpansion predicate Θ target
  upper : target ⊑ Φc

/-- The sole choice principle needed by the sequence construction: every
proper intermediate form admits a nontrivial expansion still below the
closure. -/
def StepsAvailableBelow (E : ExpansionRules Clock Var)
    (Φ Φc : TransitionForm Clock Var) : Prop :=
  ∀ Θ, (Φ ⊑ Θ) → (Θ ⊑ Φc) → Θ ≠ Φc →
    Nonempty (E.ClosureStep Φc Θ)

/-- Existence of the minimal element selected from the finite family
of rule-closed forms between an intermediate form and the closure. -/
def MinimalRuleClosedAvailableBelow (E : ExpansionRules Clock Var)
    (Φc : TransitionForm Clock Var) : Prop :=
  ∀ (Θ : TransitionForm Clock Var) (p : IntervalPredicate Clock Var),
    (Θ ⊑ Φc) → Judgement.predicate p ∈ Θ.current.locals →
      (¬ E.RuleClosedFor Θ p) → Nonempty (E.MinimalRuleClosedBetween Θ Φc p)

/-- Finiteness gives a rule-closed form below `Φc` of minimum component count.
Under subsumption, equal component counts imply equality of the forms.
The chosen form is therefore minimal under subsumption. -/
theorem IsClosed.minimalRuleClosedAvailableBelow
    {E : ExpansionRules Clock Var} {Φc : TransitionForm Clock Var}
    (hclosedc : E.IsClosed Φc) : E.MinimalRuleClosedAvailableBelow Φc := by
  intro Θ p hΘc hp hopen
  let Candidate : TransitionForm Clock Var → Prop := fun Ξ =>
    (Θ ⊑ Ξ) ∧ E.RuleClosedFor Ξ p ∧ (Ξ ⊑ Φc)
  have hpΦc : Judgement.predicate p ∈ Φc.current.locals := hΘc.currentLocals hp
  have hnonempty : ∃ Ξ, Candidate Ξ := by
    refine ⟨Φc, hΘc, hclosedc p hpΦc, ?_⟩
    exact syntacticallySubsumed_refl (∅ : Set Clock) Φc
      (by intro c hc; exact hc.elim)
  obtain ⟨Φmin, hmin⟩ :=
    exists_minimalFor_of_wellFoundedLT Candidate
      TransitionForm.componentCount hnonempty
  refine ⟨
    { form := Φmin
      extension := hmin.1.1
      ruleClosed := hmin.1.2.1
      upper := hmin.1.2.2
      minimal := ?_ }⟩
  intro Ξ hΘΞ hclosedΞ hΞc hΞmin
  have hΞCount : Ξ.componentCount ≤ Φmin.componentCount :=
    hΞmin.componentCount_le
  have hminCount : Φmin.componentCount ≤ Ξ.componentCount :=
    hmin.2 ⟨hΘΞ, hclosedΞ, hΞc⟩ hΞCount
  have heq : Ξ = Φmin :=
    hΞmin.eq_of_componentCount_eq (Nat.le_antisymm hΞCount hminCount)
  subst Ξ
  exact hΞmin

theorem IsClosure.stepsAvailable_of_minimalRuleClosedAvailable
    {E : ExpansionRules Clock Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc)
    (hminimal : E.MinimalRuleClosedAvailableBelow Φc) :
    E.StepsAvailableBelow Φ Φc := by
  intro Θ hΦΘ hΘc hne
  obtain ⟨p, hp, hopen⟩ :=
    hclosure.exists_not_ruleClosed_of_between_ne hΦΘ hΘc hne
  obtain ⟨hmin⟩ := hminimal Θ p hΘc hp hopen
  exact ⟨
    { predicate := p
      target := hmin.form
      openAtSource := hopen
      expansion := hmin.pExpansion hp hopen
      upper := hmin.upper }⟩

/-- The well-founded-recursion part of
the finite expansion sequence argument. Once the finite interval supplies a next
minimal expansion, strict rank decrease forces the path to be finite. -/
theorem IsClosure.expansionPath_of_stepsAvailable
    {E : ExpansionRules Clock Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc) (hsteps : E.StepsAvailableBelow Φ Φc) :
    E.ExpansionPath Φ Φc := by
  let R : TransitionForm Clock Var → TransitionForm Clock Var → Prop :=
    fun Θ₁ Θ₀ => RankLT (E.rank Θ₁) (E.rank Θ₀)
  have hR : WellFounded R := rankLT_wellFounded.onFun
  have aux : ∀ Θ, (Φ ⊑ Θ) → (Θ ⊑ Φc) → E.ExpansionPath Θ Φc := by
    intro Θ
    induction Θ using hR.induction with
    | h Θ ih =>
        intro hΦΘ hΘc
        by_cases heq : Θ = Φc
        · subst Θ
          exact ExpansionPath.refl Φc
        · obtain ⟨s⟩ := hsteps Θ hΦΘ hΘc heq
          apply ExpansionPath.step s.openAtSource s.expansion
          apply ih s.target
          · exact s.expansion.rankDecrease s.openAtSource
          · exact hΦΘ.trans s.expansion.extension
          · exact s.upper
  exact aux Φ
    (syntacticallySubsumed_refl (∅ : Set Clock) Φ (by intro c hc; exact hc.elim))
    hclosure.extension

/-- The finite expansion sequence argument uses minimal elements of
the componentwise interval below the closure. -/
theorem IsClosure.expansionPath_of_minimalRuleClosedAvailable
    {E : ExpansionRules Clock Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc)
    (hminimal : E.MinimalRuleClosedAvailableBelow Φc) :
    E.ExpansionPath Φ Φc :=
  hclosure.expansionPath_of_stepsAvailable
    (hclosure.stepsAvailable_of_minimalRuleClosedAvailable hminimal)

/-- Every closure admits a finite expansion sequence. -/
theorem IsClosure.expansionPath
    {E : ExpansionRules Clock Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc) : E.ExpansionPath Φ Φc :=
  hclosure.expansionPath_of_minimalRuleClosedAvailable
    hclosure.closed.minimalRuleClosedAvailableBelow

/-- Residual form of Corollary C.16 under the current and next branch
invariant conditions. -/
theorem IsClosure.preservesInvariantAt
    {E : ExpansionRules Clock Var} {σ : FiniteSignal Var}
    {Φ Φc : TransitionForm Clock Var} (hclosure : E.IsClosure Φ Φc)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hcurrent : ∀ {p : IntervalPredicate Clock Var} {Θ Θ'},
      (¬ E.RuleClosedFor Θ p) → E.PExpansion p Θ Θ' →
      E.BranchesPreserve p Θ'
        (IntervalPredicate.Invariant (P.interval ⟨k.1, by omega⟩)
          (Θ'.current.resets.apply α)))
    (hnextBranches : ∀ {p : IntervalPredicate Clock Var} {Θ Θ'},
      (¬ E.RuleClosedFor Θ p) → E.PExpansion p Θ Θ' →
      ∀ (hnext : k.1 + 1 < P.size) N', Θ'.nextPart = some N' → E.NextBranchesPreserve p Θ'
        (IntervalPredicate.Invariant (P.interval ⟨k.1 + 1, hnext⟩)
          (N'.resets.apply (ClockResetSet.elapse (Θ'.current.resets.apply α)
            (Judgement.duration P ⟨k.1, by omega⟩)))))
    (hinv : Φ.InvariantAt P α k hk) :
    Φc.InvariantAt P α k hk :=
  hclosure.expansionPath.preservesInvariantAt P α k hk hcurrent
    hnextBranches hinv

/-- Residual closure invariant from the non-predicate branch conditions. -/
theorem IsClosure.preservesInvariantAt_of_ruleInvariant
    {E : ExpansionRules Clock Var} (hrules : E.PreservesEvaluatedInvariant)
    {σ : FiniteSignal Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : E.IsClosure Φ Φc) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (hΦc : Φc.NonPredicateSatisfies σ P α k) (hinv : Φ.InvariantAt P α k hk) :
    Φc.InvariantAt P α k hk :=
  hclosure.expansionPath.preservesInvariantAt_of_ruleInvariant hrules P α k hk hΦc hinv

end ExpansionRules

end STLTableau
