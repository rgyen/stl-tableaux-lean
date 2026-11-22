/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.Closure

/-! # Expansion rules and branch transition forms

This file registers exactly the unclocked and clocked rule families defined in
`Expansion.lean` and `ClockedExpansion.lean`. `ConcreteRule` records the
expansion rules. `BranchTransitionForms` states the properties required of
their transition-form representatives after reset combination and alpha-conversion.
-/

namespace STLTableau

open scoped STL

namespace StateForm

/-- Empty state form, used as the neutral current component of a normalized
`next` judgement. -/
def empty {Clock Var : Type*} : StateForm Clock Var where
  constraints := ∅
  constraints_finite := Set.finite_empty
  resets := ClockResetSet.empty
  locals := ∅
  locals_finite := Set.finite_empty
  locals_are_local := by simp

/-- State form containing one local judgement. -/
def ofLocal {Clock Var : Type*} (J : Judgement Clock Var) (hJ : J.IsLocal) :
    StateForm Clock Var where
  constraints := ∅
  constraints_finite := Set.finite_empty
  resets := ClockResetSet.empty
  locals := {J}
  locals_finite := Set.finite_singleton J
  locals_are_local := by simpa

/-- State form containing one clock constraint. -/
def ofClock {Clock Var : Type*} (c : Clock) (r : ClockRelation) (a : NNReal) :
    StateForm Clock Var where
  constraints := {⟨c, r, a⟩}
  constraints_finite := Set.finite_singleton _
  resets := ClockResetSet.empty
  locals := ∅
  locals_finite := Set.finite_empty
  locals_are_local := by simp

@[simp] theorem satisfies_empty {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (empty : StateForm Clock Var).Satisfies σ P α k := by
  simp [empty, StateForm.Satisfies]

@[simp] theorem satisfies_ofLocal {Clock Var : Type*}
    (J : Judgement Clock Var) (hJ : J.IsLocal)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (ofLocal J hJ).Satisfies σ P α k ↔ Judgement.Satisfies σ P α k J := by
  simp [ofLocal, StateForm.Satisfies]

@[simp] theorem satisfies_ofClock {Clock Var : Type*}
    (c : Clock) (r : ClockRelation) (a : NNReal)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (ofClock c r a : StateForm Clock Var).Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k (.clock c r a) := by
  simp [ofClock, StateForm.Satisfies, ClockConstraint.Satisfies,
    Judgement.Satisfies]

/-- Recursive invariant evaluation of one local atom yields the direct-member
state invariant used by the closure layer. -/
theorem invariant_ofLocal {Clock Var : Type*}
    (J : Judgement Clock Var) (hJ : J.IsLocal)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hk : k.1 < P.size)
    (h : Judgement.EvaluatedInvariant σ P α k J) :
    Judgement.SetInvariant (P.interval ⟨k.1, hk⟩) α
      (ofLocal J hJ).locals := by
  apply Judgement.setInvariant_of_evaluated σ P α k hk
  intro Ψ hΨ
  have hEq : Ψ = J := by simpa [ofLocal] using hΨ
  subst Ψ
  exact h

end StateForm

namespace TransitionForm

/-- Transition form consisting only of a next state. -/
def ofNextState {Clock Var : Type*} (S : StateForm Clock Var) :
    TransitionForm Clock Var :=
  { current := StateForm.empty, nextPart := some S }

/-- Add a reset surrounding an already normalized transition form. The reset is
placed before the form's existing current resets, matching nested reset
evaluation. Semantic correctness later requires their consistency. -/
def prependReset {Clock Var : Type*} (Λ : ClockResetSet Clock)
    (Φ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  { current :=
      { constraints := Φ.current.constraints
        constraints_finite := Φ.current.constraints_finite
        resets := Λ.union Φ.current.resets
        locals := Φ.current.locals
        locals_finite := Φ.current.locals_finite
        locals_are_local := Φ.current.locals_are_local }
    nextPart := Φ.nextPart }

@[simp] theorem nextPart_prependReset {Clock Var : Type*}
    (Λ : ClockResetSet Clock) (Φ : TransitionForm Clock Var) :
    (prependReset Λ Φ).nextPart = Φ.nextPart := rfl

@[simp] theorem current_prependReset {Clock Var : Type*}
    (Λ : ClockResetSet Clock) (Φ : TransitionForm Clock Var) :
    (prependReset Λ Φ).current.resets = Λ.union Φ.current.resets := rfl

/-- Structural transition-form transition-form normalization for the judgement grammar. It returns
`none` exactly when a nested `next` prevents the result from having the
single optional-next shape. Reset consistency and alpha-renaming are
separate correctness obligations of `BranchTransitionForms`. -/
def toTransitionForm? {Clock Var : Type*} :
    Judgement Clock Var → Option (TransitionForm Clock Var)
  | .terminal => some (ofState (StateForm.ofLocal .terminal trivial))
  | .clock c r a => some (ofState (StateForm.ofClock c r a))
  | .leftMarker m => some (ofState (StateForm.ofLocal (.leftMarker m) trivial))
  | .predicate p => some (ofState (StateForm.ofLocal (.predicate p) trivial))
  | .reset Λ Ψ => (toTransitionForm? Ψ).map (prependReset Λ)
  | .conj Ψ₁ Ψ₂ => do
      let Φ₁ ← toTransitionForm? Ψ₁
      let Φ₂ ← toTransitionForm? Ψ₂
      pure (Φ₁.union Φ₂)
  | .next Ψ => do
      let Φ ← toTransitionForm? Ψ
      match Φ.nextPart with
      | none => pure (ofNextState Φ.current)
      | some _ => none

@[simp] theorem toTransitionForm_terminal {Clock Var : Type*} :
    toTransitionForm? (.terminal : Judgement Clock Var) =
      some (ofState (StateForm.ofLocal .terminal trivial)) := rfl

@[simp] theorem toTransitionForm_clock {Clock Var : Type*}
    (c : Clock) (r : ClockRelation) (a : NNReal) :
    toTransitionForm? (.clock c r a : Judgement Clock Var) =
      some (ofState (StateForm.ofClock c r a)) := rfl

@[simp] theorem toTransitionForm_leftMarker {Clock Var : Type*} (m : Marker) :
    toTransitionForm? (.leftMarker m : Judgement Clock Var) =
      some (ofState (StateForm.ofLocal (.leftMarker m) trivial)) := rfl

@[simp] theorem toTransitionForm_predicate {Clock Var : Type*}
    (p : IntervalPredicate Clock Var) :
    toTransitionForm? (.predicate p) =
      some (ofState (StateForm.ofLocal (.predicate p) trivial)) := rfl

/-- Semantic correctness of normalization for every atomic local judgement. -/
theorem toTransitionForm_local_satisfies_iff {Clock Var : Type*}
    (J : Judgement Clock Var) (hJ : J.IsLocal)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (ofState (StateForm.ofLocal J hJ)).Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k J := by
  rw [satisfies_ofState]
  exact StateForm.satisfies_ofLocal J hJ σ P α k

/-- Semantic correctness of normalization for a clock constraint. -/
theorem toTransitionForm_clock_satisfies_iff {Clock Var : Type*}
    (c : Clock) (r : ClockRelation) (a : NNReal)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (ofState (StateForm.ofClock c r a)).Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k (.clock c r a) := by
  rw [satisfies_ofState]
  exact StateForm.satisfies_ofClock c r a σ P α k

/-- A normalized state under `next` has exactly the judgement-level next
semantics, including rejection at the terminal position. -/
theorem satisfies_ofNextState_iff {Clock Var : Type*}
    (S : StateForm Clock Var) (Ψ : Judgement Clock Var)
    (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hS : ∀ (β : ClockValuation Clock) (j : Judgement.Position P),
      S.Satisfies σ P β j ↔ Judgement.Satisfies σ P β j Ψ) :
    (ofNextState S).Satisfies σ P α k ↔
      Judgement.Satisfies σ P α k (.next Ψ) := by
  by_cases hk : k.1 < P.size
  · simp [ofNextState, TransitionForm.Satisfies, StateForm.empty,
      Judgement.Satisfies, hk, hS]
  · simp [ofNextState, TransitionForm.Satisfies, StateForm.empty,
      Judgement.Satisfies, hk]

@[simp] theorem toTransitionForm_reset {Clock Var : Type*} (Λ : ClockResetSet Clock)
    (Ψ : Judgement Clock Var) :
    toTransitionForm? (.reset Λ Ψ) = (toTransitionForm? Ψ).map (prependReset Λ) := rfl

@[simp] theorem toTransitionForm_conj {Clock Var : Type*} (Ψ₁ Ψ₂ : Judgement Clock Var) :
    toTransitionForm? (.conj Ψ₁ Ψ₂) = (do
      let Φ₁ ← toTransitionForm? Ψ₁
      let Φ₂ ← toTransitionForm? Ψ₂
      pure (Φ₁.union Φ₂)) := rfl

end TransitionForm

/-- The properties of branch transition forms used in `app:expansion-branch-clocks`.
`relation Λ Ψ B` means that `B` represents `Λ.Ψ` in transition form.
The structural operation `toTransitionForm?` alone does not establish these
properties: reset scope, free clocks, and alpha-conversion still require proofs. -/
structure BranchTransitionForms (Clock Var : Type*) where
  relation : ClockResetSet Clock → Judgement Clock Var →
    TransitionForm Clock Var → Prop
  mono : ∀ {Λ₁ Λ₂ Ψ B}, Λ₁.Subset Λ₂ →
    Disjoint (Λ₂.clocks \ Λ₁.clocks) (Ψ.freeClocks \ Λ₁.clocks) →
    relation Λ₁ Ψ B → relation Λ₂ Ψ B
  currentPredicate_mem : ∀ {Λ Ψ B q}, relation Λ Ψ B →
    Judgement.predicate q ∈ B.current.locals → q ∈ Ψ.currentPredicates
  satisfies_iff : ∀ {Ψ Λ B}, relation Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      B.Satisfies σ P α k ↔ Judgement.Satisfies σ P (Λ.apply α) k Ψ
  nonPredicateSatisfies_iff : ∀ {Ψ Λ B}, relation Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      B.NonPredicateSatisfies σ P α k ↔ Judgement.NonPredicateSatisfies σ P (Λ.apply α) k Ψ
  currentInvariant : ∀ {Ψ Λ B}, relation Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P)
      (hk : k.1 < P.size),
      Judgement.EvaluatedInvariant σ P (Λ.apply α) k Ψ →
      Judgement.SetInvariant (P.interval ⟨k.1, hk⟩)
        (B.current.resets.apply α) B.current.locals
  nextInvariant : ∀ {Ψ Λ B}, relation Λ Ψ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P)
      (hnext : k.1 + 1 < P.size) (N : StateForm Clock Var),
      B.nextPart = some N →
      Judgement.EvaluatedInvariant σ P (Λ.apply α) k Ψ →
      Judgement.SetInvariant (P.interval ⟨k.1 + 1, hnext⟩)
        (N.resets.apply (ClockResetSet.elapse (B.current.resets.apply α)
          (Judgement.duration P ⟨k.1, by omega⟩))) N.locals

/-- Instances of the expansion rules in Figures 10 and 11 with bounded
timing intervals. Constructors record distinct clocks where required. -/
inductive ConcreteRule {Clock Var : Type*} [DecidableEq Clock] :
    IntervalPredicate Clock Var → ExpansionRule Clock Var → Prop
  | plainAnd (φ ψ : Formula Var) :
      ConcreteRule (.plain (φ ∧ₛ ψ)) (ExpansionRule.plainAnd φ ψ)
  | plainOr (φ ψ : Formula Var) :
      ConcreteRule (.plain (Formula.or φ ψ)) (ExpansionRule.plainOr φ ψ)
  | plainUntil (φ ψ : Formula Var) :
      ConcreteRule (.plain (Formula.untimedUntil φ ψ))
        (ExpansionRule.plainUntil φ ψ)
  | plainRelease (φ ψ : Formula Var) :
      ConcreteRule (.plain (Formula.release (.unbounded 0) φ ψ))
        (ExpansionRule.plainRelease φ ψ)
  | openEventually (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
      ConcreteRule (.plain (◇[(I : TimeInterval)] φ))
        (ExpansionRule.openEventually c I φ)
  | openAlways (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var) :
      ConcreteRule (.plain (□[(I : TimeInterval)] φ))
        (ExpansionRule.openAlways c I φ)
  | upperAlways (c d : Clock) (b : Marker) (I : BoundedTimeInterval)
      (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.upper c b .always I φ)
        (ExpansionRule.upperAlways c d b I φ)
  | boundedAlways (c d : Clock) (b q : Marker) (I : BoundedTimeInterval)
      (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.bounded c d b q .always I φ)
        (ExpansionRule.boundedAlways c d b q I φ)
  | upperEventually (c d : Clock) (b : Marker) (I : BoundedTimeInterval)
      (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.upper c b .eventually I φ)
        (ExpansionRule.upperEventually c d b I φ)
  | boundedEventually (c d : Clock) (b q : Marker) (I : BoundedTimeInterval)
      (φ : Formula Var) (hcd : c ≠ d) :
      ConcreteRule (.bounded c d b q .eventually I φ)
        (ExpansionRule.boundedEventually c d b q I φ)

namespace ConcreteRule

variable {Clock Var : Type*} [DecidableEq Clock]

theorem source_eq
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) : R.source = p := by
  cases hrule <;> rfl

/-- A branch has no free clocks other than those of its source predicate;
clocks introduced by a rule are reset-bound. -/
theorem branchFreeClocks
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {B : Judgement Clock Var}
    (hB : B ∈ R.branches) : B.freeClocks ⊆ p.clockSet := by
  classical
  cases hrule <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr,
      ExpansionRule.plainUntil, ExpansionRule.plainRelease,
      ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways,
      ExpansionRule.upperEventually, ExpansionRule.boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish,
      Judgement.freeClocks, Judgement.predicateClocks, IntervalPredicate.clockSet,
      ClockResetSet.clocks_union, Judgement.markedLT, Judgement.markedGT] <;>
    (try split) <;> simp_all [Judgement.freeClocks,
      Set.subset_def] <;> aesop

/-- Every branch of every registered expansion rule has a transition
form, as asserted after the successive-expansion construction in the manuscript. -/
theorem branch_has_transitionForm
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {B : Judgement Clock Var}
    (hB : B ∈ R.branches) : ∃ Φ, TransitionForm.toTransitionForm? B = some Φ := by
  cases hrule with
  | plainAnd => simp_all [ExpansionRule.plainAnd, TransitionForm.toTransitionForm?]
  | plainOr =>
      simp only [ExpansionRule.plainOr, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl <;> simp [TransitionForm.toTransitionForm?]
  | plainUntil =>
      simp only [ExpansionRule.plainUntil, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl <;> simp [TransitionForm.toTransitionForm?, TransitionForm.ofState]
  | plainRelease =>
      simp only [ExpansionRule.plainRelease, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl | rfl <;>
        simp [TransitionForm.toTransitionForm?, TransitionForm.ofState]
  | openEventually =>
      simp only [ExpansionRule.openEventually, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl <;> simp [TransitionForm.toTransitionForm?]
  | openAlways =>
      simp only [ExpansionRule.openAlways, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl <;> simp [TransitionForm.toTransitionForm?]
  | upperAlways c d b I φ hcd =>
      simp only [ExpansionRule.upperAlways, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
        cases b <;>
        simp [ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
          Judgement.markedLT, Judgement.markedGT, TransitionForm.toTransitionForm?,
          Marker.imp, Marker.conj, Marker.complement,
          TransitionForm.unionNext, TransitionForm.ofState]
  | boundedAlways c d b q I φ hcd =>
      simp only [ExpansionRule.boundedAlways, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        cases b <;> cases q <;>
        simp [ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
          ExpansionRule.boundedAlways_finish, TransitionForm.toTransitionForm?,
          Judgement.markedLT, Judgement.markedGT, TransitionForm.unionNext,
          Marker.imp, Marker.conj, Marker.notConj, Marker.complement,
          TransitionForm.ofState]
  | upperEventually c d b I φ hcd =>
      classical
      by_cases hz : I.lower = 0
      · simp only [ExpansionRule.upperEventually, hz, if_pos, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hB
        rcases hB with hdefer | hplain
        · rcases hdefer with rfl | rfl <;> cases b <;>
            simp [ExpansionRule.upperEventually_defer, Judgement.markedLT,
              Marker.imp, Marker.complement, TransitionForm.toTransitionForm?,
              TransitionForm.unionNext, TransitionForm.ofState]
        · subst B
          simp [TransitionForm.toTransitionForm?]
      · simp only [ExpansionRule.upperEventually, hz, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hB
        rcases hB with hdefer | hcheck
        · rcases hdefer with rfl | rfl <;> cases b <;>
            simp [ExpansionRule.upperEventually_defer, Judgement.markedLT,
              Marker.imp, Marker.complement, TransitionForm.toTransitionForm?,
              TransitionForm.unionNext, TransitionForm.ofState]
        · have hcheck' : B = ExpansionRule.upperEventually_check c d b ○ I φ ∨
              B = ExpansionRule.upperEventually_check c d b ● I φ := by
            simpa only [if_false, List.mem_cons, List.not_mem_nil, or_false] using hcheck
          rcases hcheck' with rfl | rfl <;> cases b <;>
            simp [ExpansionRule.upperEventually_check, Judgement.markedGT,
              Marker.conj, Marker.complement, TransitionForm.toTransitionForm?,
              TransitionForm.unionNext, TransitionForm.ofState]
  | boundedEventually c d b q I φ hcd =>
      simp only [ExpansionRule.boundedEventually, List.mem_cons, List.not_mem_nil,
        or_false] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
        cases b <;> cases q <;>
        simp [ExpansionRule.boundedEventually_defer,
          ExpansionRule.boundedEventually_check,
          ExpansionRule.boundedEventually_finish, TransitionForm.toTransitionForm?,
          Judgement.markedLT, Judgement.markedGT, TransitionForm.unionNext,
          Marker.imp, Marker.conj, Marker.notConj, Marker.complement,
          TransitionForm.ofState]

/-- Every registered rule strictly reduces the complexity of current
predicates occurring in its branches. -/
theorem complexityReduced
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) : R.ComplexityReduced := by
  cases hrule with
  | plainAnd φ ψ => exact ExpansionRule.plainAnd_complexityReduced φ ψ
  | plainOr φ ψ => exact ExpansionRule.plainOr_complexityReduced φ ψ
  | plainUntil φ ψ => exact ExpansionRule.plainUntil_complexityReduced φ ψ
  | plainRelease φ ψ => exact ExpansionRule.plainRelease_complexityReduced φ ψ
  | openEventually c I φ =>
      exact ExpansionRule.openEventually_complexityReduced c I φ
  | openAlways c I φ => exact ExpansionRule.openAlways_complexityReduced c I φ
  | upperAlways c d b I φ _ =>
      exact ExpansionRule.upperAlways_complexityReduced c d b I φ
  | boundedAlways c d b q I φ _ =>
      exact ExpansionRule.boundedAlways_complexityReduced c d b q I φ
  | upperEventually c d b I φ _ =>
      exact ExpansionRule.upperEventually_complexityReduced c d b I φ
  | boundedEventually c d b q I φ _ =>
      exact ExpansionRule.boundedEventually_complexityReduced c d b q I φ

/-- Preservation of the residual invariant when the branch's non-predicate
conditions hold. Used in the proof of Proposition 3.14. -/
theorem preservesEvaluatedInvariant
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {B : Judgement Clock Var}
    (hB : B ∈ R.branches) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (β : ClockValuation Clock)
    (k : Judgement.Position P)
    (hinv : ∀ hk : k.1 < P.size,
      IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) β p)
    (hsat : Judgement.NonPredicateSatisfies σ P β k B) :
    Judgement.EvaluatedInvariant σ P β k B := by
  cases hrule with
  | plainAnd φ ψ =>
      exact ExpansionRule.plainAnd_preserves_evaluatedInvariant
        φ ψ σ P β k B hB hsat
  | plainOr φ ψ =>
      exact ExpansionRule.plainOr_preserves_evaluatedInvariant
        φ ψ σ P β k B hB hsat
  | plainUntil φ ψ =>
      exact ExpansionRule.plainUntil_preserves_evaluatedInvariant
        φ ψ σ P β k B hB hsat
  | plainRelease φ ψ =>
      exact ExpansionRule.plainRelease_preserves_evaluatedInvariant
        φ ψ σ P β k B hB hsat
  | openEventually c I φ =>
      exact ExpansionRule.openEventually_preserves_evaluatedInvariant
        c I φ σ P β k B hB hsat
  | openAlways c I φ =>
      exact ExpansionRule.openAlways_preserves_evaluatedInvariant
        c I φ σ P β k B hB hsat
  | upperAlways c d b I φ hcd =>
      exact ExpansionRule.upperAlways_preserves_evaluatedInvariant
        c d b I φ hcd σ P β k B hB hsat
  | boundedAlways c d b q I φ hcd =>
      exact ExpansionRule.boundedAlways_preserves_evaluatedInvariant
        c d b q I φ hcd σ P β k hinv B hB hsat
  | upperEventually c d b I φ hcd =>
      exact ExpansionRule.upperEventually_preserves_evaluatedInvariant
        c d b I φ hcd σ P β k hinv B hB hsat
  | boundedEventually c d b q I φ hcd =>
      exact ExpansionRule.boundedEventually_preserves_evaluatedInvariant
        c d b q I φ hcd σ P β k hinv B hB hsat

/-- Any expansion-rule family whose rule field is exactly `ConcreteRule`
discharges the uniform rule-invariant obligation used by closure expansion. -/
theorem expansionRules_preservesEvaluatedInvariant
    (E : ExpansionRules Clock Var)
    (hrule : ∀ p R, E.rule p R ↔ ConcreteRule p R) :
    E.PreservesEvaluatedInvariant := by
  intro p R B hR hB σ P β k hinv hsat
  exact preservesEvaluatedInvariant (hrule p R |>.1 hR) hB
    σ P β k hinv hsat

end ConcreteRule

namespace BranchTransitionForms

variable {Clock Var : Type*} [DecidableEq Clock]

/-- Assemble the expansion rules from an implementation of
the alpha-converting transition-form representation interface. -/
def expansionRules (A : BranchTransitionForms Clock Var) : ExpansionRules Clock Var where
  rule := ConcreteRule
  branchTransitionForm := A.relation
  branchTransitionForm_mono := A.mono
  branchFreeClocks := by
    intro p R Ψ hR hΨ
    exact ConcreteRule.branchFreeClocks hR hΨ
  branchTransitionForm_reduced := by
    intro p R Ψ Λ B q hR hΨ hB hq
    have hlt := ConcreteRule.complexityReduced hR Ψ hΨ q
      (A.currentPredicate_mem hB hq)
    simpa [ConcreteRule.source_eq hR] using hlt
  branchTransitionForm_satisfies_iff := A.satisfies_iff
  branchTransitionForm_nonPredicateSatisfies_iff := A.nonPredicateSatisfies_iff
  branchTransitionForm_currentInvariant := A.currentInvariant
  branchTransitionForm_nextInvariant := A.nextInvariant

@[simp] theorem expansionRules_rule_iff (A : BranchTransitionForms Clock Var)
    (p : IntervalPredicate Clock Var) (R : ExpansionRule Clock Var) :
    (A.expansionRules.rule p R ↔ ConcreteRule p R) := Iff.rfl

/-- The assembled expansion rules satisfies the uniform rule-invariant
property required by `PExpansion.preservesInvariantAt_of_ruleInvariant`. -/
theorem expansionRules_preservesEvaluatedInvariant (A : BranchTransitionForms Clock Var) :
    A.expansionRules.PreservesEvaluatedInvariant :=
  ConcreteRule.expansionRules_preservesEvaluatedInvariant A.expansionRules
    (fun _ _ => Iff.rfl)

/-- One-step form of Proposition 4.16. Once branch
transition-form representatives are supplied, no rule-by-rule or branch-preservation
hypotheses remain at the call site. -/
theorem expansion_preservesInvariantAt
    (A : BranchTransitionForms Clock Var)
    {p : IntervalPredicate Clock Var} {σ : FiniteSignal Var}
    {Φ Φ' : TransitionForm Clock Var} (hexp : A.expansionRules.PExpansion p Φ Φ')
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hΦ' : Φ'.NonPredicateSatisfies σ P α k) (hinv : Φ.InvariantAt P α k hk) :
    Φ'.InvariantAt P α k hk :=
  hexp.preservesInvariantAt_of_ruleInvariant
    A.expansionRules_preservesEvaluatedInvariant P α k hk hΦ' hinv

/-- The closure invariant from guard, marker, and terminal satisfaction alone. -/
theorem closure_preservesInvariantAt
    (A : BranchTransitionForms Clock Var)
    {σ : FiniteSignal Var} {Φ Φc : TransitionForm Clock Var}
    (hclosure : A.expansionRules.IsClosure Φ Φc) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (hΦc : Φc.NonPredicateSatisfies σ P α k) (hinv : Φ.InvariantAt P α k hk) :
    Φc.InvariantAt P α k hk :=
  hclosure.preservesInvariantAt_of_ruleInvariant
    A.expansionRules_preservesEvaluatedInvariant P α k hk hΦc hinv

end BranchTransitionForms

end STLTableau
