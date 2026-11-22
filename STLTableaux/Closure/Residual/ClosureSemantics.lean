/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.BranchExtension

/-! # Semantic closure obligations -/
namespace STLTableau
open scoped STL
namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock]

/-- Uniform branch soundness, retaining the source-invariant obligation.
No stability assumption is needed in this direction. -/
theorem branch_sound {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : ConcreteRule p R) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, IntervalPredicate.Invariant (P.interval ⟨k.1, hk⟩) α p)
    (hs : R.BranchSatisfied σ P α k) : Judgement.Satisfies σ P α k (.predicate p) := by
  cases hr with
  | plainAnd φ ψ => exact (ExpansionRule.plainAnd_correct_at φ ψ σ P α k).2 hs
  | plainOr φ ψ => exact ExpansionRule.plainOr_sound_at φ ψ σ P α k hs
  | plainUntil φ ψ => exact ExpansionRule.plainUntil_sound_at φ ψ σ P α k hs
  | plainRelease φ ψ => exact ExpansionRule.plainRelease_sound_at φ ψ σ P α k hs
  | openEventually c I φ => exact (ExpansionRule.openEventually_correct_at c I φ σ P α k).2 hs
  | openAlways c I φ => exact (ExpansionRule.openAlways_correct_at c I φ σ P α k).2 hs
  | upperAlways c d b I φ hcd =>
      exact ExpansionRule.upperAlways_sound_at c d b I φ hcd σ P α k hs
  | boundedAlways c d b q I φ hcd =>
      exact ExpansionRule.boundedAlways_sound_at c d b q I φ hcd σ P α k hs
  | upperEventually c d b I φ hcd =>
      exact ExpansionRule.upperEventually_sound_at c d b I φ hcd σ P α k hi hs
  | boundedEventually c d b q I φ hcd =>
      exact ExpansionRule.boundedEventually_sound_at c d b q I φ hcd σ P α k hi hs
end ConcreteRule

namespace Judgement
variable {Clock Var : Type*}

theorem nonPredicateSatisfies_of_satisfies {σ : FiniteSignal Var}
    {P : IntervalPartition σ.domain} {α : ClockValuation Clock} {k : Position P}
    {J : Judgement Clock Var} (h : Satisfies σ P α k J) :
    NonPredicateSatisfies σ P α k J := by
  induction J generalizing α k with
  | predicate p => trivial
  | conj J K ihJ ihK => exact ⟨ihJ h.1, ihK h.2⟩
  | reset Λ J ih => exact ih h
  | next J ih =>
      simp only [Satisfies, NonPredicateSatisfies] at h ⊢
      by_cases ht : k.1 < P.size
      · simp only [dif_pos ht] at h ⊢
        exact ih h
      · simp only [dif_neg ht] at h ⊢
  | _ => exact h
end Judgement

namespace StateForm
variable {Clock Var : Type*}
theorem nonPredicateSatisfies_of_satisfies {σ : FiniteSignal Var}
    {P : IntervalPartition σ.domain} {α : ClockValuation Clock}
    {k : Judgement.Position P} {S : StateForm Clock Var} (h : S.Satisfies σ P α k) :
    S.NonPredicateSatisfies σ P α k :=
  ⟨h.1, fun J hJ => Judgement.nonPredicateSatisfies_of_satisfies (h.2 J hJ)⟩
end StateForm

namespace TransitionForm
variable {Clock Var : Type*}

/-- Retain selected current locals; current guards/resets and the whole next
component remain in their original scopes. -/
def restrictCurrent (Φ : TransitionForm Clock Var) (Q : Judgement Clock Var → Prop) :
    TransitionForm Clock Var :=
  { Φ with current := { Φ.current with
      locals := {J ∈ Φ.current.locals | Q J}
      locals_finite := Φ.current.locals_finite.subset (fun _ h => h.1)
      locals_are_local := fun J h => Φ.current.locals_are_local J h.1 } }

def KeepAtomic : Judgement Clock Var → Prop
  | .predicate p => p.IsAtomic
  | _ => True

/-- Remove non-atomic predicates from the current part of a transition form. -/
def atomicProjection (Φ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  Φ.restrictCurrent KeepAtomic

theorem restrictCurrent_satisfies_of (Φ : TransitionForm Clock Var)
    (Q T : Judgement Clock Var → Prop)
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hs : (Φ.restrictCurrent T).Satisfies σ P α k)
    (hl : ∀ J ∈ Φ.current.locals, Q J →
      Judgement.Satisfies σ P (Φ.current.resets.apply α) k J) :
    (Φ.restrictCurrent Q).Satisfies σ P α k :=
  ⟨hs.1, fun J hJ => hl J hJ.1 hJ.2, hs.2.2⟩

theorem atomicProjection_satisfies_of {Φ : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hs : Φ.Satisfies σ P α k) : Φ.atomicProjection.Satisfies σ P α k :=
  ⟨hs.1, fun J hJ => hs.2.1 J hJ.1, hs.2.2⟩

theorem nonPredicateSatisfies_of_atomicProjection {Φ : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : Judgement.Position P}
    (hs : Φ.atomicProjection.Satisfies σ P α k) : Φ.NonPredicateSatisfies σ P α k := by
  refine ⟨hs.1, ?_, ?_⟩
  · intro J hJ
    have hl := Φ.current.locals_are_local J hJ
    cases J with
    | predicate p => trivial
    | terminal => exact hs.2.1 .terminal ⟨hJ, trivial⟩
    | leftMarker m => exact hs.2.1 (.leftMarker m) ⟨hJ, trivial⟩
    | _ => contradiction
  · have hn := hs.2.2
    cases he : Φ.nextPart with
    | none => trivial
    | some N =>
        change (match Φ.nextPart with | none => True | some M => _) at hn
        simp only [he] at hn ⊢
        by_cases ht : k.1 < P.size
        · simp only [dif_pos ht] at hn ⊢
          exact StateForm.nonPredicateSatisfies_of_satisfies hn
        · simp only [dif_neg ht] at hn ⊢

end TransitionForm

/-- Restricting the target's current locals preserves subsumption when every
source local is retained. -/
theorem SyntacticallySubsumed.restrictCurrent_right {Clock Var : Type*}
    {Φ Ψ : TransitionForm Clock Var} (h : Φ ⊑ Ψ) (Q : Judgement Clock Var → Prop)
    (hq : ∀ J ∈ Φ.current.locals, Q J) : Φ ⊑ Ψ.restrictCurrent Q :=
  { h with currentLocals := fun J hj => ⟨h.currentLocals hj, hq J hj⟩ }

namespace AlphaBranchRepresentation
variable {Clock Var : Type*} [DecidableEq Clock] [Nontrivial Clock]

/-- Closure soundness at a nonterminal interval: under admissibility and the
current invariant, erased current predicates follow by induction on complexity.
The next component is retained in full by `atomicProjection`. -/
theorem closed_satisfies_of_atomicProjection {Φ : TransitionForm Clock Var}
    (hc : expansionRules.IsClosed Φ)
    (hr : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady)
    {σ : FiniteSignal Var} (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hi : Judgement.SetInvariant (P.interval ⟨k.1, hk⟩)
      (Φ.current.resets.apply α) Φ.current.locals)
    (hs : Φ.atomicProjection.Satisfies σ P α k) : Φ.Satisfies σ P α k := by
  classical
  have hpSat : ∀ p : IntervalPredicate Clock Var, Judgement.predicate p ∈ Φ.current.locals →
      Judgement.Satisfies σ P (Φ.current.resets.apply α) k (.predicate p) := by
    intro p
    induction p using (measure IntervalPredicate.complexity).wf.induction with
    | h p ih =>
        intro hp
        by_cases ha : p.IsAtomic
        · exact hs.2.1 (.predicate p) ⟨hp, ha⟩
        · obtain ⟨R, hR⟩ := ConcreteRule.exists_of_ready_not_atomic (hr p hp) ha
          rcases (hc p hp).2 with hn | ⟨S, hS, Ψ, hΨ, B, hB, hsub⟩
          · exact (hn ⟨R, hR⟩).elim
          · have hBSat : B.Satisfies σ P α k := by
              let Q : Judgement Clock Var → Prop := fun J => J ∈ B.current.locals
              have hsmall : (Φ.restrictCurrent Q).Satisfies σ P α k := by
                apply Φ.restrictCurrent_satisfies_of Q TransitionForm.KeepAtomic hs
                intro J hJ hJB
                have hl := Φ.current.locals_are_local J hJ
                cases J with
                | predicate q =>
                    exact ih q (expansionRules.branchTransitionForm_reduced hS hΨ hB hJB) hJ
                | terminal => exact hs.2.1 .terminal ⟨hJ, trivial⟩
                | leftMarker m => exact hs.2.1 (.leftMarker m) ⟨hJ, trivial⟩
                | _ => contradiction
              exact transitionForm_subsumption_sound
                (hsub.restrictCurrent_right Q (fun _ h => h)) hsmall
            exact ConcreteRule.branch_sound hS σ P (Φ.current.resets.apply α) k
              (fun _ => hi p hp) ⟨Ψ, hΨ, (hB.evaluation σ P α k).1.mp hBSat⟩
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro J hJ
  have hl := Φ.current.locals_are_local J hJ
  cases J with
  | predicate p => exact hpSat p hJ
  | terminal => exact hs.2.1 .terminal ⟨hJ, trivial⟩
  | leftMarker m => exact hs.2.1 (.leftMarker m) ⟨hJ, trivial⟩
  | _ => contradiction

theorem closed_atomicProjection_iff {Φ : TransitionForm Clock Var}
    (hc : expansionRules.IsClosed Φ)
    (hr : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady)
    {σ : FiniteSignal Var} (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hi : Judgement.SetInvariant (P.interval ⟨k.1, hk⟩)
      (Φ.current.resets.apply α) Φ.current.locals) :
    Φ.atomicProjection.Satisfies σ P α k ↔ Φ.Satisfies σ P α k :=
  ⟨closed_satisfies_of_atomicProjection hc hr P α k hk hi,
    TransitionForm.atomicProjection_satisfies_of⟩

/-- Soundness of the projected closure follows from the invariant of its
source. The closure invariant is derived using the already-proved expansion path. -/
theorem closure_sound {Φ U : TransitionForm Clock Var}
    (hc : expansionRules.IsClosure Φ U)
    (hr : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady)
    {σ : FiniteSignal Var} (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hi : Φ.InvariantAt P α k hk)
    (hs : U.atomicProjection.Satisfies σ P α k) : Φ.Satisfies σ P α k := by
  have hu := hc.preservesInvariantAt_of_ruleInvariant
    expansionRules_preservesEvaluatedInvariant P α k hk
    (TransitionForm.nonPredicateSatisfies_of_atomicProjection hs) hi
  exact transitionForm_subsumption_sound hc.extension
    (closed_satisfies_of_atomicProjection hc.closed
      (closure_preservesCurrentTableauReady hc hr) P α k hk hu.1 hs)

end AlphaBranchRepresentation
namespace Formula.TableauInput
variable {Clock Var : Type*} [DecidableEq Clock] [Nontrivial Clock]

/-- A projected closure of a certified initial formula is sound with no
caller-supplied invariant: unclocked predicates have the trivial invariant. -/
theorem projected_closure_sound (input : Formula.TableauInput Var)
    {U : TransitionForm Clock Var}
    (hc : AlphaBranchRepresentation.expansionRules.IsClosure input.initialForm U)
    {σ : FiniteSignal Var} (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hk : k.1 < P.size)
    (hs : U.atomicProjection.Satisfies σ P α k) :
    Judgement.Satisfies σ P α k (.predicate (.plain input.1)) := by
  apply (input.initialForm_satisfies σ P α k).1
  apply AlphaBranchRepresentation.closure_sound hc input.initialForm_ready P α k hk ?_ hs
  constructor
  · intro p hp
    have heq : p = .plain input.1 := by
      simpa [initialForm, TransitionForm.ofState, StateForm.ofLocal] using hp
    subst p
    trivial
  · intro hnext N hN
    simp [initialForm, TransitionForm.ofState] at hN

end Formula.TableauInput
end STLTableau
