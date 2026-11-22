/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Derivation.CompletedDerivation
import STLTableaux.Finiteness.Derivation.ResetTrimming

/-! The collection `C(M)` of Definition D.4. Original closures are admitted
unchanged. A finite completion may start from an input differing only in
unused resets. Unused resets are removed from the completed output. -/
namespace STLTableau.Section4.Finiteness.CompletedDerivation

open Section3 ResetTrimming
open Finiteness.LocalResetSupport

variable {Clock Var : Type*}

@[simp] theorem trimState_idempotent (S : Section3.StateForm Clock Var) :
    trimState (trimState S) = trimState S := by
  classical
  have reset_ext {R T : ClockResetSet Clock} (h : R.value = T.value) : R = T := by
    cases R
    cases T
    cases h
    rfl
  have hr : restrictResets (restrictResets S.resets S.localClocks) S.localClocks =
      restrictResets S.resets S.localClocks := by
    apply reset_ext
    funext c
    by_cases hc : c ∈ S.localClocks
    · simp only [restrictResets, if_pos hc]
    · simp only [restrictResets, if_neg hc]
  exact congrArg (fun R => { S with resets := R }) hr

/-- `Admitted M F` represents `F ∈ C(M)`: an original closure or a completed
construction with unused resets removed. Replaying on an input with the same
trimmed form changes only unused assignments. The stored generator is a
separate condition on the paired graph. -/
inductive Admitted [DecidableEq Clock] :
    Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop
  | original {M F} : ConcreteContextual.catalogue.IsClosure (.ofState M) F →
      M.Ready → Admitted M F
  | replayed {M F M₀ F₀} : trimState M₀ = trimState M →
      Member M₀ F₀ → trim F₀ = F → Admitted M F

theorem admitted_trim [DecidableEq Clock]
    {M : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : Member M F) : Admitted (trimState M) (trim F) :=
  .replayed (trimState_idempotent M).symm h rfl

private theorem state_nonPredicate_of_trim_eq {N M : Section3.StateForm Clock Var}
    (he : trimState N = trimState M) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    N.nonPredicateHolds σ P α k ↔ M.nonPredicateHolds σ P α k := by
  rw [← trimState_nonPredicateHolds N σ P α k, he, trimState_nonPredicateHolds]

private theorem state_numeric_of_trim_eq {N M : Section3.StateForm Clock Var}
    (he : trimState N = trimState M) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    N.EvaluatedNumeric σ P α k ↔ M.EvaluatedNumeric σ P α k := by
  rw [← trimState_numeric N σ P α k, he, trimState_numeric]

private theorem state_holds_of_trim_eq {N M : Section3.StateForm Clock Var}
    (he : trimState N = trimState M) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    N.holds σ P α k ↔ M.holds σ P α k := by
  rw [← trimState_holds N σ P α k, he, trimState_holds]

theorem admitted_localLaws [DecidableEq Clock] [Nontrivial Clock] :
    JudgementTableau.LocalLaws (Admitted (Clock := Clock) (Var := Var)) := by
  constructor
  · intro M F h σ P α k hs
    cases h with
    | original hc hr =>
      exact member_localLaws.nonPredicate (.original hc hr) σ P α k hs
    | replayed he hm ht =>
      subst F
      exact (state_nonPredicate_of_trim_eq he σ P α k).1
        (member_localLaws.nonPredicate hm σ P α k ((trim_nonPredicateHolds _ σ P α k).1 hs))
  · intro M F h σ P α k hi hs
    cases h with
    | original hc hr =>
      exact member_localLaws.numeric (.original hc hr) σ P α k hi hs
    | replayed he hm ht =>
      subst F
      exact (trim_numeric _ σ P α k).2
        (member_localLaws.numeric hm σ P α k ((state_numeric_of_trim_eq he σ P α k).2 hi)
          ((trim_nonPredicateHolds _ σ P α k).1 hs))
  · intro M F h σ P α k hi hs
    cases h with
    | original hc hr =>
      exact member_localLaws.recover (.original hc hr) σ P α k hi hs
    | replayed he hm ht =>
      subst F
      obtain ⟨hf, hn⟩ := member_localLaws.recover hm σ P α k
        ((state_numeric_of_trim_eq he σ P α k).2 hi)
        ((trim_atomicProjection_holds _ σ P α k).1 hs)
      exact ⟨(trim_holds _ σ P α k).2 hf, (state_holds_of_trim_eq he σ P α k).1 hn⟩

end STLTableau.Section4.Finiteness.CompletedDerivation
