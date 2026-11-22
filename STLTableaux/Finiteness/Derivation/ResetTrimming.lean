/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Inventory.LocalResetSupport
import STLTableaux.Finiteness.Inventory.FiniteInventory
import STLTableaux.Closure.Normalization.NumericAlphaTransport
import STLTableaux.Closure.Normalization.NonPredicateAlphaTransport
import STLTableaux.Closure.Correctness.ClosureSoundness

/-! Unused reset deletion for the completed transition forms.
The outer reset binds current locals and the free clocks of the next input,
but not the current guards. The next reset binds only the next locals. -/
namespace STLTableau.Section4.Finiteness.ResetTrimming

open Section3 Finiteness.LocalResetSupport

local notation "StateForm" => Section3.StateForm
local notation "TransitionForm" => Section3.TransitionForm

variable {Clock Var : Type*}

noncomputable abbrev trimState (S : StateForm Clock Var) : StateForm Clock Var :=
  Finiteness.LocalResetSupport.state S

noncomputable def trim (F : TransitionForm Clock Var) : TransitionForm Clock Var :=
  { current := { F.current with resets := restrictResets F.current.resets F.bodyFreeClocks },
    nextPart := F.nextPart.map trimState }

@[simp] theorem trim_next (F : TransitionForm Clock Var) :
    (trim F).nextPart = F.nextPart.map trimState := rfl

@[simp] theorem trim_current_guards (F : TransitionForm Clock Var) :
    (trim F).current.guards = F.current.guards := rfl

@[simp] theorem trim_current_locals (F : TransitionForm Clock Var) :
    (trim F).current.locals = F.current.locals := rfl

theorem trim_current_apply (F : TransitionForm Clock Var) (α : ClockValuation Clock)
    {c : Clock} (hc : c ∈ F.bodyFreeClocks) :
    (trim F).current.resets.apply α c = F.current.resets.apply α c :=
  restrictResets_apply _ _ _ c hc

/-- In a literal path, trimming the previous edge's resets does not change
the incoming values read by the next requirement. -/
theorem trim_elapse_agree_next {F : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hn : F.nextPart = some N) (α : ClockValuation Clock) (δ : NNReal)
    {c : Clock} (hc : c ∈ N.freeClocks) :
    ClockResetSet.elapse ((trim F).current.resets.apply α) δ c =
      ClockResetSet.elapse (F.current.resets.apply α) δ c := by
  have hb : c ∈ F.bodyFreeClocks := Or.inr (by simpa only [hn] using hc)
  simp only [ClockResetSet.elapse, trim_current_apply F α hb]

@[simp] theorem trimState_freeClocks (S : StateForm Clock Var) :
    (trimState S).freeClocks = S.freeClocks := by
  change S.guardClocks ∪ (S.localClocks \ (restrictResets S.resets S.localClocks).clocks) = _
  rw [restrictResets_clocks]
  ext c
  simp only [Section3.StateForm.freeClocks, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

@[simp] theorem trim_bodyFreeClocks (F : TransitionForm Clock Var) :
    (trim F).bodyFreeClocks = F.bodyFreeClocks := by
  cases hn : F.nextPart <;> simp [Section3.TransitionForm.bodyFreeClocks,
    Section3.StateForm.localClocks, trim, hn]

@[simp] theorem trim_freeClocks (F : TransitionForm Clock Var) :
    (trim F).freeClocks = F.freeClocks := by
  unfold Section3.TransitionForm.freeClocks
  rw [trim_bodyFreeClocks]
  change F.current.guardClocks ∪ (F.bodyFreeClocks \
    (restrictResets F.current.resets F.bodyFreeClocks).clocks) = _
  rw [restrictResets_clocks]
  ext c
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

private theorem restrictResets_value_subset (R : ClockResetSet Clock) (S : Set Clock)
    {c : Clock} {a : NNReal} (h : (restrictResets R S).value c = some a) :
    R.value c = some a := by
  classical
  by_cases hc : c ∈ S
  · simpa [restrictResets, hc] using h
  · have hn : (none : Option NNReal) = some a := by
      simpa only [restrictResets, if_neg hc] using h
    cases hn

theorem trimState_within {S : StateForm Clock Var}
    {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)} (h : FiniteInventory.Within L G R S) :
    FiniteInventory.Within L G R (trimState S) :=
  ⟨h.1, h.2.1, fun c a ha => h.2.2 c a
    (restrictResets_value_subset S.resets S.localClocks ha)⟩

theorem trim_within {F : TransitionForm Clock Var}
    {L : Finset (Local Clock Var)} {G : Finset (Guard Clock)}
    {R : Finset (Clock × NNReal)} (h : FiniteInventory.TransitionWithin L G R F) :
    FiniteInventory.TransitionWithin L G R (trim F) := by
  refine ⟨⟨h.1.1, h.1.2.1, fun c a ha => h.1.2.2 c a
    (restrictResets_value_subset F.current.resets F.bodyFreeClocks ha)⟩, ?_⟩
  intro N hn
  obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.mp hn
  exact trimState_within (h.2 S hS)

theorem trimState_holds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trimState S).holds σ P α k ↔ S.holds σ P α k :=
  Finiteness.LocalResetSupport.holds_iff S σ P α k

theorem trim_holds (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trim F).holds σ P α k ↔ F.holds σ P α k := by
  simp only [trim, TransitionForm.holds, StateForm.holds]
  apply and_congr
  · apply and_congr Iff.rfl
    apply forall_congr'; intro l
    apply forall_congr'; intro hl
    apply l.holds_congr_of_agree
    intro c hc
    exact restrictResets_apply _ _ _ c (Or.inl ⟨l, hl, hc⟩)
  · cases hn : F.nextPart with
    | none => rfl
    | some N =>
      by_cases hk : k.1 < P.size
      · simp only [Option.map_some, dif_pos hk]
        refine (trimState_holds N σ P _ _).trans (N.holds_congr_of_agree σ P _ _ _ ?_)
        intro c hc
        have hb : c ∈ F.bodyFreeClocks := Or.inr (by simpa only [hn] using hc)
        simp only [ClockResetSet.elapse, restrictResets_apply _ _ _ c hb]
      · simp only [Option.map_some, dif_neg hk]

/-- Projecting current locals cannot make a deleted reset relevant. The
projection keeps the entire next requirement and leaves its elapsed valuation
unchanged on the clocks it reads. -/
theorem trim_restrictCurrent_holds (F : TransitionForm Clock Var)
    (Q : Local Clock Var → Prop) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    ((trim F).restrictCurrent Q).holds σ P α k ↔ (F.restrictCurrent Q).holds σ P α k := by
  simp only [Section3.TransitionForm.restrictCurrent, trim,
    TransitionForm.holds, StateForm.holds]
  apply and_congr
  · apply and_congr Iff.rfl
    apply forall_congr'; intro l
    apply forall_congr'; intro hl
    apply l.holds_congr_of_agree
    intro c hc
    exact restrictResets_apply _ _ _ c (Or.inl ⟨l, hl.1, hc⟩)
  · cases hn : F.nextPart with
    | none => rfl
    | some N =>
      by_cases hk : k.1 < P.size
      · simp only [Option.map_some, dif_pos hk]
        refine (trimState_holds N σ P _ _).trans (N.holds_congr_of_agree σ P _ _ _ ?_)
        intro c hc
        exact trim_elapse_agree_next hn α _ hc
      · simp only [Option.map_some, dif_neg hk]

theorem trim_atomicProjection_holds (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trim F).atomicProjection.holds σ P α k ↔ F.atomicProjection.holds σ P α k :=
  trim_restrictCurrent_holds F _ σ P α k

theorem trimState_nonPredicateHolds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trimState S).nonPredicateHolds σ P α k ↔ S.nonPredicateHolds σ P α k := by
  apply and_congr Iff.rfl
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  cases l <;> rfl

theorem trim_nonPredicateHolds (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trim F).nonPredicateHolds σ P α k ↔ F.nonPredicateHolds σ P α k := by
  simp only [trim, TransitionForm.nonPredicateHolds]
  apply and_congr
  · apply and_congr Iff.rfl
    apply forall_congr'; intro l
    apply forall_congr'; intro hl
    cases l <;> rfl
  · cases hn : F.nextPart with
    | none => rfl
    | some N =>
      by_cases hk : k.1 < P.size
      · simp only [Option.map_some, dif_pos hk]
        exact (trimState_nonPredicateHolds N σ P _ _).trans
          (N.nonPredicate_congr_of_agree σ P _ _ _ (fun _ hc => trim_elapse_agree_next hn α _ hc))
      · simp only [Option.map_some, dif_neg hk]

theorem trimState_invariant (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trimState S).EvaluatedInvariant σ P α k ↔ S.EvaluatedInvariant σ P α k :=
  Finiteness.LocalResetSupport.invariant_iff S σ P α k

theorem trimState_numeric (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trimState S).EvaluatedNumeric σ P α k ↔ S.EvaluatedNumeric σ P α k := by
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  apply l.evaluatedNumeric_congr
  intro c hc
  exact restrictResets_apply _ _ _ c ⟨l, hl, hc⟩

theorem trim_numeric (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    (trim F).EvaluatedNumeric σ P α k ↔ F.EvaluatedNumeric σ P α k := by
  simp only [trim, TransitionForm.EvaluatedNumeric]
  apply and_congr
  · simp only [StateForm.EvaluatedNumeric]
    apply forall_congr'; intro l
    apply forall_congr'; intro hl
    apply l.evaluatedNumeric_congr
    intro c hc
    exact restrictResets_apply _ _ _ c (Or.inl ⟨l, hl, hc⟩)
  · cases hn : F.nextPart with
    | none => simp
    | some N =>
      simp only [Option.map_some, Option.some.injEq, forall_eq']
      apply forall_congr'; intro hk
      refine (trimState_numeric N σ P _ _).trans (N.evaluatedNumeric_congr σ P _ _ _ ?_)
      intro c hc
      have hb : c ∈ F.bodyFreeClocks := Or.inr (by simpa only [hn] using hc)
      simp only [ClockResetSet.elapse, restrictResets_apply _ _ _ c hb]

end STLTableau.Section4.Finiteness.ResetTrimming
