import STLTableaux

namespace STLTableau.Review
open scoped STL

-- Counterexamples for reset scopes and clock freshness.

theorem toTransitionForm_reset_guard_changes_meaning
    (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) :
    let Ψ : Judgement Unit Unit := ⟦() ↦ᶜ 0⟧ ·ⱼ (() =ᶜ 0)
    ∃ B, TransitionForm.toTransitionForm? Ψ = some B ∧
      Judgement.Satisfies σ P (fun _ => 1) k Ψ ∧
      ¬ B.Satisfies σ P (fun _ => 1) k := by
  dsimp
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [Judgement.Satisfies, ClockRelation.Holds]
  · simp [TransitionForm.prependReset, TransitionForm.ofState,
      StateForm.ofClock, TransitionForm.Satisfies,
      ClockConstraint.Satisfies, ClockRelation.Holds]

-- The `↑` rule for `□` has the branch `X(c ≤ 1 ∧ terminal)`.
-- On a last piece of duration ≤ 1, resetting c from 2 to 0 changes its truth.
theorem terminal_wait_reset_is_not_fresh :
    ¬ Disjoint
      ((⟦0 ↦ᶜ 0⟧ : ClockResetSet Nat).clocks \ ClockResetSet.empty.clocks)
      ((Xⱼ ((0 ≤ᶜ 1) ∧ⱼ ∗) : Judgement Nat Unit).freeClocks \
        ClockResetSet.empty.clocks) := by
  intro hdisjoint
  have hzero : (0 : Nat) ∉ ClockResetSet.empty.clocks := by
    rintro ⟨a, ha⟩
    cases ha
  exact Set.disjoint_left.1 hdisjoint
    ⟨by simp, hzero⟩ ⟨by simp [Judgement.freeClocks], hzero⟩

theorem terminal_wait_is_registered :
    let I : BoundedTimeInterval := ⟨1, 2, by norm_num, by norm_num⟩
    (Xⱼ ((0 ≤ᶜ 1) ∧ⱼ ∗) : Judgement Nat Unit) ∈
      (ExpansionRule.upperAlways 0 1 ● I Formula.truth).branches := by
  dsimp [ExpansionRule.upperAlways]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem invariantAt_last_interval
    (σ : FiniteSignal Unit) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) (hk : k.1 < P.size) (hlast : k.1 + 1 = P.size)
    (Φ : TransitionForm Nat Unit) (α : ClockValuation Nat) :
    Φ.InvariantAt P α k hk ↔
      Judgement.SetInvariant (P.interval ⟨k.1, hk⟩)
        (Φ.current.resets.apply α) Φ.current.locals := by
  simp [TransitionForm.InvariantAt, hlast]

#print axioms toTransitionForm_reset_guard_changes_meaning
#print axioms terminal_wait_reset_is_not_fresh
#print axioms ExpansionRules.PExpansion.rankDecrease
#print axioms Judgement.plain_eventually_fixed_marker_equiv
#print axioms Judgement.plain_always_fixed_marker_equiv
#print axioms Judgement.upper_split_equiv
#print axioms Judgement.upper_eventually_split_equiv
#print axioms Judgement.upper_always_split_equiv
#print axioms ConcreteRule.branchFreeClocks
#print axioms BranchTransitionForms.expansion_preservesInvariantAt
#print axioms BranchTransitionForms.closure_preservesInvariantAt
end STLTableau.Review
