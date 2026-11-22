/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.ClosureExistence

/-! # Fresh branches extending the original enclosing transition form -/
namespace STLTableau
open scoped STL
namespace StateForm
variable {Clock Var : Type*}

def LocallyClosed (S : StateForm Clock Var) : Prop := S.localClocks ⊆ S.resets.clocks

@[simp] theorem localClocks_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).localClocks = e '' S.localClocks := by
  ext c
  simp [localClocks, rename, Set.mem_image, Set.mem_iUnion]

@[simp] theorem locallyClosed_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).LocallyClosed ↔ S.LocallyClosed := by
  simp only [LocallyClosed, localClocks_rename]
  change e '' S.localClocks ⊆ (S.resets.rename e).clocks ↔ _
  rw [ClockResetSet.clocks_rename]
  exact Set.image_subset_image_iff e.injective

@[simp] theorem locallyClosed_alphaReset (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.alphaReset e).LocallyClosed ↔ S.LocallyClosed :=
  S.locallyClosed_rename e
end StateForm
namespace TransitionForm
variable {Clock Var : Type*}

def NextLocallyClosed (Φ : TransitionForm Clock Var) : Prop :=
  ∀ N, Φ.nextPart = some N → N.LocallyClosed

theorem AlphaEquivalent.nextLocallyClosed {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) : Φ.NextLocallyClosed ↔ Ψ.NextLocallyClosed := by
  induction h with
  | refl => rfl
  | outer Φ e hf => cases hn : Φ.nextPart <;> simp [NextLocallyClosed, alphaOuter, hn]
  | next Φ e hf => cases hn : Φ.nextPart <;> simp [NextLocallyClosed, alphaNext, hn]
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Only the branch is renamed: the original source and its predicate remain
literal subcomponents of the union. Closed next-local clock scopes prevent
capture by inherited next resets. -/
theorem unionCompatible_of_branchFresh (Φ B : TransitionForm Clock Var)
    (hfresh : Disjoint B.boundClocks Φ.allClocks)
    (hfree : Disjoint Φ.current.resets.clocks B.freeClocks)
    (hnextClosed : B.NextLocallyClosed) : Φ.UnionCompatible B := by
  have hcur : Φ.current.resets.Consistent B.current.resets :=
    ClockResetSet.consistent_of_disjoint (hfresh.symm.mono
      (fun _ hc => Or.inr (Or.inl hc)) (fun _ hc => Or.inl hc))
  have hnext : ∀ N K, Φ.nextPart = some N → B.nextPart = some K →
      N.resets.Consistent K.resets := by
    intro N K hn hk
    exact ClockResetSet.consistent_of_disjoint (hfresh.symm.mono
      (fun _ hc => Or.inr (nextResets_subset_bound hn hc)) (nextResets_subset_bound hk))
  refine ⟨Φ.subsumed_union_left_of_boundFresh B hfresh, ?_, hcur, hnext⟩
  apply Φ.subsumed_union_right B hcur hnext
  · apply Set.disjoint_left.2
    intro c hc hb
    have hu : c ∈ Φ.current.resets.clocks ∪ B.current.resets.clocks := by
      simpa only [union, StateForm.union, ClockResetSet.clocks_union] using hc.1
    exact Set.disjoint_left.1 hfree (hu.resolve_right hc.2) (Or.inr hb)
  · intro N M hn hm
    apply Set.disjoint_left.2
    intro c _ hc
    obtain ⟨J, hJ⟩ := Set.mem_iUnion.1 hc
    obtain ⟨hj, hf, hnot⟩ := Set.mem_iUnion.1 hJ
    exact hnot (hnextClosed N hn (Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨hj, hf⟩⟩))

/-- Finite freshening gives a compatible branch without changing the source. -/
theorem compatible_underReset_exists [Infinite Clock]
    (Φ F : TransitionForm Clock Var) (hguard : F.current.constraints = ∅)
    (hnext : F.NextLocallyClosed) :
    ∃ B, B.AlphaEquivalent (F.underReset Φ.current.resets) ∧ Φ.UnionCompatible B := by
  let B₀ := F.underReset Φ.current.resets
  obtain ⟨B, ha, hf⟩ := B₀.exists_fresh_alpha Φ.allClocks Φ.allClocks_finite
  refine ⟨B, ha, Φ.unionCompatible_of_branchFresh B hf ?_ ?_⟩
  · rw [ha.freeClocks]
    apply Set.disjoint_left.2
    intro c hc hb
    simp only [B₀, freeClocks, underReset, hguard, Set.image_empty, Set.empty_union,
      bodyFreeClocks, ClockResetSet.clocks_union] at hb
    exact hb.2 (Or.inr hc)
  · exact ha.nextLocallyClosed.2 hnext

end TransitionForm
namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock]

local macro "close_branch" : tactic =>
  `(tactic| (all_goals
        simp [ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_finish,
          Judgement.markedGT, Marker.conj, Marker.notConj, Marker.complement,
          TransitionForm.toTransitionForm?, TransitionForm.ofState, TransitionForm.ofNextState,
          TransitionForm.prependReset, TransitionForm.union, TransitionForm.unionNext,
          StateForm.ofLocal, StateForm.ofClock, StateForm.empty, StateForm.union,
          TransitionForm.NextLocallyClosed, StateForm.LocallyClosed, StateForm.localClocks,
          Judgement.freeClocks, Judgement.predicateClocks, ClockResetSet.clocks_union,
          Set.insert_subset_iff]))

/-- Each rule has at least one branch whose next-local clock occurrences are
all reset-bound. This is a syntactic existence choice, not a satisfied-branch choice. -/
theorem exists_locallyClosed_branch {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var} (hr : ConcreteRule p R) :
    ∃ Ψ ∈ R.branches, ∃ F : TransitionForm Clock Var,
      TransitionForm.toTransitionForm? Ψ = some F ∧ F.current.constraints = ∅ ∧
      F.NextLocallyClosed := by
  classical
  cases hr with
  | plainAnd φ ψ =>
      refine ⟨.conj (.predicate (.plain φ)) (.predicate (.plain ψ)),
        by simp [ExpansionRule.plainAnd], ?_⟩
      close_branch
  | plainOr φ ψ =>
      refine ⟨.predicate (.plain φ), by simp [ExpansionRule.plainOr], ?_⟩
      close_branch
  | plainUntil φ ψ =>
      refine ⟨.conj (.predicate (.plain φ)) (.predicate (.plain ψ)),
        by simp [ExpansionRule.plainUntil], ?_⟩
      close_branch
  | plainRelease φ ψ =>
      refine ⟨.predicate (.plain φ), by simp [ExpansionRule.plainRelease], ?_⟩
      close_branch
  | openEventually c I φ =>
      refine ⟨⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,○]◇[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[○]),
        by simp [ExpansionRule.openEventually], ?_⟩
      close_branch
  | openAlways c I φ =>
      refine ⟨⟦c ↦ᶜ 0⟧ ·ⱼ ((↑[c,○]□[I]φ : IntervalPredicate Clock Var) ∧ⱼ lty[○]),
        by simp [ExpansionRule.openAlways], ?_⟩
      close_branch
  | upperAlways c d b I φ hcd =>
      refine ⟨Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
        by simp [ExpansionRule.upperAlways], ?_⟩
      close_branch
  | boundedAlways c d b q I φ hcd =>
      refine ⟨Xⱼ ((c ≤ᶜ (⟨I.lower, I.lower_nonnegative⟩ : NNReal)) ∧ⱼ ∗),
        by simp [ExpansionRule.boundedAlways], ?_⟩
      close_branch
  | upperEventually c d b I φ hcd =>
      by_cases hz : I.lower = 0
      · refine ⟨.predicate (.plain φ), by simp [ExpansionRule.upperEventually, hz], ?_⟩
        close_branch
      · refine ⟨ExpansionRule.upperEventually_check c d b ○ I φ,
          by simp [ExpansionRule.upperEventually, hz], ?_⟩
        cases b
        close_branch
  | boundedEventually c d b q I φ hcd =>
      refine ⟨ExpansionRule.boundedEventually_finish d q ○ I φ,
        by simp [ExpansionRule.boundedEventually], ?_⟩
      cases q
      close_branch


/-- At least one branch of any actual rule can be inserted while preserving
literal inclusion of the original source, even with conflicting existing resets. -/
theorem compatible_branch_exists [Infinite Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var} (hr : ConcreteRule p R)
    (Φ : TransitionForm Clock Var) :
    ∃ Ψ ∈ R.branches, ∃ B,
      AlphaBranchRepresentation Φ.current.resets Ψ B ∧ Φ.UnionCompatible B := by
  obtain ⟨Ψ, hΨ, F, hF, hg, hn⟩ := hr.exists_locallyClosed_branch
  obtain ⟨B, ha, hc⟩ := Φ.compatible_underReset_exists F hg hn
  have hb := hr.branchTransitionForm_represents hΨ Φ.current.resets
  have heq : Classical.choose (hr.branch_has_transitionForm hΨ) = F :=
    Option.some.inj ((Classical.choose_spec (hr.branch_has_transitionForm hΨ)).symm.trans hF)
  change BranchRepresentation _ _
    ((Classical.choose (hr.branch_has_transitionForm hΨ)).underReset Φ.current.resets) at hb
  rw [heq] at hb
  exact ⟨Ψ, hΨ, B, ⟨_, hb, ha⟩, hc⟩

end ConcreteRule

namespace AlphaBranchRepresentation
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- A rule-closed extension of the original form; compatibility and freshness
are constructed from the rule, not supplied by the caller. -/
theorem ruleClosed_extension_exists {Φ : TransitionForm Clock Var}
    {p : IntervalPredicate Clock Var} (hp : Judgement.predicate p ∈ Φ.current.locals)
    {R : ExpansionRule Clock Var} (hr : ConcreteRule p R) :
    ∃ U, (Φ ⊑ U) ∧ expansionRules.RuleClosedFor U p := by
  obtain ⟨Ψ, hΨ, B, hb, hc⟩ := hr.compatible_branch_exists Φ
  refine ⟨Φ.union B, hc.leftSubsumed, hc.leftSubsumed.currentLocals hp,
    Or.inr ⟨R, hr, Ψ, hΨ, B, ?_, hc.rightSubsumed⟩⟩
  apply hb.mono hc.leftSubsumed.currentResets
  apply Set.disjoint_left.2
  intro c hextra hfree
  apply Set.disjoint_left.1 hc.leftSubsumed.outerFresh hextra
  refine ⟨Or.inl (Set.mem_iUnion₂.2 ⟨Judgement.predicate p, hp, ?_⟩), hfree.2⟩
  exact hr.branchFreeClocks hΨ hfree.1

theorem pExpansion_exists {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hp : Judgement.predicate p ∈ Φ.current.locals) :
    ∃ U, expansionRules.PExpansion p Φ U := by
  classical
  by_cases hh : (expansionRules : ExpansionRules Clock Var).HasRule p
  · obtain ⟨R, hr⟩ := hh
    obtain ⟨U, hsub, hu⟩ := ruleClosed_extension_exists hp hr
    obtain ⟨F, hf, _⟩ := ExpansionRules.pExpansion_exists_of_extension hp hsub hu
    exact ⟨F, hf⟩
  · exact ⟨Φ, ExpansionRules.PExpansion.refl_of_ruleClosed ⟨hp, Or.inl hh⟩⟩

/-- Every transition form has a literal minimal closure for the concrete
alpha-branch interface. No satisfaction or pre-existing closure is assumed. -/
theorem closure_exists (Φ : TransitionForm Clock Var) :
    ∃ U, expansionRules.IsClosure Φ U := by
  apply ExpansionRules.closure_exists expansionRules ?_ Φ
  intro F p hp hopen
  obtain ⟨G, he⟩ := pExpansion_exists hp
  exact ⟨G, he.extension, he.target_ruleClosed⟩

/-- The resulting minimal closure is reached by a finite sequence of the
existing literal minimal expansions. -/
theorem closure_exists_with_path (Φ : TransitionForm Clock Var) :
    ∃ U, expansionRules.IsClosure Φ U ∧ expansionRules.ExpansionPath Φ U := by
  obtain ⟨U, hu⟩ := closure_exists Φ
  exact ⟨U, hu, hu.expansionPath⟩

end AlphaBranchRepresentation

end STLTableau
