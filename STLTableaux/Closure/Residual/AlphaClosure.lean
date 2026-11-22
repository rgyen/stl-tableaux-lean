import STLTableaux.Closure.Residual.AlphaTransport

/-! # Branch representations and closure transport up to alpha-conversion

The alpha-saturated relations below transport existing literal expansions and
closures. Their definitions do not assert closure existence or minimality with
respect to an alpha-quotiented subsumption order.
-/
namespace STLTableau
open scoped STL

/-- A structural branch representative followed by syntactic alpha-conversion.
Predicate provenance is retained up to renaming, rather than literal membership. -/
def AlphaBranchRepresentation {Clock Var : Type*} (Λ : ClockResetSet Clock)
    (Ψ : Judgement Clock Var) (B : TransitionForm Clock Var) : Prop :=
  ∃ B₀, BranchRepresentation Λ Ψ B₀ ∧ B.AlphaEquivalent B₀

namespace AlphaBranchRepresentation
variable {Clock Var : Type*}

theorem of_literal {Λ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var} (h : BranchRepresentation Λ Ψ B) :
    AlphaBranchRepresentation Λ Ψ B := ⟨B, h, .refl B⟩

theorem mono {Λ₁ Λ₂ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var} (hsub : Λ₁.Subset Λ₂)
    (hfresh : Disjoint (Λ₂.clocks \ Λ₁.clocks) (Ψ.freeClocks \ Λ₁.clocks))
    (h : AlphaBranchRepresentation Λ₁ Ψ B) : AlphaBranchRepresentation Λ₂ Ψ B := by
  obtain ⟨B₀, hb, ha⟩ := h
  exact ⟨B₀, hb.mono hsub hfresh, ha⟩

theorem transport {Λ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    {B B' : TransitionForm Clock Var} (h : AlphaBranchRepresentation Λ Ψ B)
    (ha : B'.AlphaEquivalent B) : AlphaBranchRepresentation Λ Ψ B' := by
  obtain ⟨B₀, hb, h₀⟩ := h
  exact ⟨B₀, hb, ha.trans h₀⟩

theorem evaluation {Λ : ClockResetSet Clock} {Ψ : Judgement Clock Var}
    {B : TransitionForm Clock Var} (h : AlphaBranchRepresentation Λ Ψ B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (B.Satisfies σ P α k ↔ Judgement.Satisfies σ P (Λ.apply α) k Ψ) ∧
    (B.NonPredicateSatisfies σ P α k ↔
      Judgement.NonPredicateSatisfies σ P (Λ.apply α) k Ψ) ∧
    (B.evaluatedInvariant σ P α k ↔
      Judgement.EvaluatedInvariant σ P (Λ.apply α) k Ψ) := by
  obtain ⟨B₀, hb, ha⟩ := h
  have he := hb.evaluation σ P α k
  exact ⟨(ha.equivalent σ P α k).trans he.1,
    (ha.nonPredicateSatisfies σ P α k).trans he.2.1,
    (ha.evaluatedInvariant σ P α k).trans he.2.2⟩

/-- The existing expansion metatheory accepts alpha-converted branches once
complexity and all three evaluation contracts have been transported. -/
def expansionRules [DecidableEq Clock] : ExpansionRules Clock Var where
  rule := ConcreteRule
  branchTransitionForm := AlphaBranchRepresentation
  branchTransitionForm_mono := mono
  branchFreeClocks := fun hR hΨ => ConcreteRule.branchFreeClocks hR hΨ
  branchTransitionForm_reduced := by
    intro p R Ψ Λ B q hR hΨ hB hq
    obtain ⟨B₀, hb, ha⟩ := hB
    have hred : ExpansionRules.AllCurrentPredicates B₀
        (fun q => q.complexity < p.complexity) := by
      intro q hq
      have hlt := ConcreteRule.complexityReduced hR Ψ hΨ q (hb.currentPredicate_mem q hq)
      simpa [ConcreteRule.source_eq hR] using hlt
    exact ((ha.allCurrentPredicates _ (by intros; simp)).2 hred) q hq
  branchTransitionForm_satisfies_iff := fun h σ P α k => (h.evaluation σ P α k).1
  branchTransitionForm_nonPredicateSatisfies_iff := fun h σ P α k => (h.evaluation σ P α k).2.1
  branchTransitionForm_currentInvariant := by
    intro Ψ Λ B h σ P α k hk hinv
    have hi := ((h.evaluation σ P α k).2.2).2 hinv
    exact Judgement.setInvariant_of_evaluated σ P
      (B.current.resets.apply α) k hk _ hi.1
  branchTransitionForm_nextInvariant := by
    intro Ψ Λ B h σ P α k hnext N hN hinv
    have hi := ((h.evaluation σ P α k).2.2).2 hinv
    have hk : k.1 < P.size := by omega
    simp only [TransitionForm.evaluatedInvariant, hN, dif_pos hk] at hi
    exact Judgement.setInvariant_of_evaluated σ P _ ⟨k.1 + 1, by omega⟩ hnext _ hi.2

theorem expansionRules_preservesEvaluatedInvariant [DecidableEq Clock] :
    (expansionRules : ExpansionRules Clock Var).PreservesEvaluatedInvariant :=
  ConcreteRule.expansionRules_preservesEvaluatedInvariant expansionRules (fun _ _ => Iff.rfl)

theorem expansion_preservesCurrentTableauReady [DecidableEq Clock]
    {Φ Φ' : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (hexp : expansionRules.PExpansion p Φ Φ')
    (hΦ : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady) :
    ExpansionRules.AllCurrentPredicates Φ' IntervalPredicate.TableauReady := by
  apply hexp.preservesAllCurrentPredicates hΦ
  intro R Ψ B hR hΨ hB _ q hq
  obtain ⟨B₀, hb, ha⟩ := hB
  apply ((ha.currentTableauReady).2 ?_) q hq
  intro r hr
  exact (ConcreteRule.branch_tableauReady hR (hΦ p hexp.1) hΨ).currentPredicates
    (hb.currentPredicate_mem r hr)

theorem closure_preservesCurrentTableauReady [DecidableEq Clock]
    {Φ Φc : TransitionForm Clock Var} (hc : expansionRules.IsClosure Φ Φc)
    (hΦ : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady) :
    ExpansionRules.AllCurrentPredicates Φc IntervalPredicate.TableauReady :=
  hc.expansionPath.preserve (fun _ he => expansion_preservesCurrentTableauReady he) hΦ

end AlphaBranchRepresentation

namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Compatible fresh representatives now retain the complete branch contract.
The branch is anchored at the original enclosing reset set. -/
theorem alpha_branch_normalization_exists
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {Ψ : Judgement Clock Var} (hΨ : Ψ ∈ R.branches)
    (Φ : TransitionForm Clock Var) :
    ∃ Φa B : TransitionForm Clock Var,
      Φa.AlphaEquivalent Φ ∧ AlphaBranchRepresentation Φ.current.resets Ψ B ∧
      Φa.UnionCompatible B := by
  obtain ⟨Φa, B, hΦ, hB, hc⟩ := Φ.exists_alpha_compatible_representatives
    (hrule.branchTransitionForm hΨ Φ.current.resets)
  exact ⟨Φa, B, hΦ,
    ⟨_, hrule.branchTransitionForm_represents hΨ Φ.current.resets, hB⟩, hc⟩

end ConcreteRule

namespace ExpansionRules
variable {Clock Var : Type*}

/-- Existential transport of literal expansion to alpha representatives.
The selected source predicate belongs to the chosen representative. -/
def AlphaExpansion (E : ExpansionRules Clock Var) (Φ Ψ : TransitionForm Clock Var) : Prop :=
  ∃ p F G, F.AlphaEquivalent Φ ∧ E.PExpansion p F G ∧ G.AlphaEquivalent Ψ

/-- Existential transport of a literal minimal closure to alpha representatives. -/
def AlphaClosure (E : ExpansionRules Clock Var) (Φ Ψ : TransitionForm Clock Var) : Prop :=
  ∃ F G, F.AlphaEquivalent Φ ∧ E.IsClosure F G ∧ G.AlphaEquivalent Ψ

theorem PExpansion.toAlpha {E : ExpansionRules Clock Var} {p : IntervalPredicate Clock Var}
    {Φ Ψ : TransitionForm Clock Var} (h : E.PExpansion p Φ Ψ) : E.AlphaExpansion Φ Ψ :=
  ⟨p, Φ, Ψ, .refl Φ, h, .refl Ψ⟩

theorem IsClosure.toAlpha {E : ExpansionRules Clock Var}
    {Φ Ψ : TransitionForm Clock Var} (h : E.IsClosure Φ Ψ) : E.AlphaClosure Φ Ψ :=
  ⟨Φ, Ψ, .refl Φ, h, .refl Ψ⟩

theorem AlphaExpansion.transport {E : ExpansionRules Clock Var}
    {Φ Ψ Φ' Ψ' : TransitionForm Clock Var} (h : E.AlphaExpansion Φ Ψ)
    (hΦ : Φ'.AlphaEquivalent Φ) (hΨ : Ψ'.AlphaEquivalent Ψ) : E.AlphaExpansion Φ' Ψ' := by
  obtain ⟨p, F, G, hf, he, hg⟩ := h
  exact ⟨p, F, G, hf.trans hΦ.symm, he, hg.trans hΨ.symm⟩

theorem AlphaClosure.transport {E : ExpansionRules Clock Var}
    {Φ Ψ Φ' Ψ' : TransitionForm Clock Var} (h : E.AlphaClosure Φ Ψ)
    (hΦ : Φ'.AlphaEquivalent Φ) (hΨ : Ψ'.AlphaEquivalent Ψ) : E.AlphaClosure Φ' Ψ' := by
  obtain ⟨F, G, hf, he, hg⟩ := h
  exact ⟨F, G, hf.trans hΦ.symm, he, hg.trans hΨ.symm⟩

theorem AlphaExpansion.preservesInvariantAt {E : ExpansionRules Clock Var}
    (hrules : E.PreservesEvaluatedInvariant) {Φ Ψ : TransitionForm Clock Var}
    (h : E.AlphaExpansion Φ Ψ) {σ : FiniteSignal Var} (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (hs : Ψ.NonPredicateSatisfies σ P α k) (hi : Φ.InvariantAt P α k hk) :
    Ψ.InvariantAt P α k hk := by
  obtain ⟨p, F, G, hf, he, hg⟩ := h
  exact (hg.invariantAt P α k hk).1
    (he.preservesInvariantAt_of_ruleInvariant hrules P α k hk
      ((hg.nonPredicateSatisfies σ P α k).2 hs) ((hf.invariantAt P α k hk).2 hi))

theorem AlphaClosure.preservesInvariantAt {E : ExpansionRules Clock Var}
    (hrules : E.PreservesEvaluatedInvariant) {Φ Ψ : TransitionForm Clock Var}
    (h : E.AlphaClosure Φ Ψ) {σ : FiniteSignal Var} (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (hs : Ψ.NonPredicateSatisfies σ P α k) (hi : Φ.InvariantAt P α k hk) :
    Ψ.InvariantAt P α k hk := by
  obtain ⟨F, G, hf, he, hg⟩ := h
  exact (hg.invariantAt P α k hk).1
    (he.preservesInvariantAt_of_ruleInvariant hrules P α k hk
      ((hg.nonPredicateSatisfies σ P α k).2 hs) ((hf.invariantAt P α k hk).2 hi))

end ExpansionRules
namespace AlphaBranchRepresentation
variable {Clock Var : Type*} [DecidableEq Clock]

theorem alphaClosure_preservesCurrentTableauReady {Φ Ψ : TransitionForm Clock Var}
    (h : expansionRules.AlphaClosure Φ Ψ)
    (hi : ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady) :
    ExpansionRules.AllCurrentPredicates Ψ IntervalPredicate.TableauReady := by
  obtain ⟨F, G, hf, he, hg⟩ := h
  exact hg.currentTableauReady.1
    (closure_preservesCurrentTableauReady he (hf.currentTableauReady.2 hi))

end AlphaBranchRepresentation
end STLTableau
