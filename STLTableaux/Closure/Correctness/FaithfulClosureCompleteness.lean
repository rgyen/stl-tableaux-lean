import STLTableaux.Tableau.Stability.GeneratorStability
import STLTableaux.Rules.Finite.Preservation
import STLTableaux.Rules.Unbounded.UnboundedOpeningPreservation
import STLTableaux.Closure.Correctness.FaithfulClosureProgress
import STLTableaux.Closure.Normalization.NormalizedFiniteInvariant
import STLTableaux.Closure.Normalization.NormalizedInfiniteInvariant
import STLTableaux.Closure.Normalization.NormalizedStability
import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue
import STLTableaux.Closure.Correctness.FaithfulClosureIteration
import STLTableaux.Closure.Normalization.FaithfulAlphaStability
import STLTableaux.Closure.Subsumption.InvariantTransport

/-! Branch selection and closure completeness using Section 3 satisfaction. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace FaithfulClosure

/-- Finite-rule case of Theorem 3.13 and Proposition 3.14. A satisfied
normalized branch witnesses preservation of the predicate invariants and
stability, including under next and reset. -/
theorem finite_branch_complete [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, STLTableau.Invariant σ P (Λ.apply α) k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : STLTableau.satisfies σ P (Λ.apply α) k (.predicate p)) :
    ∃ (B : TransitionForm Clock Var) (Ψ : STLTableau.Judgement Clock Var)
      (F : TransitionForm Clock Var),
      ConcreteFinite.Branch (Predicate.ofFinite p) Λ B ∧
      Ψ ∈ R.branches ∧ TransitionForm.normalize? (Judgement.ofFinite Ψ) = some F ∧
      B = F.underReset Λ ∧ B.holds σ P α k ∧
      STLTableau.EvaluatedInvariant σ P (Λ.apply α) k Ψ ∧
      (Judgement.ofFinite Ψ).UnderlyingStable σ P := by
  obtain ⟨Ψ, hΨ, hsΨ, hiΨ⟩ := STLTableau.rule_complete_preserving hr σ P (Λ.apply α) k hi hst hs
  obtain ⟨F, hF, he⟩ := ConcreteFinite.branch_normalization hr hΨ Λ
  exact ⟨F.underReset Λ, Ψ, F,
    ⟨p, R, Ψ, F, rfl, hr, hΨ, hF, rfl⟩, hΨ, hF, rfl,
    (he σ P α k).2 hsΨ, hiΨ,
    GeneratorStability.finite_branch_stable hr hΨ σ P hst⟩

/-- Unbounded-rule case of Proposition 3.14 (invariant preservation).
One satisfied branch witnesses the predicate invariants. -/
theorem infinite_raw_complete [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : UnboundedClocked.Node.holds σ P α k (.predicate p)) :
    UnboundedClocked.CertifiedBranchSatisfied Bs σ P α k := by
  cases hr with
  | upperAlways c d b a φ hcd =>
      exact UnboundedClocked.upperAlways_complete_preserving σ P α k c d b a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ))))) hs
  | boundedAlways c d b q a φ hcd =>
      exact UnboundedClocked.boundedAlways_complete_preserving σ P α k c d b q a φ hcd
        (fun j => hst j φ (.neg (.until_right (.neg (.refl φ))))) hs
  | upperEventually c d b a φ hcd =>
      exact UnboundedClocked.upperEventually_complete_preserving σ P α k c d b a φ hcd hi
        (fun j => hst j φ (.until_right (.refl φ))) hs
  | boundedEventually c d b q a φ hcd =>
      exact UnboundedClocked.boundedEventually_complete_preserving σ P α k c d b q a φ hcd hi
        (fun j => hst j φ (.until_right (.refl φ))) hs

theorem infinite_branch_complete [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P (Λ.apply α) k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : UnboundedClocked.Node.holds σ P (Λ.apply α) k (.predicate p)) :
    ∃ (B : TransitionForm Clock Var) (Ψ : UnboundedClocked.Node Clock Var)
      (F : TransitionForm Clock Var),
      ConcreteInfinite.Branch (Predicate.ofUnbounded p) Λ B ∧
      Ψ ∈ Bs ∧ TransitionForm.normalize? (Judgement.ofUnbounded Ψ) = some F ∧
      B = F.underReset Λ ∧ B.holds σ P α k ∧
      UnboundedClocked.EvaluatedInvariant σ P (Λ.apply α) k Ψ ∧
      (Judgement.ofUnbounded Ψ).UnderlyingStable σ P := by
  obtain ⟨Ψ, hΨ, hsΨ, hiΨ⟩ := infinite_raw_complete hr σ P (Λ.apply α) k hi hst hs
  obtain ⟨F, hF, he⟩ := ConcreteInfinite.branch_normalization hr hΨ Λ
  exact ⟨F.underReset Λ, Ψ, F,
    ⟨p, Bs, Ψ, F, rfl, hr, hΨ, hF, rfl⟩, hΨ, hF, rfl,
    (he σ P α k).2 hsΨ, hiΨ,
    GeneratorStability.infinite_branch_stable hr hΨ σ P hst⟩

/-- Infinite opening also selects one actual normalized branch and establishes
its entire invariant at the reset valuation. -/
theorem opening_branch_complete [DecidableEq Clock]
    (c : Clock) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (Λ : ClockResetSet Clock) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hst : σ.StablePartition (UnboundedClocked.formula kind a φ) P)
    (hs : UnboundedClocked.Node.holds σ P (Λ.apply α) k
      (.plain (UnboundedClocked.formula kind a φ))) :
    ∃ (B : TransitionForm Clock Var) (m : Marker) (F : TransitionForm Clock Var),
      ConcreteOpening.Branch (.plain (UnboundedClocked.formula kind a φ)) Λ B ∧
      TransitionForm.normalize?
        (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) = some F ∧
      B = F.underReset Λ ∧ B.holds σ P α k ∧
      UnboundedClocked.EvaluatedInvariant σ P (Λ.apply α) k
        (UnboundedClocked.opening c m kind a φ) ∧
      (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)).UnderlyingStable σ P := by
  obtain ⟨m, hm⟩ := (UnboundedClocked.opening_correct σ P (Λ.apply α) k c kind a φ).1 hs
  obtain ⟨F, hF, he⟩ := ConcreteInfinite.opening_normalization c m kind a φ Λ
  exact ⟨F.underReset Λ, m, F, ⟨c, m, kind, a, φ, F, rfl, hF, rfl⟩,
    hF, rfl, (he σ P α k).2 hm,
    UnboundedClocked.opening_preserves σ P (Λ.apply α) k c m kind a φ hm,
    GeneratorStability.opening_branch_stable c m kind a φ σ P hst⟩


/-- The local finite witness in the faithful normalized transition model. -/
theorem finite_normalized_complete [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, STLTableau.Invariant σ P (Λ.apply α) k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : STLTableau.satisfies σ P (Λ.apply α) k (.predicate p)) :
    ∃ B, ConcreteFinite.Branch (Predicate.ofFinite p) Λ B ∧ B.holds σ P α k ∧
      B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B, raw, F, hb, hm, hn, rfl, hsat, hinv, hstable⟩ :=
    finite_branch_complete hr Λ σ P α k hi hst hs
  obtain ⟨G, hG, hGI⟩ := ConcreteFinite.branch_invariant_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  refine ⟨F.underReset Λ, hb, hsat, (hGI σ P α k).2 hinv, ?_⟩
  change F.UnderlyingStable σ P
  exact (TransitionForm.normalize_underlyingStable _ hn σ P).2 hstable

theorem infinite_normalized_complete [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P (Λ.apply α) k hk p)
    (hst : σ.StablePartition p.formula P)
    (hs : UnboundedClocked.Node.holds σ P (Λ.apply α) k (.predicate p)) :
    ∃ B, ConcreteInfinite.Branch (Predicate.ofUnbounded p) Λ B ∧ B.holds σ P α k ∧
      B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B, raw, F, hb, hm, hn, rfl, hsat, hinv, hstable⟩ :=
    infinite_branch_complete hr Λ σ P α k hi hst hs
  obtain ⟨G, hG, hGI⟩ := ConcreteInfinite.branch_invariant_normalization hr hm Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  refine ⟨F.underReset Λ, hb, hsat, (hGI σ P α k).2 hinv, ?_⟩
  change F.UnderlyingStable σ P
  exact (TransitionForm.normalize_underlyingStable _ hn σ P).2 hstable

theorem opening_normalized_complete [DecidableEq Clock]
    (c : Clock) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (Λ : ClockResetSet Clock) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hst : σ.StablePartition (UnboundedClocked.formula kind a φ) P)
    (hs : UnboundedClocked.Node.holds σ P (Λ.apply α) k
      (.plain (UnboundedClocked.formula kind a φ))) :
    ∃ B, ConcreteOpening.Branch (.plain (UnboundedClocked.formula kind a φ)) Λ B ∧
      B.holds σ P α k ∧ B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B, m, F, hb, hn, rfl, hsat, hinv, hstable⟩ :=
    opening_branch_complete c kind a φ Λ σ P α k hst hs
  obtain ⟨G, hG, hGI⟩ := ConcreteInfinite.opening_invariant_normalization c m kind a φ Λ
  have he : G = F := Option.some.inj (hG.symm.trans hn)
  subst G
  refine ⟨F.underReset Λ, hb, hsat, (hGI σ P α k).2 hinv, ?_⟩
  change F.UnderlyingStable σ P
  exact (TransitionForm.normalize_underlyingStable _ hn σ P).2 hstable

/-- A source with an expansion rule admits a satisfied raw
branch. Unsupported syntax needs no artificial admissibility assumption. -/
theorem mixed_raw_complete [DecidableEq Clock] (p : Predicate Clock Var)
    (hbranch : ∃ B, ConcreteMixed.catalogue.Branch p ClockResetSet.empty B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ B, ConcreteMixed.catalogue.Branch p ClockResetSet.empty B ∧ B.holds σ P α k ∧
      B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B, hb⟩ := hbranch
  rcases hb with h | h | h
  · obtain ⟨p₀, R, raw, F, rfl, hr, hm, hn, hB⟩ := h
    have hi₀ : ∀ hk : k.1 < P.size, STLTableau.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hs₀ : STLTableau.satisfies σ P α k (.predicate p₀) :=
      (Judgement.holds_ofFinite σ P α k (.predicate p₀)).1 hs
    obtain ⟨C, hc, hsat, hInv, hStable⟩ := finite_normalized_complete hr ClockResetSet.empty
      σ P α k (by simpa only [ClockResetSet.apply_empty] using hi₀)
      (by simpa only [Predicate.formula_ofFinite] using hst)
      (by simpa only [ClockResetSet.apply_empty] using hs₀)
    exact ⟨C, Or.inl hc, hsat, hInv, hStable⟩
  · obtain ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, hB⟩ := h
    have hi₀ : ∀ hk : k.1 < P.size, UnboundedClocked.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hs₀ : UnboundedClocked.Node.holds σ P α k (.predicate p₀) :=
      (Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).1 hs
    obtain ⟨C, hc, hsat, hInv, hStable⟩ := infinite_normalized_complete hr ClockResetSet.empty
      σ P α k (by simpa only [ClockResetSet.apply_empty] using hi₀)
      (by simpa only [Predicate.formula_ofUnbounded] using hst)
      (by simpa only [ClockResetSet.apply_empty] using hs₀)
    exact ⟨C, Or.inr (Or.inl hc), hsat, hInv, hStable⟩
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, hB⟩ := h
    have hs₀ : UnboundedClocked.Node.holds σ P α k
        (.plain (UnboundedClocked.formula kind a φ)) :=
      (Judgement.holds_ofUnbounded σ P α k (.plain _)).1 hs
    obtain ⟨C, hc, hsat, hInv, hStable⟩ := opening_normalized_complete c kind a φ
      ClockResetSet.empty σ P α k hst
      (by simpa only [ClockResetSet.apply_empty] using hs₀)
    exact ⟨C, Or.inr (Or.inr hc), hsat, hInv, hStable⟩

/-- A concrete decreasing closure step. Neither closure existence nor a
compatibility choice is a premise. -/
theorem preserving_step [DecidableEq Clock] [Infinite Clock]
    (S : StateForm Clock Var) (Φ : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hext : SyntacticallySubsumed (TransitionForm.ofState S) Φ)
    (hs : Φ.holds σ P α k) (hi : Φ.EvaluatedInvariant σ P α k)
    (hst : Φ.UnderlyingStable σ P)
    (hc : ¬ ConcreteContextual.catalogue.IsClosed Φ) :
    ∃ U, SyntacticallySubsumed (TransitionForm.ofState S) U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P ∧
      rank ConcreteContextual.catalogue U < rank ConcreteContextual.catalogue Φ := by
  classical
  obtain ⟨p, hp, hopen⟩ : ∃ p, Local.predicate p ∈ Φ.current.locals ∧
      ¬ ConcreteContextual.catalogue.RuleClosedFor Φ p := by
    obtain ⟨p, hp⟩ := not_forall.mp hc
    exact ⟨p, (Classical.not_imp.mp hp).1, (Classical.not_imp.mp hp).2⟩
  have hex : ∃ B, ConcreteContextual.catalogue.Branch p Φ.current.resets B := by
    by_contra hn
    exact hopen (Or.inl hn)
  obtain ⟨B, R, A, hR, ha, hB⟩ := hex
  have hip : ∀ hk : k.1 < P.size, p.Invariant σ P (Φ.current.resets.apply α) k hk :=
    hi.1 (.predicate p) hp
  have hsp : Judgement.holds σ P (Φ.current.resets.apply α) k (.predicate p) :=
    hs.1.2 (.predicate p) hp
  have hstp : σ.StablePartition p.formula P := hst _ (Or.inl ⟨p, hp, rfl⟩)
  obtain ⟨F, hF, hFs, hFi, hFst⟩ := mixed_raw_complete p ⟨R, hR⟩ σ P
    (Φ.current.resets.apply α) k hip hstp hsp
  obtain ⟨e, Fa, hfix, hFa, hcompat, hsat, hInv⟩ :=
    TransitionForm.contextual_satisfied_union Φ F (FaithfulClosure.mixed_branch_currentGuards_empty hF)
      σ P α k hs hFs hi hFi
  let U := (Φ.alphaNext e).union (Fa.underReset Φ.current.resets)
  have hanchor : SyntacticallySubsumed (TransitionForm.ofState S) (Φ.alphaNext e) :=
    ⟨hext.current, hext.outerFresh, by intro N hn; cases hn⟩
  have hFaBranch : ConcreteContextual.catalogue.Branch p
      (Φ.alphaNext e).current.resets (Fa.underReset Φ.current.resets) :=
    ⟨F, Fa, hF, hFa, rfl⟩
  have hstableSource : (Φ.alphaNext e).UnderlyingStable σ P :=
    ((TransitionForm.AlphaEquivalent.next Φ e hfix).underlyingStable σ P).2 hst
  have hstableBranch : (Fa.underReset Φ.current.resets).UnderlyingStable σ P :=
    (hFa.underlyingStable σ P).2 hFst
  refine ⟨U, hanchor.trans hcompat.left, hsat, hInv, ?_, ?_⟩
  · intro ψ hψ
    rw [TransitionForm.underlyingFormulas_union] at hψ
    exact hψ.elim (hstableSource ψ) (hstableBranch ψ)
  · have hdecrease := ConcreteContextual.union_rank_decrease (Φ.alphaNext e)
      (Fa.underReset Φ.current.resets) p hp
      (fun h => hopen ((ConcreteContextual.ruleClosed_alphaNext_iff Φ e hfix p).1 h))
      hFaBranch hcompat
    rwa [ConcreteContextual.rank_alphaNext Φ e hfix] at hdecrease

/-- State-form case of Theorem 4.22 (closure completeness). A satisfied
generator has a satisfied minimal closure with the predicate invariants
and stability in both the current and next components. -/
theorem satisfied_closure_exists [DecidableEq Clock] [Infinite Clock]
    (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : S.holds σ P α k) (hi : S.EvaluatedInvariant σ P α k)
    (hst : S.UnderlyingStable σ P) :
    ∃ U, ConcreteContextual.catalogue.IsClosure (TransitionForm.ofState S) U ∧
      U.holds σ P α k ∧ U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  let anchor := TransitionForm.ofState S
  let Q := fun U : TransitionForm Clock Var =>
    SyntacticallySubsumed anchor U ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P
  have hq : Q anchor :=
    ⟨.refl anchor, ⟨hs, trivial⟩, ⟨hi, by intro N hn; cases hn⟩,
      by simpa only [anchor, TransitionForm.UnderlyingStable,
        TransitionForm.underlyingFormulas_ofState, StateForm.UnderlyingStable] using hst⟩
  have hstep : ∀ U, Q U → ¬ ConcreteContextual.catalogue.IsClosed U →
      ∃ V, Q V ∧ rank ConcreteContextual.catalogue V < rank ConcreteContextual.catalogue U := by
    intro U hU hc
    obtain ⟨V, hext, hsat, hInv, hStable, hRank⟩ :=
      preserving_step S U σ P α k hU.1 hU.2.1 hU.2.2.1 hU.2.2.2 hc
    exact ⟨V, ⟨hext, hsat, hInv, hStable⟩, hRank⟩
  have hdown : ∀ U V, SyntacticallySubsumed anchor V → SyntacticallySubsumed V U →
      Q U → Q V := by
    intro U V hAV hVU hU
    exact ⟨hAV, hVU.sound σ P α k hU.2.1,
      hVU.evaluatedInvariant σ P α k hU.2.2.1,
      hVU.underlyingStable σ P hU.2.2.2⟩
  obtain ⟨U, hc, hU⟩ := ConcreteContextual.catalogue.anchored_minimal_closure_of_decreasing_step
    (rank ConcreteContextual.catalogue) Q anchor (fun _ h => h.1) hstep anchor hq hdown
  exact ⟨U, hc, hU.2⟩

end FaithfulClosure
end STLTableau.Section3
