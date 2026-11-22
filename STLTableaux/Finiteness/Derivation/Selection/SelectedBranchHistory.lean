import STLTableaux.Finiteness.Derivation.Selection.SelectedBranch

/-! Concrete branch selection avoiding every name in a finite retained history.
The actual pending context is unchanged. This is one local branch selection,
not a resolution termination or bounded-path existence theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Choose rule parameters before selecting a preserving branch. Every newly
introduced reset name is the one explicitly chosen clock x. -/
theorem RawBranch.exists_preserving_fresh_at
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (x : Clock) (hx : x ∉ syntaxClocks Γ ∪ syntaxClocks (.predicate p))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ B, RawBranch p B ∧ FreshFor p B Γ ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      Judgement.holds σ P α k B ∧ B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨B,hB⟩ := RawBranch.exists_of_ready p hp hn
  cases hB with
  | @finite p₀ R rule B₀ _ =>
    obtain ⟨R',hr,hfresh⟩ := finite_fresh_rule_at rule Γ x hx
    have hi₀ : ∀ hk : k.val < P.size, STLTableau.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
    obtain ⟨C,hm,hC,hI⟩ := STLTableau.rule_complete_preserving hr σ P α k hi₀ hst₀
      ((Judgement.holds_ofFinite σ P α k (.predicate p₀)).1 hs)
    exact ⟨_,.finite hr hm,(hfresh C hm).1,(hfresh C hm).2,
      (Judgement.holds_ofFinite σ P α k C).2 hC,
      (Judgement.evaluatedInvariant_ofFinite σ P α k C).2 hI,
      GeneratorStability.finite_branch_stable hr hm σ P hst₀⟩
  | @infinite p₀ Bs rule B₀ _ =>
    obtain ⟨Bs',hr,hfresh⟩ := infinite_fresh_rule_at rule Γ x hx
    have hi₀ : ∀ hk : k.val < P.size, UnboundedClocked.Invariant σ P α k hk p₀ := by
      intro hk
      cases p₀ <;> exact hi hk
    have hst₀ : σ.StablePartition p₀.formula P := by simpa using hst
    obtain ⟨C,hm,hC,hI⟩ := UnboundedClocked.rule_complete_preserving hr σ P α k hi₀ hst₀
      ((Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).1 hs)
    exact ⟨_,.infinite hr hm,(hfresh C hm).1,(hfresh C hm).2,
      (Judgement.holds_ofUnbounded σ P α k C).2 hC,
      (Judgement.evaluatedInvariant_ofUnbounded σ P α k C).2 hI,
      GeneratorStability.infinite_branch_stable hr hm σ P hst₀⟩
  | opening c m kind a φ =>
    obtain ⟨m',hm⟩ := (UnboundedClocked.opening_correct σ P α k x kind a φ).1
      ((Judgement.holds_ofUnbounded σ P α k (.plain _)).1 hs)
    have hxΓ : x ∉ syntaxClocks Γ := fun h => hx (Or.inl h)
    have hfresh : FreshFor (.plain (UnboundedClocked.formula kind a φ))
        (Judgement.ofUnbounded (UnboundedClocked.opening x m' kind a φ)) Γ := by
      simpa [FreshFor,resetNames,syntaxClocks,Judgement.ofUnbounded,
        UnboundedClocked.opening,Set.disjoint_left] using hxΓ
    have hreset : resetNames (Judgement.ofUnbounded (UnboundedClocked.opening x m' kind a φ)) ⊆
        syntaxClocks (.predicate (.plain (UnboundedClocked.formula kind a φ))) ∪ {x} := by
      simp [resetNames,syntaxClocks,Judgement.ofUnbounded,UnboundedClocked.opening]
    exact ⟨_,.opening x m' kind a φ,hfresh,hreset,
      (Judgement.holds_ofUnbounded σ P α k _).2 hm,
      (Judgement.evaluatedInvariant_ofUnbounded σ P α k _).2
        (UnboundedClocked.opening_preserves σ P α k x m' kind a φ hm),
      GeneratorStability.opening_branch_stable x m' kind a φ σ P hst⟩

/-- Actual branch selection with finite forbidden history. No auxiliary guards
or dummy context are inserted: FreshFor refers to the original Γ literally. -/
theorem RawBranch.exists_preserving_history
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (W : Set Clock) (hW : W.Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ (x : Clock) (B : MixedJ Clock Var),
      x ∉ W ∪ syntaxClocks Γ ∪ syntaxClocks (.predicate p) ∧
      RawBranch p B ∧ FreshFor p B Γ ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      Disjoint (resetNames B \ syntaxClocks (.predicate p)) W ∧
      Judgement.holds σ P α k B ∧ B.EvaluatedInvariant σ P α k ∧ B.UnderlyingStable σ P := by
  obtain ⟨x,hx⟩ := ((hW.union (syntaxClocks_finite Γ)).union
    (syntaxClocks_finite (.predicate p))).exists_notMem
  have hx₀ : x ∉ syntaxClocks Γ ∪ syntaxClocks (.predicate p) := by
    rintro (hΓ | hp)
    · exact hx (Or.inl (Or.inr hΓ))
    · exact hx (Or.inr hp)
  obtain ⟨B,hB,hfresh,hreset,htrue,hfull,hstable⟩ :=
    RawBranch.exists_preserving_fresh_at p hp hn Γ x hx₀ σ P α k hi hst hs
  have hhistory : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W := by
    apply Set.disjoint_left.2
    intro d hd hdW
    rcases hreset hd.1 with hsource | hnew
    · exact hd.2 hsource
    · have he : d = x := hnew
      subst d
      exact hx (Or.inl (Or.inl hdW))
  exact ⟨x,B,hx,hB,hfresh,hreset,hhistory,htrue,hfull,hstable⟩

/-- Normalize a branch whose new clocks avoid the given history, preserving
predicate invariants and the stability of the underlying formulas. -/
theorem exists_selected_branch_history
    (p : Predicate Clock Var) (hp : p.Ready) (hn : ¬ p.IsAtomic) (Γ : MixedJ Clock Var)
    (W : Set Clock) (hW : W.Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.val < P.size, p.Invariant σ P α k hk)
    (hst : σ.StablePartition p.formula P)
    (hs : Judgement.holds σ P α k (.predicate p)) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (F : Section3.TransitionForm Clock Var),
      x ∉ W ∪ syntaxClocks Γ ∪ syntaxClocks (.predicate p) ∧
      RawBranch p B ∧ FreshFor p B Γ ∧
      resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x} ∧
      Disjoint (resetNames B \ syntaxClocks (.predicate p)) W ∧
      SafeNormalization B F ∧ F.current.guards = ∅ ∧
      F.holds σ P α k ∧ F.EvaluatedInvariant σ P α k ∧ F.UnderlyingStable σ P := by
  obtain ⟨x,B,hx,hB,hfresh,hreset,hhistory,htrue,hfull,hstable⟩ :=
    RawBranch.exists_preserving_history p hp hn Γ W hW σ P α k hi hst hs
  obtain ⟨F,hsafe,hguards⟩ := hB.safe_normalization
  exact ⟨x,B,F,hx,hB,hfresh,hreset,hhistory,hsafe,hguards,(hsafe.holds σ P α k).2 htrue,
    (hB.invariant_normalization hsafe.normalizes σ P α k).2 hfull,
    (Section3.TransitionForm.normalize_underlyingStable B hsafe.normalizes σ P).2 hstable⟩

end STLTableau.Section4.Finiteness
