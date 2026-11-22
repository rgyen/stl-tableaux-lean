import STLTableaux.Closure.Normalization.FaithfulUnionSemantics

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm
/-- Rename the clocks bound by the next reset while preserving the current
part and the next locals' free clocks. -/
theorem exists_fresh_next [Infinite Clock] (Φ : TransitionForm Clock Var)
    (U : Set Clock) (hU : U.Finite) :
    ∃ (e : Equiv.Perm Clock),
      (∀ N, Φ.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      ∀ N, (Φ.alphaNext e).nextPart = some N → Disjoint N.resets.clocks U := by
  cases hn : Φ.nextPart with
  | none => exact ⟨Equiv.refl _,by simp [hn],by simp [alphaNext,hn]⟩
  | some N =>
      obtain ⟨e,hfix,hfresh⟩ := STLTableau.exists_fresh_clock_permutation N.resets.clocks
        (N.localClocks \ N.resets.clocks) U N.resets.finite_domain
        N.localClocks_finite.sdiff hU (Set.disjoint_left.2 (fun _ hc hf => hf.2 hc))
      refine ⟨e,?_,?_⟩
      · intro M hm
        have he : M = N := Option.some.inj hm.symm
        subst M; exact hfix
      · intro M hm
        have he : M = N.alphaReset e := by simpa [alphaNext,hn] using hm.symm
        subst M
        simpa [StateForm.alphaReset,StateForm.rename] using hfresh

/-- A concrete branch inherits the source outer reset and has no current clock
 guards. Consequently only source next names need to move; the current part is
 literally unchanged. The side condition refers solely to finite syntactic
 supports and is supplied by actual branch normalization. -/
theorem compatible_branch_preserving_current [Infinite Clock] (Φ B : TransitionForm Clock Var)
    (hcurrent : Disjoint Φ.current.resets.clocks B.freeClocks) :
    ∃ (e : Equiv.Perm Clock) (Ba : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      AlphaEquivalent Ba B ∧ (Φ.alphaNext e).UnionCompatible Ba := by
  obtain ⟨e,hfix,hfresh⟩ := Φ.exists_fresh_next B.freeClocks B.freeClocks_finite
  let Φa := Φ.alphaNext e
  have hF : Disjoint Φa.boundClocks B.freeClocks := by
    apply Set.disjoint_left.2
    intro c hc hb
    rcases hc with hc | hc
    · exact Set.disjoint_left.1 hcurrent hc hb
    · cases hn : Φa.nextPart with
      | none => simpa [hn] using hc
      | some N => exact Set.disjoint_left.1 (hfresh N hn) (by simpa [hn] using hc) hb
  obtain ⟨Ba,hBa,hfreshBa⟩ := B.exists_fresh_alpha Φa.allClocks Φa.allClocks_finite
  refine ⟨e,Ba,hfix,hBa,unionCompatible_of_boundFresh Φa Ba ?_ hfreshBa⟩
  apply Set.disjoint_left.2
  intro c hc hb
  rcases hb with hb | hb
  · exact Set.disjoint_left.1 hF hc (by rwa [hBa.freeClocks] at hb)
  · exact Set.disjoint_left.1 hfreshBa hb (Or.inr hc)

/-- The compatible literal union simultaneously retains truth and the full
 scoped invariant; no semantic closure property is assumed. -/
theorem satisfied_fresh_branch_union [Infinite Clock] (Φ B : TransitionForm Clock Var)
    (hcurrent : Disjoint Φ.current.resets.clocks B.freeClocks)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hΦ : Φ.holds σ P α k) (hB : B.holds σ P α k)
    (hiΦ : Φ.EvaluatedInvariant σ P α k) (hiB : B.EvaluatedInvariant σ P α k) :
    ∃ (e : Equiv.Perm Clock) (Ba : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      AlphaEquivalent Ba B ∧ (Φ.alphaNext e).UnionCompatible Ba ∧
      ((Φ.alphaNext e).union Ba).holds σ P α k ∧
      ((Φ.alphaNext e).union Ba).EvaluatedInvariant σ P α k := by
  obtain ⟨e,Ba,hfix,hBa,hcon⟩ := Φ.compatible_branch_preserving_current B hcurrent
  have hFa : AlphaEquivalent (Φ.alphaNext e) Φ := .next Φ e hfix
  exact ⟨e,Ba,hfix,hBa,hcon,
    (hcon.holds σ P α k).2 ⟨(hFa.holds σ P α k).2 hΦ,(hBa.holds σ P α k).2 hB⟩,
    hcon.evaluatedInvariant σ P α k ((hFa.evaluatedInvariant σ P α k).2 hiΦ)
      ((hBa.evaluatedInvariant σ P α k).2 hiB)⟩
end TransitionForm
end STLTableau.Section3
