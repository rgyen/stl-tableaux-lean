import STLTableaux.Closure.Catalogue.FaithfulFreshBranch

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm

theorem underReset_holds (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock)
    (hg : F.current.guards = ∅) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset Λ).holds σ P α k ↔ F.holds σ P (Λ.apply α) k := by
  simp only [underReset,holds,StateForm.holds,hg,Set.mem_empty_iff_false,
    IsEmpty.forall_iff,implies_true, true_and,ClockResetSet.apply_union_eq_comp]

theorem underReset_evaluatedInvariant (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.underReset Λ).EvaluatedInvariant σ P α k ↔
      F.EvaluatedInvariant σ P (Λ.apply α) k := by
  simp only [underReset,EvaluatedInvariant,StateForm.EvaluatedInvariant,
    ClockResetSet.apply_union_eq_comp]

theorem AlphaEquivalent.current_guards {F G : TransitionForm Clock Var}
    (h : AlphaEquivalent F G) : F.current.guards = G.current.guards := by
  induction h with
  | refl => rfl
  | outer => rfl
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

/-- Reset compatibility and the two literal no-capture tests suffice for
normal union. This form allows identical inherited enclosing assignments. -/
theorem unionCompatible_of_captureFree (Φ Ψ : TransitionForm Clock Var)
    (hcur : Φ.current.resets.Consistent Ψ.current.resets)
    (houterL : Disjoint Ψ.current.resets.clocks
      (Φ.bodyFreeClocks \ Φ.current.resets.clocks))
    (houterR : Disjoint Φ.current.resets.clocks
      (Ψ.bodyFreeClocks \ Ψ.current.resets.clocks))
    (hnL : ∀ N M, Φ.nextPart = some N → Ψ.nextPart = some M →
      Disjoint M.resets.clocks (N.localClocks \ N.resets.clocks))
    (hnR : ∀ N M, Φ.nextPart = some N → Ψ.nextPart = some M →
      Disjoint N.resets.clocks (M.localClocks \ M.resets.clocks))
    (hnCon : ∀ N M, Φ.nextPart = some N → Ψ.nextPart = some M →
      N.resets.Consistent M.resets) : Φ.UnionCompatible Ψ := by
  have hL : ComponentsIncluded Φ.current (Φ.union Ψ).current :=
    ⟨Set.subset_union_left,ClockResetSet.subset_union_left _ _,Set.subset_union_left⟩
  have hR : ComponentsIncluded Ψ.current (Φ.union Ψ).current :=
    ⟨Set.subset_union_right,ClockResetSet.subset_union_right _ _ hcur,Set.subset_union_right⟩
  refine ⟨⟨hL,?_,?_⟩,⟨hR,?_,?_⟩⟩
  · rw [show (Φ.union Ψ).current.resets.clocks =
        Φ.current.resets.clocks ∪ Ψ.current.resets.clocks from ClockResetSet.clocks_union _ _]
    exact (Set.disjoint_left.2 (fun _ hc hf => hf.2 hc)).union_left houterL
  · intro N hn
    cases hm : Ψ.nextPart with
    | none => exact ⟨N,by simp [union,unionNext,hn,hm],
        ⟨fun _ h => h,fun _ _ h => h,fun _ h => h⟩,
        Set.disjoint_left.2 (fun _ h f => f.2 h)⟩
    | some M =>
        refine ⟨N.union M,by simp [union,unionNext,hn,hm],
          ⟨Set.subset_union_left,ClockResetSet.subset_union_left _ _,Set.subset_union_left⟩,?_⟩
        change Disjoint (N.resets.union M.resets).clocks _
        rw [ClockResetSet.clocks_union]
        exact (Set.disjoint_left.2 (fun _ hc hf => hf.2 hc)).union_left (hnL N M hn hm)
  · rw [show (Φ.union Ψ).current.resets.clocks =
        Φ.current.resets.clocks ∪ Ψ.current.resets.clocks from ClockResetSet.clocks_union _ _]
    exact houterR.union_left (Set.disjoint_left.2 (fun _ hc hf => hf.2 hc))
  · intro M hm
    cases hn : Φ.nextPart with
    | none => exact ⟨M,by simp [union,unionNext,hn,hm],
        ⟨fun _ h => h,fun _ _ h => h,fun _ h => h⟩,
        Set.disjoint_left.2 (fun _ h f => f.2 h)⟩
    | some N =>
        refine ⟨N.union M,by simp [union,unionNext,hn,hm],
          ⟨Set.subset_union_right,ClockResetSet.subset_union_right _ _ (hnCon N M hn hm),
            Set.subset_union_right⟩,?_⟩
        change Disjoint (N.resets.union M.resets).clocks _
        rw [ClockResetSet.clocks_union]
        exact (hnR N M hn hm).union_left (Set.disjoint_left.2 (fun _ hc hf => hf.2 hc))
/-- Choose fresh representatives before adding the inherited outer reset.
The source current part is unchanged, and the inherited assignments are
retained literally rather than alpha-renamed. -/
theorem contextual_compatible_branch [Infinite Clock] (Φ F : TransitionForm Clock Var) :
    ∃ (e : Equiv.Perm Clock) (Fa : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      AlphaEquivalent Fa F ∧
      (Φ.alphaNext e).UnionCompatible (Fa.underReset Φ.current.resets) := by
  obtain ⟨e,hfix,hnextFresh⟩ := Φ.exists_fresh_next F.freeClocks F.freeClocks_finite
  let Φa := Φ.alphaNext e
  obtain ⟨Fa,hFa,hrawFresh⟩ := F.exists_fresh_alpha Φa.allClocks Φa.allClocks_finite
  have hsourceNext : ∀ N, Φa.nextPart = some N → Disjoint N.resets.clocks Fa.allClocks := by
    intro N hn
    apply Set.disjoint_left.2
    intro c hc hf
    rcases hf with hf | hf
    · exact Set.disjoint_left.1 (hnextFresh N hn) hc (by rwa [hFa.freeClocks] at hf)
    · exact Set.disjoint_left.1 hrawFresh hf (Or.inr (nextResets_subset_bound hn hc))
  have hrawCurrent : Disjoint Fa.current.resets.clocks Φ.current.resets.clocks :=
    hrawFresh.mono (fun _ h => Or.inl h) (fun _ h => Or.inr (Or.inl h))
  have hrawCon : Fa.current.resets.Consistent Φ.current.resets :=
    ClockResetSet.consistent_of_disjoint hrawCurrent
  have hcur : Φa.current.resets.Consistent (Fa.underReset Φ.current.resets).current.resets := by
    intro c a b ha hb
    have hi := ClockResetSet.subset_union_right Fa.current.resets Φ.current.resets hrawCon c a ha
    exact Option.some.inj (hi.symm.trans hb)
  refine ⟨e,Fa,hfix,hFa,unionCompatible_of_captureFree _ _ hcur ?_ ?_ ?_ ?_ ?_⟩
  · change Disjoint (Fa.current.resets.union Φ.current.resets).clocks _
    rw [ClockResetSet.clocks_union]
    apply Disjoint.union_left
    · apply Set.disjoint_left.2
      intro c hc hf
      exact Set.disjoint_left.1 hrawFresh (Or.inl hc) (Or.inl (Or.inr hf))
    · exact Set.disjoint_left.2 (fun _ hc hf => hf.2 hc)
  · apply Set.disjoint_left.2
    intro c hc hf
    exact hf.2 ((ClockResetSet.clocks_union _ _).symm ▸ Or.inr hc)
  · intro N M hn hm
    apply Set.disjoint_left.2
    intro c hc hf
    have hm' : Fa.nextPart = some M := hm
    exact Set.disjoint_left.1 hrawFresh (nextResets_subset_bound hm' hc)
      (nextLocalClocks_subset_all hn hf.1)
  · intro N M hn hm
    apply Set.disjoint_left.2
    intro c hc hf
    have hm' : Fa.nextPart = some M := hm
    exact Set.disjoint_left.1 (hsourceNext N hn) hc
      (nextLocalClocks_subset_all hm' hf.1)
  · intro N M hn hm
    apply ClockResetSet.consistent_of_disjoint
    exact (hsourceNext N hn).mono_right
      (fun _ hc => Or.inr (nextResets_subset_bound (show Fa.nextPart = some M from hm) hc))

/-- Full semantic and invariant gluing for a raw branch under its actual
inherited reset. No compatibility assumption is left to the caller. -/
theorem contextual_satisfied_union [Infinite Clock] (Φ F : TransitionForm Clock Var)
    (hg : F.current.guards = ∅) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hΦ : Φ.holds σ P α k) (hF : F.holds σ P (Φ.current.resets.apply α) k)
    (hiΦ : Φ.EvaluatedInvariant σ P α k)
    (hiF : F.EvaluatedInvariant σ P (Φ.current.resets.apply α) k) :
    ∃ (e : Equiv.Perm Clock) (Fa : TransitionForm Clock Var),
      (∀ N, Φ.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) ∧
      AlphaEquivalent Fa F ∧
      (Φ.alphaNext e).UnionCompatible (Fa.underReset Φ.current.resets) ∧
      ((Φ.alphaNext e).union (Fa.underReset Φ.current.resets)).holds σ P α k ∧
      ((Φ.alphaNext e).union (Fa.underReset Φ.current.resets)).EvaluatedInvariant σ P α k := by
  obtain ⟨e,Fa,hfix,hFa,hcon⟩ := contextual_compatible_branch Φ F
  have hΦa : AlphaEquivalent (Φ.alphaNext e) Φ := .next Φ e hfix
  have hFaG : Fa.current.guards = ∅ := hFa.current_guards.trans hg
  have hBa := (Fa.underReset_holds Φ.current.resets hFaG σ P α k).2
    ((hFa.holds σ P (Φ.current.resets.apply α) k).2 hF)
  have hiBa := (Fa.underReset_evaluatedInvariant Φ.current.resets σ P α k).2
    ((hFa.evaluatedInvariant σ P (Φ.current.resets.apply α) k).2 hiF)
  exact ⟨e,Fa,hfix,hFa,hcon,
    (hcon.holds σ P α k).2 ⟨(hΦa.holds σ P α k).2 hΦ,hBa⟩,
    hcon.evaluatedInvariant σ P α k ((hΦa.evaluatedInvariant σ P α k).2 hiΦ) hiBa⟩
end TransitionForm
end STLTableau.Section3
