import STLTableaux.Closure.Normalization.FaithfulAlphaInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm

theorem nextResets_subset_bound {Φ : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hn : Φ.nextPart = some N) : N.resets.clocks ⊆ Φ.boundClocks := by
  intro c hc; exact Or.inr (by simpa [boundClocks,hn] using hc)

theorem nextLocalClocks_subset_all {Φ : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hn : Φ.nextPart = some N) : N.localClocks ⊆ Φ.allClocks := by
  intro c hc
  by_cases hN : c ∈ N.resets.clocks
  · exact Or.inr (nextResets_subset_bound hn hN)
  · by_cases hΦ : c ∈ Φ.current.resets.clocks
    · exact Or.inr (Or.inl hΦ)
    · have hb : c ∈ Φ.bodyFreeClocks := by
        unfold bodyFreeClocks
        rw [hn]
        exact Or.inr (Or.inr ⟨hc,hN⟩)
      exact Or.inl (Or.inr ⟨hb,hΦ⟩)

structure UnionCompatible (Φ Ψ : TransitionForm Clock Var) : Prop where
  left : SyntacticallySubsumed Φ (Φ.union Ψ)
  right : SyntacticallySubsumed Ψ (Φ.union Ψ)

private theorem components_union_left (S T : StateForm Clock Var) :
    ComponentsIncluded S (S.union T) :=
  ⟨Set.subset_union_left,ClockResetSet.subset_union_left _ _,Set.subset_union_left⟩
private theorem components_union_right (S T : StateForm Clock Var)
    (h : S.resets.Consistent T.resets) : ComponentsIncluded T (S.union T) :=
  ⟨Set.subset_union_right,ClockResetSet.subset_union_right _ _ h,Set.subset_union_right⟩

theorem unionCompatible_of_boundFresh (Φ Ψ : TransitionForm Clock Var)
    (hleft : Disjoint Φ.boundClocks Ψ.allClocks)
    (hright : Disjoint Ψ.boundClocks Φ.allClocks) : Φ.UnionCompatible Ψ := by
  have hcur : Φ.current.resets.Consistent Ψ.current.resets :=
    ClockResetSet.consistent_of_disjoint
      (hleft.mono (fun _ h => Or.inl h) (fun _ h => Or.inr (Or.inl h)))
  refine ⟨⟨components_union_left _ _,?_,?_⟩,⟨components_union_right _ _ hcur,?_,?_⟩⟩
  · apply Set.disjoint_left.2
    intro c hc hf
    have hu : c ∈ Φ.current.resets.clocks ∪ Ψ.current.resets.clocks := by
      simpa only [union,StateForm.union,ClockResetSet.clocks_union] using hc
    rcases hu with hu | hu
    · exact hf.2 hu
    · exact Set.disjoint_left.1 hright (Or.inl hu) (Or.inl (Or.inr hf))
  · intro N hn
    cases hm : Ψ.nextPart with
    | none => exact ⟨N,by simp [union,unionNext,hn,hm],
        ⟨fun _ h => h,fun _ _ h => h,fun _ h => h⟩,
        Set.disjoint_left.2 (fun _ h f => f.2 h)⟩
    | some M =>
        refine ⟨N.union M,by simp [union,unionNext,hn,hm],components_union_left _ _,?_⟩
        apply Set.disjoint_left.2
        intro c hc hf
        have hu : c ∈ N.resets.clocks ∪ M.resets.clocks := by
          simpa [StateForm.union,ClockResetSet.clocks_union] using hc
        rcases hu with hu | hu
        · exact hf.2 hu
        · exact Set.disjoint_left.1 hright (nextResets_subset_bound hm hu)
            (nextLocalClocks_subset_all hn hf.1)
  · apply Set.disjoint_left.2
    intro c hc hf
    have hu : c ∈ Φ.current.resets.clocks ∪ Ψ.current.resets.clocks := by
      simpa only [union,StateForm.union,ClockResetSet.clocks_union] using hc
    rcases hu with hu | hu
    · exact Set.disjoint_left.1 hleft (Or.inl hu) (Or.inl (Or.inr hf))
    · exact hf.2 hu
  · intro M hm
    cases hn : Φ.nextPart with
    | none => exact ⟨M,by simp [union,unionNext,hn,hm],
        ⟨fun _ h => h,fun _ _ h => h,fun _ h => h⟩,
        Set.disjoint_left.2 (fun _ h f => f.2 h)⟩
    | some N =>
        have hcon : N.resets.Consistent M.resets :=
          ClockResetSet.consistent_of_disjoint
            (hleft.mono (nextResets_subset_bound hn)
              (fun _ h => Or.inr (nextResets_subset_bound hm h)))
        refine ⟨N.union M,by simp [union,unionNext,hn,hm],components_union_right _ _ hcon,?_⟩
        apply Set.disjoint_left.2
        intro c hc hf
        have hu : c ∈ N.resets.clocks ∪ M.resets.clocks := by
          simpa [StateForm.union,ClockResetSet.clocks_union] using hc
        rcases hu with hu | hu
        · exact Set.disjoint_left.1 hleft (nextResets_subset_bound hn hu)
            (nextLocalClocks_subset_all hm hf.1)
        · exact hf.2 hu

theorem exists_alpha_compatible_representatives [Infinite Clock] (Φ Ψ : TransitionForm Clock Var) :
    ∃ Φa Ψa, AlphaEquivalent Φa Φ ∧ AlphaEquivalent Ψa Ψ ∧ Φa.UnionCompatible Ψa := by
  obtain ⟨Φa,hΦ,hfreshΦ⟩ := Φ.exists_fresh_alpha Ψ.freeClocks Ψ.freeClocks_finite
  obtain ⟨Ψa,hΨ,hfreshΨ⟩ := Ψ.exists_fresh_alpha Φa.allClocks Φa.allClocks_finite
  refine ⟨Φa,Ψa,hΦ,hΨ,unionCompatible_of_boundFresh Φa Ψa ?_ hfreshΨ⟩
  apply Set.disjoint_left.2
  intro c hc hf
  rcases hf with hf | hf
  · exact Set.disjoint_left.1 hfreshΦ hc (by rwa [hΨ.freeClocks] at hf)
  · exact Set.disjoint_left.1 hfreshΨ hf (Or.inr hc)
end TransitionForm
end STLTableau.Section3
