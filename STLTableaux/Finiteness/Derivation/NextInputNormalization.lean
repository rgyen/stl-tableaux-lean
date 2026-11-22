import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Recover actual safe raw witnesses for next inputs. No encoding of arbitrary
empty state forms or neutral judgement is required. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Actual transition compatibility supplies compatibility of their two next
state forms, with their own local reset scopes. -/
theorem nextStates_compatible {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) {N M : Section3.StateForm Clock Var}
    (hn : F.nextPart = some N) (hm : G.nextPart = some M) :
    (Section3.TransitionForm.ofState N).UnionCompatible (.ofState M) := by
  obtain ⟨K,hK,hNK,hfreshN⟩ := h.left.next N hn
  obtain ⟨L,hL,hML,hfreshM⟩ := h.right.next M hm
  have he : K = L := Option.some.inj (hK.symm.trans hL)
  subst L
  have hcons : N.resets.Consistent M.resets := by
    intro c a b ha hb
    exact Option.some.inj ((hNK.resets c a ha).symm.trans (hML.resets c b hb))
  have hNM : Disjoint M.resets.clocks (N.localClocks \ N.resets.clocks) :=
    hfreshN.mono (by rintro c ⟨a,ha⟩; exact ⟨a,hML.resets c a ha⟩) Set.Subset.rfl
  have hMN : Disjoint N.resets.clocks (M.localClocks \ M.resets.clocks) :=
    hfreshM.mono (by rintro c ⟨a,ha⟩; exact ⟨a,hNK.resets c a ha⟩) Set.Subset.rfl
  apply Section3.TransitionForm.unionCompatible_of_captureFree
  · exact hcons
  · simpa only [Section3.TransitionForm.ofState,Section3.TransitionForm.bodyFreeClocks,
      Set.union_empty] using hNM
  · simpa only [Section3.TransitionForm.ofState,Section3.TransitionForm.bodyFreeClocks,
      Set.union_empty] using hMN
  · intro A B hA
    cases hA
  · intro A B hA
    cases hA
  · intro A B hA
    cases hA

/-- Every present next part of a safely normalized judgement has its own actual
safe raw input presentation. Conjunction uses precisely the next compatibility
in the given safety certificate. -/
theorem SafeNormalization.next_input {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N) :
    ∃ K, SafeNormalization K (.ofState N) := by
  induction h generalizing N with
  | terminal => cases hn
  | clock => cases hn
  | marker => cases hn
  | predicate => cases hn
  | @conj J K F G hJ hK hc ihJ ihK =>
    cases hF : F.nextPart with
    | none =>
      cases hG : G.nextPart with
      | none => simp [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hF,hG] at hn
      | some M =>
        have he : M = N := by
          simpa only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hF,hG,
            Option.some.injEq] using hn
        subst N
        exact ihK hG
    | some L =>
      cases hG : G.nextPart with
      | none =>
        have he : L = N := by
          simpa only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hF,hG,
            Option.some.injEq] using hn
        subst N
        exact ihJ hF
      | some M =>
        have he : L.union M = N := by
          simpa only [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hF,hG,
            Option.some.injEq] using hn
        subst N
        obtain ⟨A,hA⟩ := ihJ hF
        obtain ⟨B,hB⟩ := ihK hG
        exact ⟨.conj A B,.conj hA hB (nextStates_compatible hc hF hG)⟩
  | reset R h hd ih => exact ih hn
  | @next J F h hnone ih =>
    have he : F.current = N := Option.some.inj hn
    have hF : F = Section3.TransitionForm.ofState N := by
      cases F
      simp_all [Section3.TransitionForm.ofState]
    exact ⟨J,hF ▸ h⟩

end STLTableau.Section4.Finiteness
