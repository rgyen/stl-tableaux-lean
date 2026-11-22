import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Common inherited resets and actual syntactic union compatibility. Common
assignments may bind clocks in both bodies: no disjoint-all-support premise is
used. Guard independence is separate and needed only when interpreting a raw
enclosing reset through SafeNormalization, not for UnionCompatible itself. -/
namespace STLTableau.Section4.Finiteness.SharedResetCompatibility
open Section3
variable {Clock Var : Type*}

private theorem reset_ext {R S : ClockResetSet Clock} (h : R.value = S.value) : R = S := by
  cases R
  cases S
  cases h
  rfl

/-- Actual union compatibility implies consistency of its current reset maps. -/
theorem current_consistent {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) : F.current.resets.Consistent G.current.resets := by
  intro c a b ha hb
  have hr := h.right.current.resets c b hb
  have hl : (F.current.resets.union G.current.resets).value c = some a := by
    simp only [ClockResetSet.union,ha]
  exact Option.some.inj (hl.symm.trans hr)

theorem common_reset_consistent (A B R : ClockResetSet Clock)
    (hAB : A.Consistent B) (hAR : A.Consistent R) (hBR : B.Consistent R) :
    (A.union R).Consistent (B.union R) := by
  intro c a b ha hb
  cases hA : A.value c with
  | none =>
    change (match A.value c with | some v => some v | none => R.value c) = some a at ha
    rw [hA] at ha
    cases hB : B.value c with
    | none =>
      change (match B.value c with | some v => some v | none => R.value c) = some b at hb
      rw [hB] at hb
      exact Option.some.inj (ha.symm.trans hb)
    | some v =>
      have hvb : v = b := by simpa only [ClockResetSet.union,hB,Option.some.injEq] using hb
      exact (hBR c v a hB ha).symm.trans hvb
  | some v =>
    have hva : v = a := by simpa only [ClockResetSet.union,hA,Option.some.injEq] using ha
    cases hB : B.value c with
    | none =>
      change (match B.value c with | some w => some w | none => R.value c) = some b at hb
      rw [hB] at hb
      exact hva.symm.trans (hAR c v b hA hb)
    | some w =>
      have hwb : w = b := by simpa only [ClockResetSet.union,hB,Option.some.injEq] using hb
      exact hva.symm.trans ((hAB c v w hA hB).trans hwb)

/-- Only consistency of the new current reset maps is additionally required;
the existing capture and next-component clauses survive the common binder. -/
theorem underReset_compatible_of_current_consistent
    {F G : Section3.TransitionForm Clock Var} (h : F.UnionCompatible G) (R : ClockResetSet Clock)
    (hc : (F.current.resets.union R).Consistent (G.current.resets.union R)) :
    (F.underReset R).UnionCompatible (G.underReset R) := by
  refine ⟨⟨⟨h.left.current.guards,ClockResetSet.subset_union_left _ _,h.left.current.locals⟩,?_,h.left.next⟩,
    ⟨⟨h.right.current.guards,ClockResetSet.subset_union_right _ _ hc,h.right.current.locals⟩,?_,h.right.next⟩⟩
  · apply Set.disjoint_left.2
    intro c hc' hf
    have hfbody : c ∈ F.bodyFreeClocks := hf.1
    have hn : c ∉ F.current.resets.clocks ∪ R.clocks := by
      simpa only [Section3.TransitionForm.underReset,ClockResetSet.clocks_union] using hf.2
    have ht : (c ∈ F.current.resets.clocks ∨ c ∈ R.clocks) ∨
        c ∈ G.current.resets.clocks ∨ c ∈ R.clocks := by
      simpa only [Section3.TransitionForm.union,Section3.TransitionForm.underReset,
        Section3.StateForm.union,ClockResetSet.clocks_union,Set.mem_union] using hc'
    rcases ht with (hcF | hcR) | hcG | hcR
    · exact hn (Or.inl hcF)
    · exact hn (Or.inr hcR)
    · exact Set.disjoint_left.1 h.left.outerFresh
        (show c ∈ (F.union G).current.resets.clocks by
          rw [show (F.union G).current.resets.clocks = F.current.resets.clocks ∪ G.current.resets.clocks
            from ClockResetSet.clocks_union _ _]
          exact Or.inr hcG) ⟨hfbody,fun hcF => hn (Or.inl hcF)⟩
    · exact hn (Or.inr hcR)
  · apply Set.disjoint_left.2
    intro c hc' hf
    have hfbody : c ∈ G.bodyFreeClocks := hf.1
    have hn : c ∉ G.current.resets.clocks ∪ R.clocks := by
      simpa only [Section3.TransitionForm.underReset,ClockResetSet.clocks_union] using hf.2
    have ht : (c ∈ F.current.resets.clocks ∨ c ∈ R.clocks) ∨
        c ∈ G.current.resets.clocks ∨ c ∈ R.clocks := by
      simpa only [Section3.TransitionForm.union,Section3.TransitionForm.underReset,
        Section3.StateForm.union,ClockResetSet.clocks_union,Set.mem_union] using hc'
    rcases ht with (hcF | hcR) | hcG | hcR
    · exact Set.disjoint_left.1 h.right.outerFresh
        (show c ∈ (F.union G).current.resets.clocks by
          rw [show (F.union G).current.resets.clocks = F.current.resets.clocks ∪ G.current.resets.clocks
            from ClockResetSet.clocks_union _ _]
          exact Or.inl hcF) ⟨hfbody,fun hcG => hn (Or.inl hcG)⟩
    · exact hn (Or.inr hcR)
    · exact hn (Or.inl hcG)
    · exact hn (Or.inr hcR)

/-- A precise characterization: with old compatibility fixed, common inherited
reset preservation is equivalent to this purely numeric reset-graph condition. -/
theorem underReset_compatible_iff
    {F G : Section3.TransitionForm Clock Var} (h : F.UnionCompatible G) (R : ClockResetSet Clock) :
    (F.underReset R).UnionCompatible (G.underReset R) ↔
      (F.current.resets.union R).Consistent (G.current.resets.union R) :=
  ⟨fun hc => current_consistent hc,underReset_compatible_of_current_consistent h R⟩

/-- Readily usable sufficient conditions: the inherited reset agrees with each
child's introduced current assignments. Shared body-clock uses are allowed. -/
theorem underReset_compatible {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) (R : ClockResetSet Clock)
    (hFR : F.current.resets.Consistent R) (hGR : G.current.resets.Consistent R) :
    (F.underReset R).UnionCompatible (G.underReset R) :=
  underReset_compatible_of_current_consistent h R
    (common_reset_consistent _ _ _ (current_consistent h) hFR hGR)

/-- Fresh introduced current reset names are one way to obtain consistency;
inherited R may still bind clocks read by either child's body. -/
theorem underReset_compatible_of_fresh {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) (R : ClockResetSet Clock)
    (hF : Disjoint F.current.resets.clocks R.clocks)
    (hG : Disjoint G.current.resets.clocks R.clocks) :
    (F.underReset R).UnionCompatible (G.underReset R) :=
  underReset_compatible h R (ClockResetSet.consistent_of_disjoint hF)
    (ClockResetSet.consistent_of_disjoint hG)

/-- Distributing a common inherited reset over compatible forms retains the
same actual normalized syntax (including its reset graph and next component). -/
theorem reset_union_shared (A B R : ClockResetSet Clock) (hBR : B.Consistent R) :
    (A.union R).union (B.union R) = (A.union B).union R := by
  apply reset_ext
  funext c
  cases hA : A.value c with
  | some a => simp only [ClockResetSet.union,hA]
  | none =>
    simp only [ClockResetSet.union,hA]
    cases hB : B.value c with
    | none =>
      cases hR : R.value c <;> rfl
    | some b =>
      cases hR : R.value c with
      | none => rfl
      | some r =>
        have he := hBR c b r hB hR
        simp only [he]

theorem union_underReset (F G : Section3.TransitionForm Clock Var) (R : ClockResetSet Clock)
    (hGR : G.current.resets.Consistent R) :
    (F.underReset R).union (G.underReset R) = (F.union G).underReset R := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · rfl
    · exact reset_union_shared _ _ R hGR
    · rfl
  · rfl

/-- Assembly for raw children under one inherited reset. Compatibility is
proved above. Guard support independence is stated separately because it is
required to move an enclosing reset past current guards in raw syntax. -/
theorem safe_common_reset {J K : MixedJ Clock Var} {F G : Section3.TransitionForm Clock Var}
    (hJ : SafeNormalization J F) (hK : SafeNormalization K G) (hc : F.UnionCompatible G)
    (R : ClockResetSet Clock) (hGR : G.current.resets.Consistent R)
    (hgF : Disjoint R.clocks F.current.guardClocks) (hgG : Disjoint R.clocks G.current.guardClocks) :
    SafeNormalization (.reset R (.conj J K)) ((F.underReset R).union (G.underReset R)) := by
  rw [union_underReset F G R hGR]
  apply SafeNormalization.reset R (.conj hJ hK hc)
  apply Set.disjoint_left.2
  intro c hcR hcguard
  obtain ⟨g,hg,hgc⟩ := hcguard
  rcases hg with hg | hg
  · exact Set.disjoint_left.1 hgF hcR ⟨g,hg,hgc⟩
  · exact Set.disjoint_left.1 hgG hcR ⟨g,hg,hgc⟩

/-- The distributed raw reset presentation has the same certified normal form. -/
theorem safe_distributed_reset {J K : MixedJ Clock Var} {F G : Section3.TransitionForm Clock Var}
    (hJ : SafeNormalization J F) (hK : SafeNormalization K G) (hc : F.UnionCompatible G)
    (R : ClockResetSet Clock) (hFR : F.current.resets.Consistent R) (hGR : G.current.resets.Consistent R)
    (hgF : Disjoint R.clocks F.current.guardClocks) (hgG : Disjoint R.clocks G.current.guardClocks) :
    SafeNormalization (.conj (.reset R J) (.reset R K)) ((F.underReset R).union (G.underReset R)) :=
  .conj (.reset R hJ hgF) (.reset R hK hgG) (underReset_compatible hc R hFR hGR)

end STLTableau.Section4.Finiteness.SharedResetCompatibility
