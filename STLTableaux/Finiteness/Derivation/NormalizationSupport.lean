import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! The actual syntactic normalizer introduces no clock names. The support
includes current and next guards, locals and reset bindings. Disjoint raw
support therefore gives genuine normalized capture-free union compatibility. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

namespace NormalizationSupport

private theorem empty_clocks : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
  ext c
  constructor
  · rintro ⟨a,ha⟩
    cases ha
  · intro h
    cases h

private def stateSupport (S : Section3.StateForm Clock Var) : Set Clock :=
  S.guardClocks ∪ S.localClocks ∪ S.resets.clocks

private theorem allClocks_flat (F : Section3.TransitionForm Clock Var) :
    F.allClocks = stateSupport F.current ∪
      match F.nextPart with | none => ∅ | some N => stateSupport N := by
  ext c
  cases hn : F.nextPart <;>
    simp only [Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.TransitionForm.boundClocks,
      Section3.StateForm.freeClocks,stateSupport,hn,Set.mem_union,Set.mem_sdiff,Set.mem_empty_iff_false] <;> tauto

private theorem stateSupport_union (S T : Section3.StateForm Clock Var) :
    stateSupport (S.union T) = stateSupport S ∪ stateSupport T := by
  ext c
  simp only [stateSupport,Section3.StateForm.union,Section3.StateForm.guardClocks,
    Section3.StateForm.localClocks,ClockResetSet.clocks_union,Set.mem_union,Set.mem_setOf_eq]
  aesop

theorem allClocks_union (F G : Section3.TransitionForm Clock Var) :
    (F.union G).allClocks = F.allClocks ∪ G.allClocks := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp only [allClocks_flat,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      hf,hg,stateSupport_union] <;> ext c <;>
    simp only [Set.mem_union,Set.mem_empty_iff_false] <;> tauto

theorem allClocks_underReset (F : Section3.TransitionForm Clock Var) (R : ClockResetSet Clock) :
    (F.underReset R).allClocks = F.allClocks ∪ R.clocks := by
  cases hn : F.nextPart <;> ext c <;>
    simp only [allClocks_flat,Section3.TransitionForm.underReset,stateSupport,hn,
      ClockResetSet.clocks_union,Set.mem_union,Set.mem_empty_iff_false] <;> tauto

theorem allClocks_ofNext (F : Section3.TransitionForm Clock Var) (hn : F.nextPart = none) :
    (Section3.TransitionForm.ofNextState F.current).allClocks = F.allClocks := by
  simp only [allClocks_flat,Section3.TransitionForm.ofNextState,hn,stateSupport,
    Section3.StateForm.empty,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
    empty_clocks,Set.mem_empty_iff_false,false_and,exists_false,
    Set.setOf_false,Set.empty_union,Set.union_empty]

end NormalizationSupport

/-- Every name in the actual safe normal form occurs in the raw syntax.
No separate name-bound or normalization support premise is assumed. -/
theorem SafeNormalization.allClocks_subset_syntax
    {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.allClocks ⊆ syntaxClocks J := by
  induction h with
  | terminal =>
    simp [NormalizationSupport.allClocks_flat,NormalizationSupport.stateSupport,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Section3.Local.freeClocks,Section3.Local.toJudgement,Section3.Judgement.freeClocks,NormalizationSupport.empty_clocks,syntaxClocks]
  | clock c r a =>
    simp [NormalizationSupport.allClocks_flat,NormalizationSupport.stateSupport,
      Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,NormalizationSupport.empty_clocks,syntaxClocks]
  | marker m =>
    simp [NormalizationSupport.allClocks_flat,NormalizationSupport.stateSupport,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Section3.Local.freeClocks,Section3.Local.toJudgement,Section3.Judgement.freeClocks,NormalizationSupport.empty_clocks,syntaxClocks]
  | predicate p =>
    cases p <;> simp [NormalizationSupport.allClocks_flat,NormalizationSupport.stateSupport,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Section3.Local.freeClocks,Section3.Local.toJudgement,Section3.Judgement.freeClocks,NormalizationSupport.empty_clocks,syntaxClocks]
    exact fun _ hc => hc
  | conj h g hc ih ig =>
    rw [NormalizationSupport.allClocks_union]
    exact Set.union_subset_union ih ig
  | reset R h hd ih =>
    rw [NormalizationSupport.allClocks_underReset]
    intro c hc
    rcases hc with hc | hc
    · exact Or.inr (ih hc)
    · exact Or.inl hc
  | next h hn ih =>
    rw [NormalizationSupport.allClocks_ofNext _ hn]
    exact ih

namespace NormalizationSupport

/-- Whole-syntax disjointness yields actual normalized union compatibility.
For a common inherited reset, combine this with SharedResetCompatibility;
there is no demand that the inherited body's own clocks be globally fresh. -/
theorem unionCompatible_of_disjoint_syntax
    {J K : MixedJ Clock Var} {F G : Section3.TransitionForm Clock Var}
    (hF : SafeNormalization J F) (hG : SafeNormalization K G)
    (hd : Disjoint (syntaxClocks J) (syntaxClocks K)) : F.UnionCompatible G := by
  have hnorm : Disjoint F.allClocks G.allClocks :=
    hd.mono hF.allClocks_subset_syntax hG.allClocks_subset_syntax
  apply Section3.TransitionForm.unionCompatible_of_boundFresh F G
  · exact hnorm.mono_left (fun _ hc => Or.inr hc)
  · exact hnorm.symm.mono_left (fun _ hc => Or.inr hc)

end NormalizationSupport
end STLTableau.Section4.Finiteness
