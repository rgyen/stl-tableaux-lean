import STLTableaux.Finiteness.Derivation.DerivationRelation

/-! A concrete resolved boundary edge, constructed with actual safety proofs.
It witnesses admission of the new boundary operation, not bounded completeness. -/
namespace STLTableau.Section4.Finiteness.BoundaryExample
open Section3
open scoped STL
variable {Var : Type*}

private def bounded (I : BoundedTimeInterval) (φ : Formula Var) : Predicate Nat Var :=
  .bounded 0 1 .closed .open .always (.bounded I) φ
private def upper (I : BoundedTimeInterval) (φ : Formula Var) : Predicate Nat Var :=
  .upper 0 .closed .always (.bounded I) φ
private def successor (I : BoundedTimeInterval) (φ : Formula Var) : MixedJ Nat Var :=
  .conj (.clock 0 .le ⟨I.lower,I.lower_nonnegative⟩)
    (.reset (ClockResetSet.singleton 2 0)
      (.conj (.predicate (.bounded 0 2 .closed .open .always (.bounded I) φ)) (.marker .closed)))

def input (I : BoundedTimeInterval) (φ : Formula Var) : MixedJ Nat Var :=
  .reset (ClockResetSet.singleton 1 0)
    (.conj (.predicate (bounded I φ)) (.conj (.marker .closed) (.marker .closed)))

def full (I : BoundedTimeInterval) (φ : Formula Var) : MixedJ Nat Var :=
  .conj (.conj (.predicate (upper I φ)) (.next (successor I φ)))
    (.conj (.marker .closed) (.marker .closed))

def erased (I : BoundedTimeInterval) (φ : Formula Var) : MixedJ Nat Var :=
  .conj (.next (successor I φ)) (.conj (.marker .closed) (.marker .closed))

private theorem safe_conj {J K : MixedJ Nat Var} {F G : Section3.TransitionForm Nat Var}
    (hJ : SafeNormalization J F) (hK : SafeNormalization K G)
    (hl : Disjoint F.boundClocks G.allClocks)
    (hr : Disjoint G.boundClocks F.allClocks) : SafeNormalization (.conj J K) (F.union G) :=
  .conj hJ hK (Section3.TransitionForm.unionCompatible_of_boundFresh F G hl hr)

private def resolve (I : BoundedTimeInterval) (φ : Formula Var) :
    Resolve (input I φ) (full I φ) (erased I φ) := by
  have raw : RawBranch (upper I φ) (.next (successor I φ)) := by
    have hm : ExpansionRule.upperAlways_defer 0 2 .closed .closed I φ ∈
        (ExpansionRule.upperAlways 0 2 .closed I φ).branches := by simp [ExpansionRule.upperAlways]
    have h := RawBranch.finite (STLTableau.ConcreteRule.upperAlways 0 2 .closed I φ (by decide)) hm
    simpa [upper,successor,Section3.Predicate.ofFinite,Section3.Judgement.ofFinite,
      ExpansionRule.upperAlways_defer,Marker.imp,STLTableau.Judgement.markedLT] using h
  have next : Resolve (.next (successor I φ)) (.next (successor I φ))
      (.next (successor I φ)) := .leaf (.next _)
  have up := Resolve.expandSolo raw (by simp [upper,Predicate.IsAtomic]) (by
    simp [FreshWithoutContext,resetNames,syntaxClocks,successor,upper,
      ClockResetSet.clocks,ClockResetSet.singleton,Set.disjoint_left]) next
  apply Resolve.boundaryOptional (FrozenByUpper.defer 0 1 .closed .closed .always
    (.bounded I) φ (by decide)) (by
      simp [Section3.Judgement.freeClocks])
  exact Resolve.conj up (.conj (.leaf (.marker .closed)) (.leaf (.marker .closed)))

set_option linter.unusedSimpArgs false in
/-- The safety certificates are constructed, including next guards and both
private right-reset names. The result uses the resolved constructor. -/
theorem boundary_resolved (I : BoundedTimeInterval) (φ : Formula Var) :
    ∃ (N : Section3.StateForm Nat Var) (F : Section3.TransitionForm Nat Var),
      SafeNormalization (input I φ) (.ofState N) ∧
      SafeNormalization (full I φ) F ∧
      SafeNormalization (erased I φ) F.atomicProjection ∧ Derives N F := by
  let M : Section3.TransitionForm Nat Var := .ofState (.ofLocal (.marker .closed))
  have hM : SafeNormalization (.marker .closed) M := .marker _
  have hMM := safe_conj hM hM (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,ClockResetSet.clocks,ClockResetSet.empty]) (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,ClockResetSet.clocks,ClockResetSet.empty])
  let B : Section3.TransitionForm Nat Var := .ofState (.ofLocal
    (.predicate (.bounded 0 2 .closed .open .always (.bounded I) φ)))
  have hB : SafeNormalization (.predicate (.bounded 0 2 .closed .open .always (.bounded I) φ)) B := .predicate _
  have hBM := safe_conj hB hM (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, B,Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,ClockResetSet.clocks,ClockResetSet.empty]) (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,ClockResetSet.clocks,ClockResetSet.empty])
  have hR := SafeNormalization.reset (ClockResetSet.singleton 2 0) hBM (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, B,M,Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.guardClocks])
  have hC : SafeNormalization (.clock 0 .le ⟨I.lower,I.lower_nonnegative⟩)
      (.ofState (.ofGuard ⟨0,.le,⟨I.lower,I.lower_nonnegative⟩⟩) : Section3.TransitionForm Nat Var) := .clock _ _ _
  have hS := safe_conj hC hR (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,
      Section3.StateForm.ofGuard,ClockResetSet.clocks,ClockResetSet.empty]) (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, B,M,Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.TransitionForm.boundClocks,
      Section3.TransitionForm.union,Section3.TransitionForm.underReset,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,
      Section3.StateForm.union,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
      ClockResetSet.clocks_union,ClockResetSet.clocks,ClockResetSet.empty,
      ClockResetSet.singleton,Set.disjoint_left])
  have hnext := SafeNormalization.next hS rfl
  have hU : SafeNormalization (.predicate (upper I φ))
      (.ofState (.ofLocal (.predicate (upper I φ))) : Section3.TransitionForm Nat Var) := .predicate _
  have hUN := safe_conj hU hnext (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, Section3.TransitionForm.boundClocks,Section3.TransitionForm.ofState,
      Section3.StateForm.ofLocal,ClockResetSet.clocks,ClockResetSet.empty]) (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, B,M,upper,Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.TransitionForm.boundClocks,
      Section3.TransitionForm.ofNextState,Section3.TransitionForm.union,
      Section3.TransitionForm.unionNext,Section3.TransitionForm.underReset,
      Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,
      Section3.StateForm.empty,Section3.StateForm.union,Section3.StateForm.guardClocks,
      Section3.StateForm.localClocks,Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks,
      ClockResetSet.clocks_union,ClockResetSet.clocks,ClockResetSet.empty,
      ClockResetSet.singleton,Set.disjoint_left])
  have noM (F : Section3.TransitionForm Nat Var) : Disjoint F.boundClocks (M.union M).allClocks := by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.allClocks,Section3.TransitionForm.freeClocks,
      Section3.TransitionForm.bodyFreeClocks,Section3.TransitionForm.boundClocks,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,
      Section3.StateForm.union,Section3.StateForm.guardClocks,Section3.StateForm.localClocks,
      Local.freeClocks,Local.toJudgement,Section3.Judgement.freeClocks,
      ClockResetSet.clocks_union,ClockResetSet.clocks,ClockResetSet.empty]
  have noMB (F : Section3.TransitionForm Nat Var) : Disjoint (M.union M).boundClocks F.allClocks := by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.boundClocks,Section3.TransitionForm.union,
      Section3.TransitionForm.unionNext,Section3.TransitionForm.ofState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,ClockResetSet.clocks_union,
      ClockResetSet.clocks,ClockResetSet.empty]
  have hH := safe_conj hUN hMM (noM _) (noMB _)
  have hA := safe_conj hnext hMM (noM _) (noMB _)
  have hBin : SafeNormalization (.predicate (bounded I φ))
      (.ofState (.ofLocal (.predicate (bounded I φ))) : Section3.TransitionForm Nat Var) := .predicate _
  have hbody := safe_conj hBin hMM (noM _) (noMB _)
  have hJ := SafeNormalization.reset (ClockResetSet.singleton 1 0) hbody (by
    simp [-ENNReal.none_eq_top, -ENNReal.some_eq_coe,
      ClockResetSet.union, Section3.TransitionForm.unionNext, Section3.StateForm.ofLocal, M,Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.guardClocks])
  have d := resolve I φ
  have he := d.normalize_erased_of_full hH.normalizes
  have heq := Option.some.inj (hA.normalizes.symm.trans he)
  rw [heq] at hA
  exact ⟨_,_,hJ,hH,hA,Derives.resolved d hJ hH hA⟩

end STLTableau.Section4.Finiteness.BoundaryExample
