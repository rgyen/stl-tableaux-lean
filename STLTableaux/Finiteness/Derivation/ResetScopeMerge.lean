import STLTableaux.Finiteness.Derivation.Derivation

/-! Regroup compatible reset scopes by structural equivalence. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Independently scoped conjuncts may share a consistent reset map precisely
when each additional map avoids the other's free, unbound clock values. -/
theorem merge_reset_scopes (R S : ClockResetSet Clock) (J K : MixedJ Clock Var)
    (hc : R.Consistent S)
    (hJ : Disjoint S.clocks (J.freeClocks \ R.clocks))
    (hK : Disjoint R.clocks (K.freeClocks \ S.clocks)) :
    StructuralEq (.conj (.reset R J) (.reset S K))
      (.reset (R.union S) (.conj J K)) := by
  have left : StructuralEq (.reset R J) (.reset (R.union S) J) :=
    .trans (.symm (.resetUnused S (.reset R J) hJ)) (.resetNested S R J)
  have right : StructuralEq (.reset S K) (.reset (R.union S) K) := by
    have h : StructuralEq (.reset S K) (.reset (S.union R) K) :=
      .trans (.symm (.resetUnused R (.reset S K) hK)) (.resetNested R S K)
    rw [← reset_union_comm_of_consistent R S hc] at h
    exact h
  exact .trans (.conj left right) (.symm (.resetDistrib (R.union S) J K))

/-- A guard can be moved outside a reset only if that reset does not bind its
clock. The guard's relation and threshold are unchanged. -/
theorem extract_unreset_guard (R : ClockResetSet Clock) (c : Clock)
    (r : ClockRelation) (a : NNReal) (J : MixedJ Clock Var) (hc : c ∉ R.clocks) :
    StructuralEq (.reset R (.conj (.clock c r a) J))
      (.conj (.clock c r a) (.reset R J)) := by
  have hf : Disjoint R.clocks (Section3.Judgement.freeClocks
      (.clock c r a : MixedJ Clock Var)) := by
    apply Set.disjoint_left.mpr
    intro x hx he
    have he : x = c := he
    exact hc (he ▸ hx)
  exact .trans (.resetDistrib R (.clock c r a) J)
    (.conj (.resetUnused R (.clock c r a) hf) (.refl _))

end STLTableau.Section4.Finiteness
