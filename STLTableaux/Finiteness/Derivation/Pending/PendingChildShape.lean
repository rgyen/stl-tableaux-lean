import STLTableaux.Finiteness.Derivation.Pending.PendingFold
import STLTableaux.Finiteness.Derivation.Pending.PendingCollection
import STLTableaux.Finiteness.Derivation.ResetScopeMerge

/-! Direct syntactic assembly of a selected canonical branch and a PRESENT
residual pending spine. No resolver or completed-target existence is assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem fold_append_present {X Y : List (MixedJ Clock Var)}
    {J : MixedJ Clock Var} (hX : foldCurrent X = some J) :
    ∃ L, foldCurrent (X ++ Y) = some L := by
  cases h : foldCurrent (X ++ Y) with
  | some L => exact ⟨L,rfl⟩
  | none =>
    have he := (foldCurrent_none_iff _).1 h
    have hx := (List.append_eq_nil_iff.mp he).1
    rw [hx] at hX
    cases hX

private theorem fold_perm_present {X Y : List (MixedJ Clock Var)}
    (hp : X.Perm Y) {J : MixedJ Clock Var} (hX : foldCurrent X = some J) :
    ∃ K, foldCurrent Y = some K := by
  cases h : foldCurrent Y with
  | some K => exact ⟨K,rfl⟩
  | none =>
    have hy := (foldCurrent_none_iff _).1 h
    have hl := hp.length_eq
    rw [hy,List.length_nil] at hl
    have hx : X = [] := List.length_eq_zero_iff.mp hl
    rw [hx] at hX
    cases hX

/-- Merge the actual reset scopes, reorder only by list permutation, then
collect current locals while retaining every literal next payload. -/
theorem assemble_child_canonical
    {Rb S : ClockResetSet Clock} {Lb Lrest : List (Local Clock Var)}
    {Nb Nold : List (MixedJ Clock Var)} {Cb Γ : MixedJ Clock Var}
    (hCb : canonicalSyntax Rb [] Lb Nb = some Cb)
    (hΓ : foldCurrent (Lrest.map Local.toJudgement ++ Nold.map Section3.Judgement.next) = some Γ)
    (hc : Rb.Consistent S) (hL : Disjoint S.clocks Cb.freeClocks)
    (hR : Disjoint Rb.clocks (Γ.freeClocks \ S.clocks)) :
    ∃ Cchild, canonicalSyntax (Rb.union S) [] (PendingCollection.collect (Lb ++ Lrest))
        (Nb ++ Nold) = some Cchild ∧
      StructuralEq (.conj Cb (.reset S Γ)) Cchild ∧
      pendingWeight Cchild ≤ pendingWeight Cb + pendingWeight Γ := by
  cases hb : foldCurrent (Lb.map Local.toJudgement ++ Nb.map Section3.Judgement.next) with
  | none => simp [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hb] at hCb
  | some Kb =>
    have he : .reset Rb Kb = Cb := by
      simpa only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hb,Option.map_some,Option.some.injEq] using hCb
    subst Cb
    obtain ⟨App,hApp⟩ := fold_append_present (Y := Lrest.map Local.toJudgement ++
      Nold.map Section3.Judgement.next) hb
    have hp : ((Lb.map Local.toJudgement ++ Nb.map Section3.Judgement.next) ++
        (Lrest.map Local.toJudgement ++ Nold.map Section3.Judgement.next)).Perm
        ((Lb ++ Lrest).map Local.toJudgement ++ (Nb ++ Nold).map Section3.Judgement.next) := by
      have hmid : (Nb.map Section3.Judgement.next ++ Lrest.map Local.toJudgement).Perm
          (Lrest.map Local.toJudgement ++ Nb.map Section3.Judgement.next) := List.perm_append_comm
      simpa only [List.map_append,List.append_assoc] using
        (hmid.append_right (Nold.map Section3.Judgement.next)).append_left (Lb.map Local.toJudgement)
    obtain ⟨Sorted,hSorted⟩ := fold_perm_present hp hApp
    obtain ⟨Collected,hCollected,hcollect,hweight,_,_⟩ :=
      PendingCollection.collect_locals (Lb ++ Lrest) (Nb ++ Nold) Sorted hSorted
    have happend := foldCurrent_append hb hΓ hApp
    have hperm := foldCurrent_perm hp hApp hSorted
    have hmerged := merge_reset_scopes Rb S Kb Γ hc hL hR
    refine ⟨.reset (Rb.union S) Collected,?_,?_,?_⟩
    · simp only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hCollected,Option.map_some]
    · exact .trans hmerged (.reset (Rb.union S) (.trans happend (.trans hperm hcollect)))
    · change pendingWeight Collected ≤ pendingWeight Kb + pendingWeight Γ
      have ha := foldCurrent_append_weight hb hΓ hApp
      have hpw := foldCurrent_perm_weight hp hApp hSorted
      omega

end STLTableau.Section4.Finiteness
