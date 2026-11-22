import STLTableaux.Finiteness.Derivation.CanonicalSafety
import STLTableaux.Finiteness.Derivation.CurrentGuardProjection
import STLTableaux.Finiteness.Derivation.NextStatePrivacy
import STLTableaux.Finiteness.Derivation.Pending.PendingNextPrivacy

/-! Canonical judgements for state forms with a nonempty set of locals. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem local_safe (l : Local Clock Var) :
    SafeNormalization l.toJudgement (.ofState (.ofLocal l)) := by
  cases l with
  | terminal => exact .terminal
  | marker m => exact .marker m
  | predicate p => exact .predicate p

private theorem local_fold_safe (L : List (Local Clock Var)) (B : MixedJ Clock Var)
    (hf : foldCurrent (L.map Local.toJudgement) = some B) :
    ∃ S : Section3.StateForm Clock Var, SafeNormalization B (.ofState S) ∧
      S.guards = ∅ ∧ S.resets = ClockResetSet.empty ∧ S.locals = {l | l ∈ L} := by
  induction L generalizing B with
  | nil => cases hf
  | cons l L ih =>
      cases ht : foldCurrent (L.map Local.toJudgement) with
      | none =>
          have he : l.toJudgement = B := by simpa [foldCurrent,ht,optionalConj] using hf
          subst B
          have heL : L = [] := by
            have hm := (foldCurrent_none_iff _).1 ht
            simpa only [List.map_eq_nil_iff] using hm
          subst L
          refine ⟨.ofLocal l,local_safe l,rfl,rfl,?_⟩
          ext a; simp [Section3.StateForm.ofLocal]
      | some T =>
          have he : .conj l.toJudgement T = B := by simpa [foldCurrent,ht,optionalConj] using hf
          subst B
          obtain ⟨S,hS,hg,hr,hl⟩ := ih T ht
          have hc := CanonicalSafety.state_compatible (Section3.StateForm.ofLocal l)
            (Section3.TransitionForm.ofState S) rfl (by
              change Disjoint S.resets.clocks _
              rw [hr,empty_reset_clocks]
              exact Set.disjoint_left.2 (fun _ hx _ => False.elim hx))
          refine ⟨(Section3.StateForm.ofLocal l).union S,.conj (local_safe l) hS hc,?_,?_,?_⟩
          · change ∅ ∪ S.guards = ∅; rw [hg,Set.union_empty]
          · change ClockResetSet.empty.union S.resets = ClockResetSet.empty; rw [hr]; rfl
          · ext a; simp [Section3.StateForm.union,Section3.StateForm.ofLocal,hl]

private theorem state_reset_exact (S N : Section3.StateForm Clock Var)
    (hg : S.guards = ∅) (hr : S.resets = ClockResetSet.empty) (hl : S.locals = N.locals) :
    (Section3.TransitionForm.ofState S).underReset N.resets = .ofState {N with guards := ∅, guards_finite := Set.finite_empty} := by
  apply congrArg (fun T => Section3.TransitionForm.ofState T)
  apply Section3.StateForm.ext_components
  · exact hg
  · change S.resets.union N.resets = N.resets
    rw [hr]; rfl
  · exact hl

private theorem canonical_state_safe
    (N : Section3.StateForm Clock Var) (G : List (Section3.Guard Clock)) (L : List (Local Clock Var))
    (hG : {g | g ∈ G} = N.guards) (hL : {l | l ∈ L} = N.locals) (hLn : L ≠ [])
    (C : MixedJ Clock Var) (hshape : canonicalSyntax N.resets G L [] = some C) :
    SafeNormalization C (.ofState N) := by
  cases hb : foldCurrent (L.map Local.toJudgement) with
  | none =>
      have he := (foldCurrent_none_iff _).1 hb
      exact False.elim (hLn (List.map_eq_nil_iff.1 he))
  | some B =>
      obtain ⟨S,hS,hg,hr,hl⟩ := local_fold_safe L B hb
      have hreset : SafeNormalization (.reset N.resets B)
          ((Section3.TransitionForm.ofState S).underReset N.resets) := .reset _ hS (by
        change Disjoint N.resets.clocks S.guardClocks
        simp only [Section3.StateForm.guardClocks,hg,Set.mem_empty_iff_false,false_and,exists_false,Set.setOf_false]
        exact Set.disjoint_empty _)
      rw [state_reset_exact S N hg hr (hl.trans hL)] at hreset
      cases hguards : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
      | none =>
          have heG : G = [] := List.map_eq_nil_iff.1 ((foldCurrent_none_iff _).1 hguards)
          have hNg : N.guards = ∅ := by rw [← hG,heG]; ext g; simp
          have heC : .reset N.resets B = C := by
            simpa [canonicalSyntax,hguards,hb,optionalConj] using hshape
          subst C
          have heN : {N with guards := ∅, guards_finite := Set.finite_empty} = N := by
            apply Section3.StateForm.ext_components
            · exact hNg.symm
            · rfl
            · rfl
          rw [heN] at hreset
          exact hreset
      | some A =>
          obtain ⟨T,hT,hTr,hTl,hcompatible⟩ := CanonicalSafety.guard_spine G A hguards
          have hTg : T.guards = N.guards := by
            have hcanon : canonicalSyntax ClockResetSet.empty G [] [] = some A := by
              simp [canonicalSyntax,hguards,foldCurrent,optionalConj]
            exact hT.currentGuards_eq.trans ((canonical_currentGuards hcanon).trans hG)
          have heC : .conj A (.reset N.resets B) = C := by
            simpa [canonicalSyntax,hguards,hb,optionalConj] using hshape
          subst C
          have hsafe := SafeNormalization.conj hT hreset (hcompatible _)
          convert hsafe using 1
          apply congrArg (fun T => Section3.TransitionForm.ofState T)
          apply Section3.StateForm.ext_components
          · change N.guards = T.guards ∪ ∅; rw [hTg,Set.union_empty]
          · change N.resets = T.resets.union N.resets; rw [hTr]; rfl
          · change N.locals = T.locals ∪ N.locals; rw [hTl,Set.empty_union]


/-- A nonempty-local state has a directly constructed owned, next-free input.
The finite history is chosen from its actual constructed syntax. -/
theorem exists_owned_state_input (N : Section3.StateForm Clock Var) (hne : N.locals.Nonempty)
    (hprivate : ∀ p q, Local.predicate p ∈ N.locals → Local.predicate q ∈ N.locals → p ≠ q →
      Disjoint (syntaxClocks (.predicate p)) (syntaxClocks (.predicate q))) :
    ∃ (J : MixedJ Clock Var) (W : Set Clock) (owned : OwnedPending J N.resets W),
      owned.nextInputs = [] ∧ SafeNormalization J (.ofState N) ∧ NextPrivate J := by
  classical
  let G := N.guards_finite.toFinset.toList
  let L := N.locals_finite.toFinset.toList
  have hG : {g | g ∈ G} = N.guards := by ext g; simp [G]
  have hL : {l | l ∈ L} = N.locals := by ext l; simp [L]
  have hLn : L ≠ [] := by
    intro he
    obtain ⟨l,hl⟩ := hne
    have hm : l ∈ L := by rw [← hL] at hl; exact hl
    rw [he] at hm
    cases hm
  obtain ⟨B,hB⟩ : ∃B, foldCurrent (L.map Local.toJudgement) = some B := by
    cases hb : foldCurrent (L.map Local.toJudgement) with
    | some B => exact ⟨B,rfl⟩
    | none => exact False.elim (hLn (List.map_eq_nil_iff.1 ((foldCurrent_none_iff _).1 hb)))
  obtain ⟨C,hC⟩ : ∃C, canonicalSyntax N.resets G L [] = some C := by
    cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => exact ⟨.reset N.resets B,by simp [canonicalSyntax,hB,hg,optionalConj]⟩
    | some A => exact ⟨.conj A (.reset N.resets B),by simp [canonicalSyntax,hB,hg,optionalConj]⟩
  have hsafe := canonical_state_safe N G L hG hL hLn C hC
  let W := syntaxClocks C ∪ N.resets.clocks
  let owned : OwnedPending C N.resets W := {
    guards := G
    locals := L
    nextInputs := []
    canonical := C
    shape := hC
    regroup := .refl C
    regroup_nonincrease := le_rfl
    locals_nodup := Finset.nodup_toList _
    private_sources := by
      intro p q hp hq hpq
      apply hprivate p q
      · change Local.predicate p ∈ {l | l ∈ L} at hp
        rw [hL] at hp
        exact hp
      · change Local.predicate q ∈ {l | l ∈ L} at hq
        rw [hL] at hq
        exact hq
      · exact hpq
    source_next := by intro p K hp hK; cases hK
    next_private := by simp
    next_flat := by intro K hK; cases hK
    absent_body_reset := by intro he; exact False.elim (hLn he)
    input_safe := ⟨_,hsafe⟩
    finite_budget := (syntaxClocks_finite C).union N.resets.finite_domain
    covers_input := by
      intro c hc
      rcases hc with (hc | hc) | hc
      · exact Or.inl hc
      · exact Or.inl hc
      · exact Or.inr hc }
  refine ⟨C,W,owned,rfl,hsafe,?_⟩
  rw [canonical_nextPrivate_iff hC]
  intro K hK
  cases hK

end STLTableau.Section4.Finiteness
