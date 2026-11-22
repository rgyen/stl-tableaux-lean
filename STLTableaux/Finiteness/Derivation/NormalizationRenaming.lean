import STLTableaux.Finiteness.Derivation.DerivationRenaming
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Literal global renaming of safe normalized resolution certificates. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def renameTransition (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var) :
    Section3.TransitionForm Clock Var := ⟨F.current.rename e,F.nextPart.map (Section3.StateForm.rename e)⟩

private theorem image_disjoint (e : Equiv.Perm Clock) {S T : Set Clock}
    (h : Disjoint S T) : Disjoint (e '' S) (e '' T) := by
  apply Set.disjoint_left.2
  rintro _ ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
  exact Set.disjoint_left.1 h hs (e.injective he ▸ ht)

private theorem reset_union (e : Equiv.Perm Clock) (R S : ClockResetSet Clock) :
    (R.union S).rename e = (R.rename e).union (S.rename e) := by
  cases R; cases S; rfl

@[simp] theorem guardClocks_rename (e : Equiv.Perm Clock) (S : Section3.StateForm Clock Var) :
    (S.rename e).guardClocks = e '' S.guardClocks := by
  ext c
  simp only [Section3.StateForm.guardClocks,Section3.StateForm.rename,Set.mem_setOf_eq,Set.mem_image,Guard.rename]
  constructor
  · rintro ⟨g,⟨h,hh,rfl⟩,rfl⟩; exact ⟨h.clock,⟨h,hh,rfl⟩,rfl⟩
  · rintro ⟨d,⟨g,hg,rfl⟩,rfl⟩; exact ⟨g.rename e,⟨g,hg,rfl⟩,rfl⟩

@[simp] theorem rename_state_union (e : Equiv.Perm Clock) (S T : Section3.StateForm Clock Var) :
    (S.union T).rename e = (S.rename e).union (T.rename e) := by
  apply Section3.StateForm.ext_components
  · exact Set.image_union _ _ _
  · exact reset_union e _ _
  · exact Set.image_union _ _ _

@[simp] theorem rename_transition_union (e : Equiv.Perm Clock) (F G : Section3.TransitionForm Clock Var) :
    renameTransition e (F.union G) = (renameTransition e F).union (renameTransition e G) := by
  cases F with | mk S N =>
    cases G with | mk T M =>
      cases N <;> cases M <;> simp [renameTransition,Section3.TransitionForm.union,Section3.TransitionForm.unionNext]

@[simp] theorem rename_bodyFreeClocks (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var) :
    (renameTransition e F).bodyFreeClocks = e '' F.bodyFreeClocks := by
  cases hn : F.nextPart <;>
    simp [renameTransition,Section3.TransitionForm.bodyFreeClocks,hn,Set.image_union]

private theorem components_rename (e : Equiv.Perm Clock) {S T : Section3.StateForm Clock Var}
    (h : ComponentsIncluded S T) : ComponentsIncluded (S.rename e) (T.rename e) := by
  refine ⟨Set.image_mono h.guards,?_,Set.image_mono h.locals⟩
  intro c a hc
  exact h.resets (e.symm c) a hc

theorem subsumed_rename (e : Equiv.Perm Clock) {F G : Section3.TransitionForm Clock Var}
    (h : Section3.SyntacticallySubsumed F G) :
    Section3.SyntacticallySubsumed (renameTransition e F) (renameTransition e G) := by
  refine ⟨components_rename e h.current,?_,?_⟩
  · change Disjoint (G.current.rename e).resets.clocks
      ((renameTransition e F).bodyFreeClocks \ (F.current.rename e).resets.clocks)
    simp only [Section3.StateForm.rename,ClockResetSet.clocks_rename,rename_bodyFreeClocks,
      ← Set.image_sdiff e.injective]
    exact image_disjoint e h.outerFresh
  · intro N hn
    cases hx : F.nextPart with
    | none => simp [renameTransition,hx] at hn
    | some M =>
      have he : M.rename e = N := by simpa [renameTransition,hx] using hn
      subst N
      obtain ⟨K,hk,hinc,hd⟩ := h.next M hx
      refine ⟨K.rename e,by simp [renameTransition,hk],components_rename e hinc,?_⟩
      change Disjoint (K.resets.rename e).clocks ((M.rename e).localClocks \ (M.resets.rename e).clocks)
      rw [ClockResetSet.clocks_rename,Section3.StateForm.localClocks_rename,ClockResetSet.clocks_rename,
        ← Set.image_sdiff e.injective]
      exact image_disjoint e hd

theorem unionCompatible_rename (e : Equiv.Perm Clock) {F G : Section3.TransitionForm Clock Var}
    (h : F.UnionCompatible G) : (renameTransition e F).UnionCompatible (renameTransition e G) := by
  constructor
  · simpa only [rename_transition_union] using subsumed_rename e h.left
  · simpa only [rename_transition_union] using subsumed_rename e h.right

@[simp] theorem rename_underReset (e : Equiv.Perm Clock) (R : ClockResetSet Clock)
    (F : Section3.TransitionForm Clock Var) :
    renameTransition e (F.underReset R) = (renameTransition e F).underReset (R.rename e) := by
  cases F with | mk S N =>
    cases S
    simp only [renameTransition,Section3.TransitionForm.underReset,Section3.StateForm.rename,reset_union]

@[simp] theorem reset_rename_empty (e : Equiv.Perm Clock) :
    (ClockResetSet.empty : ClockResetSet Clock).rename e = ClockResetSet.empty := by rfl

@[simp] theorem rename_state_empty (e : Equiv.Perm Clock) :
    (Section3.StateForm.empty : Section3.StateForm Clock Var).rename e = Section3.StateForm.empty := by
  apply Section3.StateForm.ext_components <;>
    simp [Section3.StateForm.rename,Section3.StateForm.empty]

@[simp] theorem rename_state_local (e : Equiv.Perm Clock) (l : Local Clock Var) :
    (Section3.StateForm.ofLocal l).rename e = Section3.StateForm.ofLocal (l.rename e) := by
  apply Section3.StateForm.ext_components <;>
    simp [Section3.StateForm.rename,Section3.StateForm.ofLocal]

@[simp] theorem rename_state_guard (e : Equiv.Perm Clock) (g : Section3.Guard Clock) :
    (Section3.StateForm.ofGuard (Var := Var) g).rename e = Section3.StateForm.ofGuard (g.rename e) := by
  apply Section3.StateForm.ext_components <;>
    simp [Section3.StateForm.rename,Section3.StateForm.ofGuard]

/-- Actual recursive syntactic safety is preserved, including current guard support. -/
theorem SafeNormalization.rename (e : Equiv.Perm Clock) {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    SafeNormalization (renameJudgement e J) (renameTransition e F) := by
  induction h with
  | terminal => simpa [renameJudgement,renameTransition,Section3.TransitionForm.ofState,Local.rename] using (SafeNormalization.terminal (Clock := Clock) (Var := Var))
  | clock c r a => simpa [renameJudgement,renameTransition,Section3.TransitionForm.ofState,Guard.rename] using (SafeNormalization.clock (Var := Var) (e c) r a)
  | marker m => simpa [renameJudgement,renameTransition,Section3.TransitionForm.ofState,Local.rename] using (SafeNormalization.marker (Clock := Clock) (Var := Var) m)
  | predicate p => simpa [renameJudgement,renameTransition,Section3.TransitionForm.ofState,Local.rename] using (SafeNormalization.predicate (p.rename e))
  | conj h g hc ih ig =>
      simpa only [rename_transition_union,renameJudgement] using
        (SafeNormalization.conj ih ig (unionCompatible_rename e hc))
  | @reset R J F h hd ih =>
      rw [rename_underReset]
      apply SafeNormalization.reset _ ih
      change Disjoint (R.rename e).clocks (F.current.rename e).guardClocks
      rw [ClockResetSet.clocks_rename,guardClocks_rename]
      exact image_disjoint e hd
  | @next J F h hn ih =>
      have hnext : (renameTransition e F).nextPart = none := by simp [renameTransition,hn]
      simpa [renameJudgement,renameTransition,Section3.TransitionForm.ofNextState] using (SafeNormalization.next ih hnext)


@[simp] theorem rename_ofState (e : Equiv.Perm Clock) (N : Section3.StateForm Clock Var) :
    renameTransition e (Section3.TransitionForm.ofState N) = Section3.TransitionForm.ofState (N.rename e) := rfl

private theorem keepAtomic_rename (e : Equiv.Perm Clock) (l : Local Clock Var) :
    Section3.TransitionForm.KeepAtomic (l.rename e) ↔ Section3.TransitionForm.KeepAtomic l := by
  cases l with
  | terminal => rfl
  | marker => rfl
  | predicate p => cases p <;> rfl

@[simp] theorem rename_atomicProjection (e : Equiv.Perm Clock) (F : Section3.TransitionForm Clock Var) :
    renameTransition e F.atomicProjection = (renameTransition e F).atomicProjection := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · rfl
    · rfl
    · ext l
      change (l ∈ Local.rename e '' {a ∈ F.current.locals | Section3.TransitionForm.KeepAtomic a}) ↔
        l ∈ {a ∈ Local.rename e '' F.current.locals | Section3.TransitionForm.KeepAtomic a}
      constructor
      · rintro ⟨a,⟨ha,hk⟩,rfl⟩
        exact ⟨⟨a,ha,rfl⟩,(keepAtomic_rename e a).2 hk⟩
      · rintro ⟨⟨a,ha,rfl⟩,hk⟩
        exact ⟨a,⟨ha,(keepAtomic_rename e a).1 hk⟩,rfl⟩
  · rfl

end STLTableau.Section4.Finiteness
