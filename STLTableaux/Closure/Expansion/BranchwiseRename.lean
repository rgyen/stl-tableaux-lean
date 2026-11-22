import STLTableaux.Closure.Expansion.BranchwiseExpansion
import STLTableaux.Finiteness.ClockAllocation.SupportedClockPermutations

/-! Uniform clock permutations act on concrete contextual one-step expansions.
Unlike the scoped alpha conversions internal to a step, this operation
renames every clock consistently, including free names. -/
namespace STLTableau.Section3.ConcreteContextual
open STLTableau.Section4.Finiteness
variable {Clock Var : Type*}

@[simp] theorem predicate_rename_refl (p : Predicate Clock Var) :
    p.rename (Equiv.refl Clock) = p := by cases p <;> rfl

theorem predicate_rename_trans (e f : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).rename f = p.rename (e.trans f) := by cases p <;> rfl

@[simp] theorem predicate_rename_inverse (e : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).rename e.symm = p := by cases p <;> simp [Predicate.rename]

private theorem local_rename_trans (e f : Equiv.Perm Clock) (l : Local Clock Var) :
    (l.rename e).rename f = l.rename (e.trans f) := by
  cases l <;> simp [Local.rename, predicate_rename_trans]

private theorem state_rename_trans (e f : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).rename f = S.rename (e.trans f) := by
  apply StateForm.ext_components
  · change Guard.rename f '' (Guard.rename e '' S.guards) = _
    rw [Set.image_image]
    rfl
  · cases S.resets; rfl
  · change Local.rename f '' (Local.rename e '' S.locals) = _
    rw [Set.image_image]
    exact Set.image_congr fun l _ => local_rename_trans e f l

private theorem state_rename_refl (S : StateForm Clock Var) :
    S.rename (Equiv.refl Clock) = S := by
  apply StateForm.ext_components
  · change Guard.rename (Equiv.refl Clock) '' S.guards = _
    have h : Guard.rename (Equiv.refl Clock) = id := by funext g; cases g; rfl
    rw [h, Set.image_id]
  · change S.resets.rename (Equiv.refl Clock) = S.resets
    generalize S.resets = R
    cases R
    rfl
  · change Local.rename (Equiv.refl Clock) '' S.locals = _
    have h : Local.rename (Equiv.refl Clock) = (id : Local Clock Var → _) := by
      funext l
      cases l <;> simp [Local.rename]
    rw [h, Set.image_id]

theorem renameTransition_trans (e f : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    renameTransition f (renameTransition e F) = renameTransition (e.trans f) F := by
  cases F with
  | mk S N => cases N <;> simp [renameTransition, state_rename_trans]

@[simp] theorem renameTransition_refl (F : TransitionForm Clock Var) :
    renameTransition (Equiv.refl Clock) F = F := by
  cases F with
  | mk S N => cases N <;> simp [renameTransition, state_rename_refl]

@[simp] theorem renameTransition_inverse (e : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    renameTransition e.symm (renameTransition e F) = F := by
  rw [renameTransition_trans]
  simp

theorem renameTransition_eq_of_fixes (e : Equiv.Perm Clock) (F : TransitionForm Clock Var)
    (h : ∀ c ∈ F.allClocks, e c = c) : renameTransition e F = F :=
  (transition_rename_congr F e (Equiv.refl Clock) h).trans (renameTransition_refl F)

theorem branchwiseCurrent_rename_iff (e : Equiv.Perm Clock)
    (F : TransitionForm Clock Var) (p : Predicate Clock Var) :
    p.rename e ∈ branchwiseCurrent (renameTransition e F) ↔ p ∈ branchwiseCurrent F := by
  change Local.predicate (p.rename e) ∈ Local.rename e '' F.current.locals ↔ _
  constructor
  · rintro ⟨l, hl, he⟩
    cases l with
    | terminal => cases he
    | marker => cases he
    | predicate q =>
      have h := congrArg (Predicate.rename e.symm) (Local.predicate.inj he)
      have he' : q = p := by simpa only [predicate_rename_inverse] using h
      subst q
      exact hl
  · intro hp
    exact ⟨.predicate p, hp, rfl⟩

private def conjPerm (e f : Equiv.Perm Clock) : Equiv.Perm Clock :=
  (e.symm.trans f).trans e

private theorem conj_comp (e f : Equiv.Perm Clock) :
    e.trans (conjPerm e f) = f.trans e := by ext c; simp [conjPerm]

private theorem conj_fixes (e f : Equiv.Perm Clock) {s : Set Clock}
    (h : ∀ c ∈ s, f c = c) : ∀ c ∈ e '' s, conjPerm e f c = c := by
  rintro _ ⟨c, hc, rfl⟩
  simp [conjPerm, h c hc]

private theorem rename_alphaReset (e f : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.alphaReset f).rename e = (S.rename e).alphaReset (conjPerm e f) := by
  have he : (S.rename f).rename e = (S.rename e).rename (conjPerm e f) := by
    rw [state_rename_trans, state_rename_trans, conj_comp]
  apply StateForm.ext_components
  · rfl
  · change ((S.rename f).rename e).resets = ((S.rename e).rename (conjPerm e f)).resets
    exact congrArg StateForm.resets he
  · change ((S.rename f).rename e).locals = ((S.rename e).rename (conjPerm e f)).locals
    exact congrArg StateForm.locals he

private theorem rename_alphaOuter (e f : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    renameTransition e (F.alphaOuter f) = (renameTransition e F).alphaOuter (conjPerm e f) := by
  cases F with
  | mk S N => cases N <;>
    simp [renameTransition, TransitionForm.alphaOuter, rename_alphaReset,
      state_rename_trans, conj_comp]

private theorem rename_alphaNext (e f : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    renameTransition e (F.alphaNext f) = (renameTransition e F).alphaNext (conjPerm e f) := by
  cases F with
  | mk S N => cases N <;> simp [renameTransition, TransitionForm.alphaNext, rename_alphaReset]

private theorem outer_conj_fixes (e f : Equiv.Perm Clock) (F : TransitionForm Clock Var)
    (hf : ∀ c ∈ F.bodyFreeClocks \ F.current.resets.clocks, f c = c) :
    ∀ c ∈ (renameTransition e F).bodyFreeClocks \ (renameTransition e F).current.resets.clocks,
      conjPerm e f c = c := by
  change ∀ c ∈ (renameTransition e F).bodyFreeClocks \ (F.current.resets.rename e).clocks, _
  rw [rename_bodyFreeClocks, ClockResetSet.clocks_rename, ← Set.image_sdiff e.injective]
  exact conj_fixes e f hf

private theorem next_conj_fixes (e f : Equiv.Perm Clock) (F : TransitionForm Clock Var)
    (hf : ∀ N, F.nextPart = some N → ∀ c ∈ N.localClocks \ N.resets.clocks, f c = c) :
    ∀ N, (renameTransition e F).nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, conjPerm e f c = c := by
  intro N hN
  cases he : F.nextPart with
  | none => simp [renameTransition, he] at hN
  | some S =>
    have hh : S.rename e = N := by simpa [renameTransition, he] using hN
    subst N
    rw [StateForm.localClocks_rename]
    change ∀ c ∈ e '' S.localClocks \ (S.resets.rename e).clocks, _
    rw [ClockResetSet.clocks_rename, ← Set.image_sdiff e.injective]
    exact conj_fixes e f (hf S he)

private theorem alphaEquivalent_rename (e : Equiv.Perm Clock) {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) : (renameTransition e F).AlphaEquivalent (renameTransition e G) := by
  induction h with
  | refl => exact .refl _
  | outer F f hf =>
    rw [rename_alphaOuter]
    exact .outer _ _ (outer_conj_fixes e f F hf)
  | next F f hf =>
    rw [rename_alphaNext]
    exact .next _ _ (next_conj_fixes e f F hf)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

private theorem nextAlphaPath_rename (e : Equiv.Perm Clock) {F G : TransitionForm Clock Var}
    (h : NextAlphaPath F G) : NextAlphaPath (renameTransition e F) (renameTransition e G) := by
  induction h with
  | refl => exact .refl _
  | step F f hf _ ih =>
    rw [rename_alphaNext] at ih
    exact .step _ _ (next_conj_fixes e f F hf) ih

private theorem normalize_rename (e : Equiv.Perm Clock) (J : MixedJ Clock Var) :
    TransitionForm.normalize? (renameJudgement e J) =
      (TransitionForm.normalize? J).map (renameTransition e) := by
  induction J with
  | terminal => simp [renameJudgement, TransitionForm.normalize?, Local.rename]
  | marker => simp [renameJudgement, TransitionForm.normalize?, Local.rename]
  | clock => simp [renameJudgement, TransitionForm.normalize?, Guard.rename]
  | predicate => simp [renameJudgement, TransitionForm.normalize?, Local.rename]
  | reset R J ih =>
    simp only [renameJudgement, TransitionForm.normalize?, ih]
    cases TransitionForm.normalize? J <;> simp [rename_underReset]
  | conj J K ihJ ihK =>
    simp only [renameJudgement, TransitionForm.normalize?, ihJ, ihK]
    cases TransitionForm.normalize? J <;> cases TransitionForm.normalize? K <;>
      simp [rename_transition_union]
  | next J ih =>
    simp only [renameJudgement, TransitionForm.normalize?, ih]
    cases TransitionForm.normalize? J with
    | none => rfl
    | some F =>
      cases h : F.nextPart <;> simp [renameTransition, h, TransitionForm.ofNextState]

private theorem mixed_branch_raw [DecidableEq Clock]
    {p : Predicate Clock Var} {R : ClockResetSet Clock} {F : TransitionForm Clock Var} :
    ConcreteMixed.catalogue.Branch p R F ↔
      ∃ J U, RawBranch p J ∧ TransitionForm.normalize? J = some U ∧ F = U.underReset R := by
  constructor
  · intro h
    change ConcreteFinite.Branch p R F ∨ ConcreteInfinite.Branch p R F ∨
      ConcreteOpening.Branch p R F at h
    rcases h with h | h | h
    · obtain ⟨_, _, J, U, rfl, hr, hm, hn, rfl⟩ := h
      exact ⟨_, U, .finite hr hm, hn, rfl⟩
    · obtain ⟨_, _, J, U, rfl, hr, hm, hn, rfl⟩ := h
      exact ⟨_, U, .infinite hr hm, hn, rfl⟩
    · obtain ⟨c, m, kind, a, φ, U, rfl, hn, rfl⟩ := h
      exact ⟨_, U, .opening c m kind a φ, hn, rfl⟩
  · rintro ⟨J, U, h, hn, rfl⟩
    change ConcreteFinite.Branch p R (U.underReset R) ∨
      ConcreteInfinite.Branch p R (U.underReset R) ∨ ConcreteOpening.Branch p R (U.underReset R)
    cases h with
    | finite hr hm => exact Or.inl ⟨_, _, _, U, rfl, hr, hm, hn, rfl⟩
    | infinite hr hm => exact Or.inr (Or.inl ⟨_, _, _, U, rfl, hr, hm, hn, rfl⟩)
    | opening c m kind a φ => exact Or.inr (Or.inr ⟨c, m, kind, a, φ, U, rfl, hn, rfl⟩)

theorem branch_rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {p : Predicate Clock Var} {R : ClockResetSet Clock} {F : TransitionForm Clock Var}
    (h : catalogue.Branch p R F) :
    catalogue.Branch (p.rename e) (R.rename e) (renameTransition e F) := by
  obtain ⟨B, A, hB, hα, rfl⟩ := h
  refine ⟨renameTransition e B, renameTransition e A, ?_, alphaEquivalent_rename e hα,
    rename_underReset e R A⟩
  obtain ⟨J, U, hJ, hU, rfl⟩ := mixed_branch_raw.mp hB
  apply mixed_branch_raw.mpr
  refine ⟨renameJudgement e J, renameTransition e U, hJ.rename e, ?_, ?_⟩
  · rw [normalize_rename, hU]
    rfl
  · rw [rename_underReset, reset_rename_empty]

private theorem reset_rename_inverse (e : Equiv.Perm Clock) (R : ClockResetSet Clock) :
    (R.rename e).rename e.symm = R := by
  cases R
  simp [ClockResetSet.rename]

theorem ruleClosedFor_rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {F : TransitionForm Clock Var} {p : Predicate Clock Var}
    (h : catalogue.RuleClosedFor F p) :
    catalogue.RuleClosedFor (renameTransition e F) (p.rename e) := by
  rcases h with h | ⟨B, hB, hsub⟩
  · left
    rintro ⟨B, hB⟩
    apply h
    refine ⟨renameTransition e.symm B, ?_⟩
    have hh := branch_rename e.symm hB
    change catalogue.Branch ((p.rename e).rename e.symm)
      ((F.current.resets.rename e).rename e.symm) _ at hh
    simpa only [predicate_rename_inverse, reset_rename_inverse] using hh
  · exact Or.inr ⟨renameTransition e B, branch_rename e hB, subsumed_rename e hsub⟩

theorem ruleClosedFor_rename_iff [DecidableEq Clock] (e : Equiv.Perm Clock)
    (F : TransitionForm Clock Var) (p : Predicate Clock Var) :
    catalogue.RuleClosedFor (renameTransition e F) (p.rename e) ↔ catalogue.RuleClosedFor F p := by
  constructor
  · intro h
    simpa only [renameTransition_inverse, predicate_rename_inverse] using ruleClosedFor_rename e.symm h
  · exact ruleClosedFor_rename e

theorem branchwisePExpansion_rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {F G : TransitionForm Clock Var} {p : Predicate Clock Var}
    (h : catalogue.BranchwisePExpansion p F G) :
    catalogue.BranchwisePExpansion (p.rename e) (renameTransition e F) (renameTransition e G) := by
  rcases h with ⟨hc, rfl⟩ | ⟨B, hb, hf, hg, hm⟩
  · exact Or.inl ⟨ruleClosedFor_rename e hc, rfl⟩
  · refine Or.inr ⟨renameTransition e B, branch_rename e hb, subsumed_rename e hf,
      subsumed_rename e hg, ?_⟩
    intro H hF hB hG
    have hF' : SyntacticallySubsumed F (renameTransition e.symm H) := by
      simpa only [renameTransition_inverse] using subsumed_rename e.symm hF
    have hB' : SyntacticallySubsumed B (renameTransition e.symm H) := by
      simpa only [renameTransition_inverse] using subsumed_rename e.symm hB
    have hG' : SyntacticallySubsumed (renameTransition e.symm H) G := by
      simpa only [renameTransition_inverse] using subsumed_rename e.symm hG
    have hs := subsumed_rename e (hm _ hF' hB' hG')
    have he : renameTransition e (renameTransition e.symm H) = H :=
      renameTransition_inverse e.symm H
    rwa [he] at hs

theorem AlphaBranchwisePExpansion.rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {F G : TransitionForm Clock Var} {p : Predicate Clock Var}
    (h : AlphaBranchwisePExpansion p F G) :
    AlphaBranchwisePExpansion (p.rename e) (renameTransition e F) (renameTransition e G) := by
  obtain ⟨A, ha, hs⟩ := h
  exact ⟨renameTransition e A, nextAlphaPath_rename e ha, branchwisePExpansion_rename e hs⟩

end STLTableau.Section3.ConcreteContextual
