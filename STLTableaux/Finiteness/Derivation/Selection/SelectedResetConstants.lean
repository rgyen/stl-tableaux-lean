import STLTableaux.Finiteness.Derivation.Selection.SelectedAnnotationProvenance
import STLTableaux.Finiteness.Derivation.CanonicalResetMap

/-! Exact assignment provenance; inherited assignments remain distinguished
 from assignments of actual raw ledger entries. No clock-owner consistency is
 inferred from this value provenance. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

private theorem union_value_origin {R S : ClockResetSet Clock} {c : Clock} {a : NNReal}
    (h : (R.union S).value c=some a) : R.value c=some a ∨ S.value c=some a := by
  cases hr : R.value c with
  | none => exact Or.inr (by simpa only [ClockResetSet.union,hr] using h)
  | some b => exact Or.inl (by simpa only [ClockResetSet.union,hr] using h)

theorem currentResetMap_value_literal {J : MixedJ Clock Var} {c : Clock} {a : NNReal}
    (h : (currentResetMap J).value c=some a) : RawResetAt c a J := by
  induction J with
  | terminal | clock | marker | predicate | next => cases h
  | conj J K ih ik =>
      rcases union_value_origin h with h | h
      · exact Or.inl (ih h)
      · exact Or.inr (ik h)
  | reset R J ih =>
      rcases union_value_origin h with h | h
      · exact Or.inr (ih h)
      · exact Or.inl h

private theorem fold_reset_empty (Xs : List (MixedJ Clock Var))
    (h : ∀X∈Xs,currentResetMap X=ClockResetSet.empty)
    {K : MixedJ Clock Var} (hk : foldCurrent Xs=some K) : currentResetMap K=ClockResetSet.empty := by
  induction Xs generalizing K with
  | nil => cases hk
  | cons X Xs ih =>
      rw [foldCurrent_cons] at hk
      have he := Option.some.inj hk
      subst K
      cases ht : foldCurrent Xs with
      | none => exact h X List.mem_cons_self
      | some T =>
          change (currentResetMap X).union (currentResetMap T)=_
          rw [h X List.mem_cons_self,ih (fun Y hy => h Y (List.mem_cons_of_mem X hy)) ht]
          rfl

private theorem residual_reset_empty (L : List (Local Clock Var)) (Ns : List (MixedJ Clock Var))
    {K : MixedJ Clock Var} (hk : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)=some K) :
    currentResetMap K=ClockResetSet.empty := by
  apply fold_reset_empty _ _ hk
  intro X hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨l,_,rfl⟩ := List.mem_map.1 hx
    cases l <;> rfl
  · obtain ⟨J,_,rfl⟩ := List.mem_map.1 hx
    rfl

private theorem copy_value_origin {R : ClockResetSet Clock} {L : List (Local Clock Var)}
    {c : Clock} {a : NNReal} (h : (copyActiveResets R L).value c=some a) : R.value c=some a := by
  have he := congrArg (fun S : ClockResetSet Clock => S.value c) (copyActiveResets_absorb R L)
  simpa only [ClockResetSet.union,h] using he.symm

variable [DecidableEq Clock]

theorem OrdinaryChoice.child_reset_provenance
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned)
    {c : Clock} {a : NNReal} (h : choice.childR.value c=some a) :
    R.value c=some a ∨ RawResetAt c a choice.B := by
  rw [choice.reset_origin] at h
  cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) with
  | none =>
      simp only [ordinarySelectedInput,hf] at h
      exact Or.inr (currentResetMap_value_literal h)
  | some Γ =>
      have he := residual_reset_empty _ _ hf
      simp only [ordinarySelectedInput,hf,currentResetMap,he] at h
      rcases union_value_origin h with h | h
      · exact Or.inr (currentResetMap_value_literal h)
      · rcases union_value_origin h with h | h
        · cases h
        · exact Or.inl (copy_value_origin h)

omit [DecidableEq Clock] in
private theorem outside_reset_map (G : List (Section3.Guard Clock)) (R : ClockResetSet Clock)
    (K : MixedJ Clock Var) : currentResetMap (outsidePending G R K)=(currentResetMap K).union R := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,currentResetMap]
  | some A =>
      have he : currentResetMap A=ClockResetSet.empty := by
        apply fold_reset_empty _ _ hg
        intro X hx
        obtain ⟨g,_,rfl⟩ := List.mem_map.1 hx
        cases g
        rfl
      simp only [outsidePending,hg,currentResetMap,he]
      rfl

omit [DecidableEq Clock] in
private theorem canonical_reset_map {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) : currentResetMap owned.canonical=R := by
  obtain ⟨F,hF⟩ := owned.input_safe
  rw [← safe_reset_map hF]
  exact owned.current_resets_of_safe hF

/-- Every assignment in this tree's full current output is inherited with its
 exact value or appears at the same clock in an actual source-bearing entry. -/
theorem SelectedTree.current_reset_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {c : Clock} {a : NNReal}
    (h : (currentResetMap H).value c=some a) :
    R.value c=some a ∨ ∃entry∈T.rawLedger,RawResetAt c a entry.body := by
  induction T with
  | zero leaf hz => exact Or.inl (by rwa [canonical_reset_map leaf] at h)
  | ordinary leaf choice tail ih =>
      rw [outside_reset_map] at h
      rcases union_value_origin h with h | h
      · simp only [currentResetMap,ClockResetSet.union,ClockResetSet.empty] at h
        rcases ih h with h | ⟨entry,he,ha⟩
        · rcases choice.child_reset_provenance h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨_,List.mem_cons_self,h⟩
        · exact Or.inr ⟨entry,List.mem_cons_of_mem _ he,ha⟩
      · exact Or.inl h
  | required leaf choice tail ih =>
      rw [outside_reset_map] at h
      rcases union_value_origin h with h | h
      · rcases ih h with h | h
        · exact Or.inl (copy_value_origin h)
        · exact Or.inr h
      · exact Or.inl h
  | optional leaf choice upper forced tail ih =>
      rw [outside_reset_map] at h
      rcases union_value_origin h with h | h
      · rw [outside_reset_map] at h
        rcases union_value_origin h with h | h
        · simp only [currentResetMap,ClockResetSet.union,ClockResetSet.empty] at h
          rcases ih h with h | ⟨entry,he,ha⟩
          · rcases upper.child_reset_provenance h with h | h
            · exact Or.inl (copy_value_origin h)
            · exact Or.inr ⟨_,List.mem_cons_self,h⟩
          · exact Or.inr ⟨entry,List.mem_cons_of_mem _ he,ha⟩
        · exact Or.inl (copy_value_origin h)
      · exact Or.inl h

theorem SelectedTree.normalized_current_reset_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {c : Clock} {a : NNReal} (h : F.current.resets.value c=some a) :
    R.value c=some a ∨ ∃entry∈T.rawLedger,
      RawResetAt c a entry.body ∧ a∈branchConstants entry.source := by
  rw [safe_reset_map hSafe] at h
  rcases T.current_reset_provenance h with h | ⟨entry,he,ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨entry,he,ha,entry.reset_constant ha⟩

end STLTableau.Section4.Finiteness
