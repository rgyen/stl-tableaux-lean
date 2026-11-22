import STLTableaux.Closure.Normalization.ClosureCompatibility

/-! Transport of literal subsumption through capture-free renaming of inherited
next binders. The current source predicate and reset valuation are unchanged. -/
namespace STLTableau
open scoped STL
variable {Clock Var : Type*}

namespace IntervalPredicate
@[simp] theorem rename_inverse (p : IntervalPredicate Clock Var) (e : Equiv.Perm Clock) :
    (p.rename e).rename e.symm = p := by cases p <;> simp [rename]
end IntervalPredicate
namespace ClockResetSet
@[simp] theorem rename_inverse (Λ : ClockResetSet Clock) (e : Equiv.Perm Clock) :
    (Λ.rename e).rename e.symm = Λ := by
  cases Λ
  simp [rename]
end ClockResetSet
namespace Judgement
@[simp] theorem rename_inverse (J : Judgement Clock Var) (e : Equiv.Perm Clock) :
    (J.rename e).rename e.symm = J := by
  induction J with
  | predicate p => simp [rename]
  | reset Λ J ih => simp [rename,ih]
  | next J ih => simp [rename,ih]
  | conj J K ihJ ihK => simp [rename,ihJ,ihK]
  | _ => simp [rename]
end Judgement

namespace StateForm

theorem localFree_alphaReset (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.alphaReset e).localClocks \ (S.alphaReset e).resets.clocks =
      e '' (S.localClocks \ S.resets.clocks) := by
  change (S.rename e).localClocks \ (S.resets.rename e).clocks = _
  rw [localClocks_rename, ClockResetSet.clocks_rename]
  exact (Set.image_sdiff e.injective _ _).symm

@[simp] theorem alphaReset_inverse (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.alphaReset e).alphaReset e.symm = S := by
  apply StateForm.ext (S₁ := (S.alphaReset e).alphaReset e.symm) (S₂ := S)
  · rfl
  · exact ClockResetSet.rename_inverse S.resets e
  · change Judgement.rename e.symm '' (Judgement.rename e '' S.locals) = S.locals
    simp only [Set.image_image, Function.comp_def, Judgement.rename_inverse, Set.image_id']

end StateForm
namespace TransitionForm

theorem bodyFreeClocks_alphaNext (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    (Φ.alphaNext e).bodyFreeClocks = Φ.bodyFreeClocks := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, bodyFreeClocks, hn]
  | some N =>
      simp [alphaNext, bodyFreeClocks, hn, N.alphaReset_freeClocks e (hfix N hn)]

private theorem nextPart_alphaNext {Φ : TransitionForm Clock Var} {e : Equiv.Perm Clock}
    {M : StateForm Clock Var} (h : (Φ.alphaNext e).nextPart = some M) :
    ∃ N, Φ.nextPart = some N ∧ M = N.alphaReset e := by
  change Φ.nextPart.map (StateForm.alphaReset e) = some M at h
  obtain ⟨N,hN,hM⟩ := Option.map_eq_some_iff.mp h
  exact ⟨N,hN,hM.symm⟩

@[simp] theorem alphaNext_inverse (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (Φ.alphaNext e).alphaNext e.symm = Φ := by
  cases Φ with
  | mk S N => cases N <;> simp [alphaNext]

theorem alphaNext_fix_inverse (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    ∀ N, (Φ.alphaNext e).nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e.symm c = c := by
  intro N hN c hc
  obtain ⟨M,hM,rfl⟩ := nextPart_alphaNext hN
  rw [StateForm.localFree_alphaReset] at hc
  obtain ⟨x,hx,rfl⟩ := hc
  exact (e.symm_apply_apply x).trans (hfix M hM x hx).symm

end TransitionForm
namespace SyntacticallySubsumed

/-- Component inclusion and the capture-avoidance side conditions transport
under the same next-binder permutation. -/
theorem alphaNext {Φ Ψ : TransitionForm Clock Var} (h : Φ ⊑ Ψ)
    (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    Φ.alphaNext e ⊑ Ψ.alphaNext e := by
  refine ⟨h.requiredResets,h.currentConstraints,h.currentResets,h.currentLocals,?_,?_,?_,?_,?_,?_⟩
  · simpa only [TransitionForm.alphaNext, Option.isSome_map] using h.nextShape
  · intro M N hM hN
    obtain ⟨M₀,hm,rfl⟩ := TransitionForm.nextPart_alphaNext hM
    obtain ⟨N₀,hn,rfl⟩ := TransitionForm.nextPart_alphaNext hN
    exact h.nextConstraints M₀ N₀ hm hn
  · intro M N hM hN
    obtain ⟨M₀,hm,rfl⟩ := TransitionForm.nextPart_alphaNext hM
    obtain ⟨N₀,hn,rfl⟩ := TransitionForm.nextPart_alphaNext hN
    intro c a ha
    exact h.nextResets M₀ N₀ hm hn (e.symm c) a ha
  · intro M N hM hN
    obtain ⟨M₀,hm,rfl⟩ := TransitionForm.nextPart_alphaNext hM
    obtain ⟨N₀,hn,rfl⟩ := TransitionForm.nextPart_alphaNext hN
    exact Set.image_mono (h.nextLocals M₀ N₀ hm hn)
  · change Disjoint (Ψ.current.resets.clocks \ Φ.current.resets.clocks)
      (Φ.alphaNext e).bodyFreeClocks
    rw [TransitionForm.bodyFreeClocks_alphaNext Φ e hfix]
    exact h.outerFresh
  · intro M N hM hN
    obtain ⟨M₀,hm,rfl⟩ := TransitionForm.nextPart_alphaNext hM
    obtain ⟨N₀,hn,rfl⟩ := TransitionForm.nextPart_alphaNext hN
    have hold := h.nextFresh M₀ N₀ hm hn
    have hfree : (⋃ x ∈ M₀.locals, x.freeClocks \ M₀.resets.clocks) =
        M₀.localClocks \ M₀.resets.clocks := by ext c; simp [StateForm.localClocks]; aesop
    have hnew : (⋃ x ∈ (M₀.alphaReset e).locals,
        x.freeClocks \ (M₀.alphaReset e).resets.clocks) =
        (M₀.alphaReset e).localClocks \ (M₀.alphaReset e).resets.clocks := by
      ext c; simp [StateForm.localClocks]; aesop
    rw [hfree] at hold
    rw [hnew, StateForm.localFree_alphaReset]
    change Disjoint ((N₀.resets.rename e).clocks \ (M₀.resets.rename e).clocks) _
    rw [ClockResetSet.clocks_rename, ClockResetSet.clocks_rename, ← Set.image_sdiff e.injective]
    exact (Set.disjoint_image_iff e.injective).2 hold

/-- A capture-free permutation for a larger form fixes the unbound
next-local names of every subsumed smaller form. -/
theorem next_fix_of_subsumed {Φ Ψ : TransitionForm Clock Var} (h : Φ ⊑ Ψ)
    (e : Equiv.Perm Clock)
    (hfix : ∀ N, Ψ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    ∀ M, Φ.nextPart = some M →
      ∀ c ∈ M.localClocks \ M.resets.clocks, e c = c := by
  intro M hm c hc
  have hsome := h.nextShape (by simp [hm])
  cases hn : Ψ.nextPart with
  | none => simp [hn] at hsome
  | some N =>
      apply hfix N hn c
      obtain ⟨J,hJ,hcJ⟩ := Set.mem_iUnion₂.mp hc.1
      refine ⟨Set.mem_iUnion₂.mpr ⟨J,h.nextLocals M N hm hn hJ,hcJ⟩, ?_⟩
      intro hreset
      exact Set.disjoint_left.1 (h.nextFresh M N hm hn) ⟨hreset,hc.2⟩
        (Set.mem_iUnion₂.mpr ⟨J,hJ,hcJ,hc.2⟩)

end SyntacticallySubsumed
namespace AlphaBranchRepresentation
variable [DecidableEq Clock]

/-- Rule closure transports through source next-binder alpha-conversion.
The represented branch is alpha-converted by the same permutation. -/
theorem ruleClosed_alphaNext {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (h : expansionRules.RuleClosedFor Φ p) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    expansionRules.RuleClosedFor (Φ.alphaNext e) p := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hn | hb
  · exact Or.inl hn
  · obtain ⟨R,hR,Ψ,hΨ,B,hB,hsub⟩ := hb
    have hBfix := hsub.next_fix_of_subsumed e hfix
    exact Or.inr ⟨R,hR,Ψ,hΨ,B.alphaNext e,
      hB.transport (.next B e hBfix), hsub.alphaNext e hBfix⟩

theorem ruleClosed_alphaNext_iff {Φ : TransitionForm Clock Var} {p : IntervalPredicate Clock Var}
    (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    expansionRules.RuleClosedFor (Φ.alphaNext e) p ↔ expansionRules.RuleClosedFor Φ p := by
  constructor
  · intro h
    have hh := ruleClosed_alphaNext h e.symm (Φ.alphaNext_fix_inverse e hfix)
    simpa only [TransitionForm.alphaNext_inverse] using hh
  · exact fun h => ruleClosed_alphaNext h e hfix

theorem rank_alphaNext (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    expansionRules.rank (Φ.alphaNext e) = expansionRules.rank Φ := by
  have he : expansionRules.rankEntry (Φ.alphaNext e) = expansionRules.rankEntry Φ := by
    funext J
    cases J <;> simp only [ExpansionRules.rankEntry]
    case predicate p => rw [ruleClosed_alphaNext_iff e hfix]
  simp only [ExpansionRules.rank, he]
  rfl

end AlphaBranchRepresentation
end STLTableau
