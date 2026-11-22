import STLTableaux.Closure.Catalogue.FaithfulContextualFreshBranch
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm

theorem alphaNext_bodyFreeClocks (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    (Φ.alphaNext e).bodyFreeClocks = Φ.bodyFreeClocks := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext,bodyFreeClocks,hn]
  | some N => simp [alphaNext,bodyFreeClocks,hn,N.alphaReset_freeClocks e (hfix N hn)]
end TransitionForm

/-- A subsumed next component cannot leave one of its local free clocks bound
in the target. Thus a target-safe permutation is also source-safe. -/
theorem SyntacticallySubsumed.next_fix_of_subsumed {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (e : Equiv.Perm Clock)
    (hfix : ∀ M, Ψ.nextPart = some M →
      ∀ c ∈ M.localClocks \ M.resets.clocks, e c = c) :
    ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c := by
  intro N hn c hc
  obtain ⟨M,hm,hNM,hfresh⟩ := h.next N hn
  apply hfix M hm c
  constructor
  · obtain ⟨l,hl,hcl⟩ := hc.1
    exact ⟨l,hNM.locals hl,hcl⟩
  · exact fun hM => Set.disjoint_left.1 hfresh hM hc

namespace ComponentsIncluded
private theorem alphaReset {S T : StateForm Clock Var} (h : ComponentsIncluded S T)
    (e : Equiv.Perm Clock) : ComponentsIncluded (S.alphaReset e) (T.alphaReset e) := by
  refine ⟨h.guards,?_,Set.image_mono h.locals⟩
  intro c a hc
  exact h.resets (e.symm c) a hc
end ComponentsIncluded

theorem SyntacticallySubsumed.alphaNext {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (e : Equiv.Perm Clock)
    (hfix : ∀ M, Ψ.nextPart = some M →
      ∀ c ∈ M.localClocks \ M.resets.clocks, e c = c) :
    SyntacticallySubsumed (Φ.alphaNext e) (Ψ.alphaNext e) := by
  have hfΦ := h.next_fix_of_subsumed e hfix
  refine ⟨h.current,?_,?_⟩
  · change Disjoint Ψ.current.resets.clocks
      ((Φ.alphaNext e).bodyFreeClocks \ Φ.current.resets.clocks)
    rw [TransitionForm.alphaNext_bodyFreeClocks Φ e hfΦ]
    exact h.outerFresh
  · intro N hn
    cases hN : Φ.nextPart with
    | none => simp [TransitionForm.alphaNext,hN] at hn
    | some N₀ =>
        have he : N = N₀.alphaReset e := by
          simpa [TransitionForm.alphaNext,hN] using hn.symm
        subst N
        obtain ⟨M₀,hM,hNM,hfresh⟩ := h.next N₀ hN
        refine ⟨M₀.alphaReset e,by simp [TransitionForm.alphaNext,hM],hNM.alphaReset e,?_⟩
        change Disjoint (M₀.resets.rename e).clocks
          ((N₀.alphaReset e).localClocks \ (N₀.resets.rename e).clocks)
        rw [ClockResetSet.clocks_rename,StateForm.localClocks_alphaReset,
          ClockResetSet.clocks_rename,← Set.image_sdiff e.injective]
        apply Set.disjoint_left.2
        rintro c ⟨x,hx,hxe⟩ ⟨y,hy,hye⟩
        have he : x = y := e.injective (hxe.trans hye.symm)
        subst y
        exact Set.disjoint_left.1 hfresh hx hy
namespace Predicate
@[simp] theorem rename_inverse (p : Predicate Clock Var) (e : Equiv.Perm Clock) :
    (p.rename e).rename e.symm = p := by cases p <;> simp [rename]
end Predicate
namespace Local
@[simp] theorem rename_inverse (l : Local Clock Var) (e : Equiv.Perm Clock) :
    (l.rename e).rename e.symm = l := by cases l <;> simp [rename]
end Local
namespace StateForm
private theorem reset_rename_inverse (Λ : ClockResetSet Clock) (e : Equiv.Perm Clock) :
    (Λ.rename e).rename e.symm = Λ := by cases Λ; simp [ClockResetSet.rename]
@[simp] theorem alphaReset_inverse (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.alphaReset e).alphaReset e.symm = S := by
  apply StateForm.ext_components
  · rfl
  · exact reset_rename_inverse S.resets e
  · change Local.rename e.symm '' (Local.rename e '' S.locals) = S.locals
    simp only [Set.image_image,Function.comp_def,Local.rename_inverse,Set.image_id']
theorem localFree_alphaReset (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.alphaReset e).localClocks \ (S.alphaReset e).resets.clocks =
      e '' (S.localClocks \ S.resets.clocks) := by
  change (S.rename e).localClocks \ (S.resets.rename e).clocks = _
  rw [localClocks_rename,ClockResetSet.clocks_rename]
  exact (Set.image_sdiff e.injective _ _).symm
end StateForm
namespace TransitionForm
@[simp] theorem alphaNext_inverse (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (Φ.alphaNext e).alphaNext e.symm = Φ := by
  cases Φ with
  | mk S N => cases N <;> simp [alphaNext]

theorem alphaNext_fix_inverse (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    ∀ N, (Φ.alphaNext e).nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e.symm c = c := by
  intro N hn c hc
  obtain ⟨M,hm,he⟩ := Option.map_eq_some_iff.mp hn
  subst N
  rw [StateForm.localFree_alphaReset] at hc
  obtain ⟨x,hx,rfl⟩ := hc
  exact (e.symm_apply_apply x).trans (hfix M hm x hx).symm
end TransitionForm
end STLTableau.Section3
