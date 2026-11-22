import STLTableaux.Finiteness.Derivation.Selection.SelectedPolicy
import STLTableaux.Finiteness.Derivation.Pending.PendingCompletionBase

/-! Realization of the same selected proof tree as an actual Resolve witness.
No semantic assumptions enter this structural induction. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem guard_weight_zero (G : List (Section3.Guard Clock)) (C : MixedJ Clock Var)
    (h : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some C) :
    pendingWeight C = 0 := by
  induction G generalizing C with
  | nil => simp [foldCurrent] at h
  | cons g gs ih =>
    rw [List.map_cons,foldCurrent_cons] at h
    have he := Option.some.inj h
    subst C
    cases ht : foldCurrent (gs.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none => cases g; rfl
    | some T =>
      have hz := ih T ht
      cases g; simpa only [prependCurrent,pendingWeight,Section3.Guard.toJudgement,Nat.zero_add] using hz

private theorem outside_realize
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (Body : MixedJ Clock Var)
    (hb : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Body)
    {H Er : MixedJ Clock Var} (D : Resolve (.reset R Body) H Er) :
    Nonempty (Resolve J
      (match foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
       | none => H | some G => .conj G H)
      (match foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
       | none => Er | some G => .conj G Er)) := by
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    have he : .reset R Body = owned.canonical := by
      simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
    exact ⟨.structural (owned.regroup.trans (he ▸ .refl _)) D⟩
  | some G =>
    have he : .conj G (.reset R Body) = owned.canonical := by
      simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
    exact ⟨.structural (owned.regroup.trans (he ▸ .refl _))
      (.conj (PendingCompletionBase.resolve_zero G (guard_weight_zero _ _ hg)) D)⟩

private theorem ordinary_realize
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var}
    {R : ClockResetSet Clock} {W : Set Clock} (owned : OwnedPending J R W)
    (choice : OrdinaryChoice E owned) {H Er : MixedJ Clock Var}
    (tail : Resolve (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
        owned.nextInputs.map Section3.Judgement.next))) H Er) :
    Nonempty (Resolve J (outsidePending owned.guards R (.conj (.predicate choice.p) H))
      (outsidePending owned.guards R Er)) := by
  obtain ⟨Body,hBody,hExpose⟩ := owned_selected_exposure owned choice.p choice.left choice.right choice.split
  cases hΓ : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    have hfresh : FreshWithoutContext choice.p choice.B := by
      simpa only [ordinarySelectedFresh,hΓ] using choice.fresh
    have htail : Resolve choice.B H Er := by simpa only [ordinarySelectedInput,hΓ] using tail
    rw [hΓ] at hExpose
    have D : Resolve (.reset R Body) (.reset R (.conj (.predicate choice.p) H)) (.reset R Er) :=
      .structural (.reset R hExpose) (.reset R (.expandSolo choice.branch choice.maximal.1 hfresh htail))
    exact outside_realize owned Body hBody D
  | some Γ =>
    have hfresh : FreshFor choice.p choice.B (.reset (copyActiveResets R (choice.left++choice.right)) Γ) := by
      simpa only [ordinarySelectedFresh,hΓ] using choice.fresh
    have htail : Resolve (.conj choice.B (.reset (copyActiveResets R (choice.left++choice.right)) Γ)) H Er := by
      simpa only [ordinarySelectedInput,hΓ] using tail
    rw [hΓ] at hExpose
    have hd := (copied_remaining_protected owned ∅ (Set.disjoint_empty _) choice.p
      choice.left choice.right choice.split).mono_right
      ((free_subset_syntax (.predicate choice.p)).trans Set.subset_union_right)
    have Dscope : Resolve (.reset R (.conj (.predicate choice.p) Γ))
        (.reset R (.conj (.predicate choice.p) H)) (.reset R Er) :=
      .structural (copied_source_exposure R (choice.left++choice.right) choice.p Γ hd)
        (.reset R (.expandCtx choice.branch choice.maximal.1 hfresh htail))
    exact outside_realize owned Body hBody (.structural (.reset R hExpose) Dscope)

theorem SelectedTree.realize_nonempty
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : Nonempty (Resolve J H Er) := by
  induction T with
  | zero owned hz => exact ⟨.structural owned.regroup (PendingCompletionBase.resolve_zero _ hz)⟩
  | ordinary owned choice tail ih =>
    obtain ⟨D⟩ := ih
    exact ordinary_realize owned choice D
  | required owned choice tail ih =>
    obtain ⟨D⟩ := ih
    obtain ⟨Body,hBody,⟨Dscope⟩⟩ := owned_boundary_copied_backward owned true choice.c choice.d
      choice.m choice.ell choice.kind choice.I choice.phi choice.left choice.right choice.rest
      choice.split choice.selection choice.right_zero choice.frozen choice.Gamma _ _ choice.residual D
    exact outside_realize owned Body hBody Dscope
  | optional owned choice upper forced tail ih =>
    obtain ⟨D⟩ := ih
    obtain ⟨Dup⟩ := ordinary_realize choice.child upper D
    obtain ⟨Body,hBody,⟨Dscope⟩⟩ := owned_boundary_copied_backward owned false choice.c choice.d
      choice.m choice.ell choice.kind choice.I choice.phi choice.left choice.right choice.rest
      choice.split choice.selection choice.right_zero choice.frozen choice.Gamma _ _ choice.residual Dup
    exact outside_realize owned Body hBody Dscope

noncomputable def SelectedTree.realize
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : Resolve J H Er := Classical.choice T.realize_nonempty

end STLTableau.Section4.Finiteness
