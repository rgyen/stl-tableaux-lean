import STLTableaux.ModelChecking.Preprocessing.NormalizedInputBranches
import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Syntax.FaithfulNormalizedSyntax

/-! Preservation of the normalized input grammar by normalization, scoped clock
renaming and arbitrary minimal contextual closures. No label pruning is used. -/

namespace STLTableau.Section3
variable {Clock Var : Type*}
abbrev Predicate.NormalizedReady := @Section4.Finiteness.predicateNormalizedReady Clock Var
abbrev Judgement.NormalizedReady := @Section4.Finiteness.judgementNormalizedReady Clock Var

attribute [local simp] Section4.Finiteness.predicateNormalizedReady
  Section4.Finiteness.judgementNormalizedReady

def Local.NormalizedReady : Local Clock Var → Prop
  | .predicate p => p.NormalizedReady
  | _ => True

def StateForm.NormalizedReady (S : StateForm Clock Var) : Prop := ∀ l ∈ S.locals, l.NormalizedReady

def TransitionForm.NormalizedReady (F : TransitionForm Clock Var) : Prop :=
  F.current.NormalizedReady ∧ ∀ N, F.nextPart = some N → N.NormalizedReady

namespace StateForm
@[simp] theorem normalizedReady_ofLocal (l : Local Clock Var) :
    (ofLocal l).NormalizedReady ↔ l.NormalizedReady := by
  simp [NormalizedReady,ofLocal]
@[simp] theorem normalizedReady_empty : (empty : StateForm Clock Var).NormalizedReady := by
  simp [NormalizedReady,empty]
@[simp] theorem normalizedReady_union (S T : StateForm Clock Var) :
    (S.union T).NormalizedReady ↔ S.NormalizedReady ∧ T.NormalizedReady := by
  simp only [NormalizedReady,union,Set.mem_union]
  aesop
end StateForm
namespace TransitionForm
@[simp] theorem normalizedReady_ofState (S : StateForm Clock Var) :
    (ofState S).NormalizedReady ↔ S.NormalizedReady := by
  simp [NormalizedReady,ofState]
@[simp] theorem normalizedReady_ofNextState (S : StateForm Clock Var) :
    (ofNextState S).NormalizedReady ↔ S.NormalizedReady := by
  simp [NormalizedReady,ofNextState]
@[simp] theorem normalizedReady_underReset
    (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock) :
    (F.underReset Λ).NormalizedReady ↔ F.NormalizedReady := Iff.rfl
@[simp] theorem normalizedReady_union (F G : TransitionForm Clock Var) :
    (F.union G).NormalizedReady ↔ F.NormalizedReady ∧ G.NormalizedReady := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [NormalizedReady,union,unionNext,hf,hg,StateForm.normalizedReady_union] <;> aesop

theorem normalize_normalizedReady (Ψ : Judgement Clock Var) {F : TransitionForm Clock Var}
    (hn : normalize? Ψ = some F) (h : Ψ.NormalizedReady) : F.NormalizedReady := by
  induction Ψ generalizing F with
  | terminal => cases hn; simp [Local.NormalizedReady]
  | clock c r a => cases hn; simp [StateForm.NormalizedReady,StateForm.ofGuard]
  | marker m => cases hn; simp [Local.NormalizedReady]
  | predicate p =>
      cases hn
      simpa only [normalizedReady_ofState, StateForm.normalizedReady_ofLocal, Local.NormalizedReady,
        Judgement.NormalizedReady, Section4.Finiteness.judgementNormalizedReady] using h
  | reset Λ Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          simp [normalize?,he] at hn
          subst F
          exact (normalizedReady_underReset G Λ).2 (ih he h)
  | conj Ψ Χ ihΨ ihΧ =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          cases hf : normalize? Χ with
          | none => simp [normalize?,he,hf] at hn
          | some H =>
              simp [normalize?,he,hf] at hn
              subst F
              exact (normalizedReady_union G H).2 ⟨ihΨ he h.1,ihΧ hf h.2⟩
  | next Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          cases hx : G.nextPart with
          | some N => simp [normalize?,he,hx] at hn
          | none =>
              simp [normalize?,he,hx] at hn
              subst F
              exact (normalizedReady_ofNextState G.current).2 (ih he h).1
end TransitionForm
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
@[simp] theorem Predicate.normalizedReady_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).NormalizedReady ↔ p.NormalizedReady := by
  cases p <;> rfl
@[simp] theorem Local.normalizedReady_rename (e : Equiv.Perm Clock) (l : Local Clock Var) :
    (l.rename e).NormalizedReady ↔ l.NormalizedReady := by
  cases l <;> simp [Local.NormalizedReady,Local.rename]
@[simp] theorem StateForm.normalizedReady_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).NormalizedReady ↔ S.NormalizedReady := by
  simp [StateForm.NormalizedReady,StateForm.rename]
@[simp] theorem StateForm.normalizedReady_alphaReset
    (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.alphaReset e).NormalizedReady ↔ S.NormalizedReady := by
  simp [StateForm.NormalizedReady,StateForm.alphaReset,StateForm.rename]
@[simp] theorem TransitionForm.normalizedReady_alphaOuter
    (e : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    (F.alphaOuter e).NormalizedReady ↔ F.NormalizedReady := by
  cases hn : F.nextPart <;>
    simp [TransitionForm.NormalizedReady,TransitionForm.alphaOuter,hn,StateForm.NormalizedReady,
      StateForm.alphaReset,StateForm.rename]
@[simp] theorem TransitionForm.normalizedReady_alphaNext
    (e : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    (F.alphaNext e).NormalizedReady ↔ F.NormalizedReady := by
  cases hn : F.nextPart <;>
    simp [TransitionForm.NormalizedReady,TransitionForm.alphaNext,hn]
theorem TransitionForm.AlphaEquivalent.normalizedReady {F G : TransitionForm Clock Var}
    (ha : F.AlphaEquivalent G) : F.NormalizedReady ↔ G.NormalizedReady := by
  induction ha with
  | refl => rfl
  | outer F e hf => exact F.normalizedReady_alphaOuter e
  | next F e hf => exact F.normalizedReady_alphaNext e
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

namespace ConcreteMixed

theorem branch_normalizedReady [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hB : catalogue.Branch p Λ B) (hp : p.NormalizedReady) : B.NormalizedReady := by
  rcases hB with h | h | h
  · obtain ⟨p₀,R,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact (TransitionForm.normalizedReady_underReset F Λ).2
      (TransitionForm.normalize_normalizedReady _ hn
        (STLTableau.Section4.Finiteness.finite_branch_normalizedReady hr hp hm))
  · obtain ⟨p₀,Bs,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact (TransitionForm.normalizedReady_underReset F Λ).2
      (TransitionForm.normalize_normalizedReady _ hn
        (STLTableau.Section4.Finiteness.infinite_branch_normalizedReady hr hp hm))
  · obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := h
    apply (TransitionForm.normalizedReady_underReset F Λ).2
    apply TransitionForm.normalize_normalizedReady _ hn
    cases kind <;> simpa [UnboundedClocked.opening,UnboundedClocked.formula,
      Judgement.ofUnbounded, Judgement.NormalizedReady,
      Predicate.ofUnbounded, Predicate.NormalizedReady,
      Section4.Finiteness.judgementNormalizedReady,
      Section4.Finiteness.predicateNormalizedReady] using hp
end ConcreteMixed
namespace ConcreteContextual

theorem branch_normalizedReady [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hB : catalogue.Branch p Λ B) (hp : p.NormalizedReady) : B.NormalizedReady := by
  obtain ⟨R,A,hr,ha,rfl⟩ := hB
  exact (TransitionForm.normalizedReady_underReset A Λ).2
    (ha.normalizedReady.mpr (ConcreteMixed.branch_normalizedReady hr hp))
end ConcreteContextual
end STLTableau.Section3

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

theorem SafeNormalization.normalizedReady {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (hn : SafeNormalization J F) :
    F.NormalizedReady ↔ judgementNormalizedReady J := by
  induction hn with
  | terminal => simp [Section3.Local.NormalizedReady, judgementNormalizedReady]
  | clock => simp [Section3.StateForm.NormalizedReady, Section3.StateForm.ofGuard,
      judgementNormalizedReady]
  | marker => simp [Section3.Local.NormalizedReady, judgementNormalizedReady]
  | predicate => simp [Section3.Local.NormalizedReady, judgementNormalizedReady]
  | conj _ _ _ ih ig =>
    simpa only [Section3.TransitionForm.normalizedReady_union, judgementNormalizedReady] using
      and_congr ih ig
  | reset _ _ _ ih => exact ih
  | @next J F _ hx ih =>
    have he : F.NormalizedReady ↔ F.current.NormalizedReady := by
      simp [Section3.TransitionForm.NormalizedReady, hx]
    exact (Section3.TransitionForm.normalizedReady_ofNextState F.current).trans (he.symm.trans ih)

end STLTableau.Section4.Finiteness

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm

theorem restrict_normalizedReady (F : TransitionForm Clock Var) :
    (F.restrictLocals Local.NormalizedReady Local.NormalizedReady).NormalizedReady := by
  refine ⟨fun l hl => hl.2, ?_⟩
  intro N hn
  obtain ⟨M,hm,rfl⟩ := Option.map_eq_some_iff.mp hn
  exact fun l hl => hl.2
end TransitionForm
namespace ConcreteContextual

theorem closure_normalizedReady [DecidableEq Clock]
    {anchor F : TransitionForm Clock Var}
    (hc : catalogue.IsClosure anchor F)
    (hnormalizedReady : anchor.NormalizedReady) : F.NormalizedReady := by
  have ha : SyntacticallySubsumed anchor
      (F.restrictLocals Local.NormalizedReady Local.NormalizedReady) :=
    hc.extension.restrictLocalsTarget _ _ hnormalizedReady.1
      (fun N M hn hm => hnormalizedReady.2 N hn)
  have hf : catalogue.IsClosed (F.restrictLocals Local.NormalizedReady Local.NormalizedReady) := by
    intro p hp
    have hpF : Local.predicate p ∈ F.current.locals := hp.1
    have hpr : p.NormalizedReady := hp.2
    rcases hc.closed p hpF with hnone | ⟨B,hB,hBF⟩
    · exact Or.inl hnone
    · have hnormalizedReadyB := branch_normalizedReady hB hpr
      exact Or.inr ⟨B,hB,hBF.restrictLocalsTarget _ _ hnormalizedReadyB.1
        (fun N M hn hm => hnormalizedReadyB.2 N hn)⟩
  have he := catalogue.minimal_restriction_eq hc Local.NormalizedReady Local.NormalizedReady ha hf
  rw [he]
  exact F.restrict_normalizedReady
end ConcreteContextual
end STLTableau.Section3

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

theorem derives_normalizedReady
    {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (hd : Derives N F) (hn : N.NormalizedReady) : F.NormalizedReady := by
  cases hd with
  | original hc _ =>
    exact ConcreteContextual.closure_normalizedReady hc
      ((Section3.TransitionForm.normalizedReady_ofState N).mpr hn)
  | resolved hd hi hf _ =>
    exact hf.normalizedReady.mpr (hd.normalizedReady
      (hi.normalizedReady.mp ((Section3.TransitionForm.normalizedReady_ofState N).mpr hn))).1

end STLTableau.Section4.Finiteness
