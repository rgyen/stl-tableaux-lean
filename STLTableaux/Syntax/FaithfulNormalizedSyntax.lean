import STLTableaux.Closure.Subsumption.FaithfulClosureRestriction
import STLTableaux.Closure.Correctness.MixedConcreteClosure
import STLTableaux.ModelChecking.Preprocessing.Admissibility

/-! The internal mixed grammar, including Boolean constants and both finite
and infinite bounds. The narrower normalized input is defined in InputSyntax.lean.
Readiness is syntactic and requires distinct clocks in the `↑↓` form. -/
namespace STLTableau
namespace Formula
variable {Var : Type*}
inductive MixedReady : Formula Var → Prop
  | truth : MixedReady .truth
  | falsity : MixedReady falsity
  | atom (a : AtomicProposition Var) : MixedReady (.atom a)
  | and {φ ψ} : MixedReady φ → MixedReady ψ → MixedReady (.and φ ψ)
  | or {φ ψ} : MixedReady φ → MixedReady ψ → MixedReady (Formula.or φ ψ)
  | until {φ ψ} : MixedReady φ → MixedReady ψ → MixedReady (untimedUntil φ ψ)
  | release {φ ψ} : MixedReady φ → MixedReady ψ →
      MixedReady (Formula.release (.unbounded 0) φ ψ)
  | eventually (I : TimeInterval) {φ} : MixedReady φ → MixedReady (eventually I φ)
  | always (I : TimeInterval) {φ} : MixedReady φ → MixedReady (always I φ)

@[simp] theorem mixedReady_and {φ ψ : Formula Var} :
    (Formula.and φ ψ).MixedReady ↔ φ.MixedReady ∧ ψ.MixedReady := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · exact fun h => .and h.1 h.2
@[simp] theorem mixedReady_or {φ ψ : Formula Var} :
    (Formula.or φ ψ).MixedReady ↔ φ.MixedReady ∧ ψ.MixedReady := by
  constructor
  · intro h; cases h; exact ⟨by assumption,by assumption⟩
  · exact fun h => .or h.1 h.2
@[simp] theorem mixedReady_until {φ ψ : Formula Var} :
    (untimedUntil φ ψ).MixedReady ↔ φ.MixedReady ∧ ψ.MixedReady := by
  constructor
  · intro h; cases h
    · exact ⟨by assumption,by assumption⟩
    · exact ⟨.truth,by assumption⟩
  · exact fun h => .until h.1 h.2
@[simp] theorem mixedReady_release {φ ψ : Formula Var} :
    (Formula.release (.unbounded 0) φ ψ).MixedReady ↔ φ.MixedReady ∧ ψ.MixedReady := by
  constructor
  · intro h; cases h
    · exact ⟨by assumption,by assumption⟩
  · exact fun h => .release h.1 h.2
@[simp] theorem mixedReady_eventually {φ : Formula Var} {I : TimeInterval} :
    (Formula.eventually I φ).MixedReady ↔ φ.MixedReady := by
  constructor
  · intro h; cases h <;> assumption
  · exact .eventually I
@[simp] theorem mixedReady_always {φ : Formula Var} {I : TimeInterval} :
    (Formula.always I φ).MixedReady ↔ φ.MixedReady := by
  constructor
  · intro h; cases h <;> assumption
  · exact .always I

end Formula
end STLTableau

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Predicate

def Ready : Predicate Clock Var → Prop
  | .plain φ => φ.MixedReady
  | .upper _ _ _ _ φ => φ.MixedReady
  | .bounded c d _ _ _ _ φ => c ≠ d ∧ φ.MixedReady

end Predicate
namespace Judgement

def Ready : Judgement Clock Var → Prop
  | .predicate p => p.Ready
  | .conj F G => F.Ready ∧ G.Ready
  | .reset _ F | .next F => F.Ready
  | _ => True

end Judgement
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Judgement
@[simp] theorem ready_finiteLT (c : Clock) (m : Marker) (a : NNReal) :
    (ofFinite (STLTableau.Judgement.markedLT c m a) : Judgement Clock Var).Ready := by
  cases m <;> trivial
@[simp] theorem ready_finiteGT (c : Clock) (m : Marker) (a : NNReal) :
    (ofFinite (STLTableau.Judgement.markedGT c m a) : Judgement Clock Var).Ready := by
  cases m <;> trivial
@[simp] theorem ready_infiniteLT (c : Clock) (m : Marker) (a : NNReal) :
    (ofUnbounded (UnboundedClocked.Node.lt c m a) : Judgement Clock Var).Ready := by
  cases m <;> trivial
@[simp] theorem ready_infiniteGT (c : Clock) (m : Marker) (a : NNReal) :
    (ofUnbounded (UnboundedClocked.Node.gt c m a) : Judgement Clock Var).Ready := by
  cases m <;> trivial
end Judgement
namespace ConcreteFinite
set_option maxHeartbeats 1000000 in
theorem raw_ready [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) (hp : (Predicate.ofFinite p).Ready)
    {B : STLTableau.Judgement Clock Var} (hB : B ∈ R.branches) :
    (Judgement.ofFinite B).Ready := by
  classical
  cases hr <;>
    simp only [ExpansionRule.plainAnd, ExpansionRule.plainOr,
      ExpansionRule.plainUntil, ExpansionRule.plainRelease,
      ExpansionRule.openEventually, ExpansionRule.openAlways,
      ExpansionRule.upperAlways, ExpansionRule.boundedAlways,
      ExpansionRule.upperEventually, ExpansionRule.boundedEventually,
      List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Judgement.Ready, Judgement.ofFinite, Predicate.Ready, Predicate.ofFinite,
      ExpansionRule.upperAlways_defer, ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer, ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish, ExpansionRule.upperEventually_defer,
      ExpansionRule.upperEventually_check, ExpansionRule.boundedEventually_defer,
      ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish ] <;>
    (try split <;> trivial)
end ConcreteFinite

namespace ConcreteInfinite
open UnboundedClocked
set_option maxHeartbeats 1000000 in
theorem raw_ready [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) (hp : (Predicate.ofUnbounded p).Ready)
    {B : Node Clock Var} (hB : B ∈ Bs) :
    (Judgement.ofUnbounded B).Ready := by
  classical
  cases hr <;>
    simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
      boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_append] at hB <;>
    (try split_ifs at hB) <;>
    (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Judgement.Ready, Judgement.ofUnbounded, Predicate.Ready,
      Predicate.ofUnbounded, upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer,
      boundedAlwaysCheck, alwaysWait, alwaysLast, upperEventuallyDefer,
      upperEventuallyCheck, boundedEventuallyDefer, boundedEventuallyCheck,
      boundedEventuallyFinish] <;>
    (try split <;> trivial)
end ConcreteInfinite
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Predicate

theorem Ready.admitted [DecidableEq Clock] [Nontrivial Clock]
    {p : Predicate Clock Var} (h : p.Ready) : ConcreteMixed.catalogue.Admitted p := by
  obtain ⟨c,d,hcd⟩ := exists_pair_ne Clock
  change ConcreteFinite.Admitted p ∨ ConcreteInfinite.Admitted p ∨ ConcreteOpening.Admitted p
  cases p with
  | plain φ =>
      cases h with
      | truth => exact Or.inl (Or.inl trivial)
      | falsity => exact Or.inl (Or.inl trivial)
      | atom a => exact Or.inl (Or.inl trivial)
      | and hφ hψ => exact Or.inl (Or.inr ⟨_,_,rfl,.plainAnd _ _⟩)
      | or hφ hψ => exact Or.inl (Or.inr ⟨_,_,rfl,.plainOr _ _⟩)
      | «until» hφ hψ => exact Or.inl (Or.inr ⟨_,_,rfl,.plainUntil _ _⟩)
      | release hφ hψ => exact Or.inl (Or.inr ⟨_,_,rfl,.plainRelease _ _⟩)
      | eventually I hφ =>
          cases I with
          | bounded I => exact Or.inl (Or.inr ⟨_,_,rfl,.openEventually c I _⟩)
          | unbounded a => exact Or.inr (Or.inr (Or.inr ⟨c,.eventually,a,_,rfl⟩))
      | always I hφ =>
          cases I with
          | bounded I => exact Or.inl (Or.inr ⟨_,_,rfl,.openAlways c I _⟩)
          | unbounded a => exact Or.inr (Or.inr (Or.inr ⟨c,.always,a,_,rfl⟩))
  | upper e b kind I φ =>
      obtain ⟨f,hef⟩ := exists_ne e
      cases I with
      | bounded I =>
          left; right
          cases kind
          · exact ⟨_,_,rfl,.upperAlways e f b I φ (Ne.symm hef)⟩
          · exact ⟨_,_,rfl,.upperEventually e f b I φ (Ne.symm hef)⟩
      | unbounded a =>
          right; left; right
          cases kind
          · exact ⟨_,_,rfl,.upperAlways e f b a φ (Ne.symm hef)⟩
          · exact ⟨_,_,rfl,.upperEventually e f b a φ (Ne.symm hef)⟩
  | bounded e f b q kind I φ =>
      cases I with
      | bounded I =>
          left; right
          cases kind
          · exact ⟨_,_,rfl,.boundedAlways e f b q I φ h.1⟩
          · exact ⟨_,_,rfl,.boundedEventually e f b q I φ h.1⟩
      | unbounded a =>
          right; left; right
          cases kind
          · exact ⟨_,_,rfl,.boundedAlways e f b q a φ h.1⟩
          · exact ⟨_,_,rfl,.boundedEventually e f b q a φ h.1⟩
end Predicate
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
def Local.Ready : Local Clock Var → Prop
  | .predicate p => p.Ready
  | _ => True

def StateForm.Ready (S : StateForm Clock Var) : Prop := ∀ l ∈ S.locals, l.Ready

def TransitionForm.Ready (F : TransitionForm Clock Var) : Prop :=
  F.current.Ready ∧ ∀ N, F.nextPart = some N → N.Ready

namespace StateForm
@[simp] theorem ready_ofLocal (l : Local Clock Var) : (ofLocal l).Ready ↔ l.Ready := by
  simp [Ready,ofLocal]
@[simp] theorem ready_empty : (empty : StateForm Clock Var).Ready := by simp [Ready,empty]
@[simp] theorem ready_union (S T : StateForm Clock Var) :
    (S.union T).Ready ↔ S.Ready ∧ T.Ready := by
  simp only [Ready,union,Set.mem_union]
  aesop
end StateForm
namespace TransitionForm
@[simp] theorem ready_ofState (S : StateForm Clock Var) : (ofState S).Ready ↔ S.Ready := by
  simp [Ready,ofState]
@[simp] theorem ready_ofNextState (S : StateForm Clock Var) : (ofNextState S).Ready ↔ S.Ready := by
  simp [Ready,ofNextState]
@[simp] theorem ready_underReset (F : TransitionForm Clock Var) (Λ : ClockResetSet Clock) :
    (F.underReset Λ).Ready ↔ F.Ready := Iff.rfl
@[simp] theorem ready_union (F G : TransitionForm Clock Var) :
    (F.union G).Ready ↔ F.Ready ∧ G.Ready := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [Ready,union,unionNext,hf,hg,StateForm.ready_union] <;> aesop

theorem normalize_ready (Ψ : Judgement Clock Var) {F : TransitionForm Clock Var}
    (hn : normalize? Ψ = some F) (h : Ψ.Ready) : F.Ready := by
  induction Ψ generalizing F with
  | terminal => cases hn; simp [Local.Ready]
  | clock c r a => cases hn; simp [StateForm.Ready,StateForm.ofGuard]
  | marker m => cases hn; simp [Local.Ready]
  | predicate p => cases hn; simpa only [ready_ofState,StateForm.ready_ofLocal,Local.Ready,Judgement.Ready] using h
  | reset Λ Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          simp [normalize?,he] at hn
          subst F
          exact (ready_underReset G Λ).2 (ih he h)
  | conj Ψ Χ ihΨ ihΧ =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          cases hf : normalize? Χ with
          | none => simp [normalize?,he,hf] at hn
          | some H =>
              simp [normalize?,he,hf] at hn
              subst F
              exact (ready_union G H).2 ⟨ihΨ he h.1,ihΧ hf h.2⟩
  | next Ψ ih =>
      cases he : normalize? Ψ with
      | none => simp [normalize?,he] at hn
      | some G =>
          cases hx : G.nextPart with
          | some N => simp [normalize?,he,hx] at hn
          | none =>
              simp [normalize?,he,hx] at hn
              subst F
              exact (ready_ofNextState G.current).2 (ih he h).1
end TransitionForm
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
@[simp] theorem Predicate.ready_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).Ready ↔ p.Ready := by
  cases p <;> simp [Predicate.Ready,Predicate.rename,e.injective.eq_iff]
@[simp] theorem Local.ready_rename (e : Equiv.Perm Clock) (l : Local Clock Var) :
    (l.rename e).Ready ↔ l.Ready := by cases l <;> simp [Local.Ready,Local.rename]
@[simp] theorem StateForm.ready_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).Ready ↔ S.Ready := by simp [StateForm.Ready,StateForm.rename]
@[simp] theorem StateForm.ready_alphaReset (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.alphaReset e).Ready ↔ S.Ready := by
  simp [StateForm.Ready,StateForm.alphaReset,StateForm.rename]
@[simp] theorem TransitionForm.ready_alphaOuter (e : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    (F.alphaOuter e).Ready ↔ F.Ready := by
  cases hn : F.nextPart <;>
    simp [TransitionForm.Ready,TransitionForm.alphaOuter,hn,StateForm.Ready,
      StateForm.alphaReset,StateForm.rename]
@[simp] theorem TransitionForm.ready_alphaNext (e : Equiv.Perm Clock) (F : TransitionForm Clock Var) :
    (F.alphaNext e).Ready ↔ F.Ready := by
  cases hn : F.nextPart <;>
    simp [TransitionForm.Ready,TransitionForm.alphaNext,hn]
theorem TransitionForm.AlphaEquivalent.ready {F G : TransitionForm Clock Var}
    (ha : F.AlphaEquivalent G) : F.Ready ↔ G.Ready := by
  induction ha with
  | refl => rfl
  | outer F e hf => exact F.ready_alphaOuter e
  | next F e hf => exact F.ready_alphaNext e
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

namespace ConcreteMixed

theorem branch_ready [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hB : catalogue.Branch p Λ B) (hp : p.Ready) : B.Ready := by
  rcases hB with h | h | h
  · obtain ⟨p₀,R,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact (TransitionForm.ready_underReset F Λ).2
      (TransitionForm.normalize_ready _ hn (ConcreteFinite.raw_ready hr hp hm))
  · obtain ⟨p₀,Bs,Ψ,F,rfl,hr,hm,hn,rfl⟩ := h
    exact (TransitionForm.ready_underReset F Λ).2
      (TransitionForm.normalize_ready _ hn (ConcreteInfinite.raw_ready hr hp hm))
  · obtain ⟨c,m,kind,a,φ,F,rfl,hn,rfl⟩ := h
    apply (TransitionForm.ready_underReset F Λ).2
    apply TransitionForm.normalize_ready _ hn
    cases kind <;> simpa [UnboundedClocked.opening,UnboundedClocked.formula,
      Judgement.ofUnbounded,Judgement.Ready,Predicate.ofUnbounded,Predicate.Ready] using hp
end ConcreteMixed
namespace ConcreteContextual

theorem branch_ready [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hB : catalogue.Branch p Λ B) (hp : p.Ready) : B.Ready := by
  obtain ⟨R,A,hr,ha,rfl⟩ := hB
  exact (TransitionForm.ready_underReset A Λ).2 (ha.ready.mpr (ConcreteMixed.branch_ready hr hp))
end ConcreteContextual
end STLTableau.Section3

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace TransitionForm

theorem restrict_ready (F : TransitionForm Clock Var) :
    (F.restrictLocals Local.Ready Local.Ready).Ready := by
  refine ⟨fun l hl => hl.2, ?_⟩
  intro N hn
  obtain ⟨M,hm,rfl⟩ := Option.map_eq_some_iff.mp hn
  exact fun l hl => hl.2
end TransitionForm
namespace ConcreteContextual

theorem closure_ready [DecidableEq Clock]
    {anchor F : TransitionForm Clock Var}
    (hc : catalogue.IsClosure anchor F) (hready : anchor.Ready) : F.Ready := by
  have ha : SyntacticallySubsumed anchor (F.restrictLocals Local.Ready Local.Ready) :=
    hc.extension.restrictLocalsTarget _ _ hready.1 (fun N M hn hm => hready.2 N hn)
  have hf : catalogue.IsClosed (F.restrictLocals Local.Ready Local.Ready) := by
    intro p hp
    have hpF : Local.predicate p ∈ F.current.locals := hp.1
    have hpr : p.Ready := hp.2
    rcases hc.closed p hpF with hnone | ⟨B,hB,hBF⟩
    · exact Or.inl hnone
    · have hreadyB := branch_ready hB hpr
      exact Or.inr ⟨B,hB,hBF.restrictLocalsTarget _ _ hreadyB.1
        (fun N M hn hm => hreadyB.2 N hn)⟩
  have he := catalogue.minimal_restriction_eq hc Local.Ready Local.Ready ha hf
  rw [he]
  exact F.restrict_ready
end ConcreteContextual
end STLTableau.Section3
