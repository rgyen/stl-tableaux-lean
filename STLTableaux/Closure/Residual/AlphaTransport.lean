import STLTableaux.Closure.Residual.FreshNormalization
import STLTableaux.ModelChecking.Preprocessing.Admissibility

/-! # Transport through syntactic clock alpha-equivalence -/
namespace STLTableau
open scoped STL

namespace IntervalPredicate
variable {Clock Var : Type*}
@[simp] theorem complexity_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var) :
    (p.rename e).complexity = p.complexity := by cases p <;> rfl
@[simp] theorem tableauReady_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var) :
    (p.rename e).TableauReady ↔ p.TableauReady := by
  cases p <;> simp [rename, TableauReady, e.injective.eq_iff]
@[simp] theorem isAtomic_rename (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var) :
    (p.rename e).IsAtomic ↔ p.IsAtomic := by cases p <;> rfl
end IntervalPredicate

namespace Judgement
variable {Clock Var : Type*}
theorem nonPredicateSatisfies_rename (e : Equiv.Perm Clock) (Ψ : Judgement Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) :
    NonPredicateSatisfies σ P α k (Ψ.rename e) ↔ NonPredicateSatisfies σ P (α ∘ e) k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => rfl
  | reset Λ Ψ ih => simp [rename, NonPredicateSatisfies, ih, ClockResetSet.apply_rename]
  | next Ψ ih =>
      simp only [rename, NonPredicateSatisfies]
      split
      · exact ih _ _
      · rfl
  | conj Φ Ψ ihΦ ihΨ => simp [rename, NonPredicateSatisfies, ihΦ, ihΨ]
  | _ => rfl

theorem evaluatedInvariant_rename (e : Equiv.Perm Clock) (Ψ : Judgement Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) :
    EvaluatedInvariant σ P α k (Ψ.rename e) ↔ EvaluatedInvariant σ P (α ∘ e) k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => simp [rename, EvaluatedInvariant, IntervalPredicate.invariant_rename]
  | reset Λ Ψ ih => simp [rename, EvaluatedInvariant, ih, ClockResetSet.apply_rename]
  | next Ψ ih =>
      simp only [rename, EvaluatedInvariant]
      split
      · exact ih _ _
      · rfl
  | conj Φ Ψ ihΦ ihΨ => simp [rename, EvaluatedInvariant, ihΦ, ihΨ]
  | _ => rfl

end Judgement

namespace StateForm
variable {Clock Var : Type*}
theorem nonPredicateSatisfies_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.rename e).NonPredicateSatisfies σ P α k ↔ S.NonPredicateSatisfies σ P (α ∘ e) k := by
  simp [rename, NonPredicateSatisfies, Judgement.nonPredicateSatisfies_rename,
    ClockResetSet.apply_rename]

theorem alphaReset_nonPredicateSatisfies (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.alphaReset e).NonPredicateSatisfies σ P α k ↔ S.NonPredicateSatisfies σ P α k := by
  simp only [alphaReset, rename, NonPredicateSatisfies, Set.forall_mem_image,
    Judgement.nonPredicateSatisfies_rename,
    ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro Ψ
  apply forall_congr'
  intro hΨ
  exact Judgement.nonPredicateSatisfies_congr_of_agree
    (fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c
      (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩)) σ P k

def evaluatedInvariant (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  ∀ Ψ ∈ S.locals, Judgement.EvaluatedInvariant σ P (S.resets.apply α) k Ψ

theorem evaluatedInvariant_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.rename e).evaluatedInvariant σ P α k ↔ S.evaluatedInvariant σ P (α ∘ e) k := by
  simp [rename, evaluatedInvariant, Judgement.evaluatedInvariant_rename, ClockResetSet.apply_rename]

theorem alphaReset_evaluatedInvariant (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.alphaReset e).evaluatedInvariant σ P α k ↔ S.evaluatedInvariant σ P α k := by
  simp only [alphaReset, rename, evaluatedInvariant, Set.forall_mem_image,
    Judgement.evaluatedInvariant_rename, ClockResetSet.apply_rename]
  apply forall_congr'
  intro Ψ
  apply forall_congr'
  intro hΨ
  exact Judgement.evaluatedInvariant_congr_of_agree
    (fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c
      (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩)) σ P k

theorem evaluatedInvariant_congr_of_agree (S : StateForm Clock Var)
    {α β : ClockValuation Clock} (h : ∀ c ∈ S.freeClocks, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) :
    S.evaluatedInvariant σ P α k ↔ S.evaluatedInvariant σ P β k := by
  have forward : ∀ {γ δ : ClockValuation Clock},
      (∀ c ∈ S.freeClocks, γ c = δ c) →
      S.evaluatedInvariant σ P γ k → S.evaluatedInvariant σ P δ k := by
    intro γ δ hagree hs Ψ hΨ
    apply (Judgement.evaluatedInvariant_congr_of_agree (σ := σ) (P := P) (k := k) ?_).1
      (hs Ψ hΨ)
    intro c hc
    cases hr : S.resets.value c with
    | some a => simp [ClockResetSet.apply, hr]
    | none =>
        have hcn : c ∉ S.resets.clocks := by
          rintro ⟨a, ha⟩
          rw [hr] at ha
          cases ha
        unfold ClockResetSet.apply
        rw [hr]
        exact hagree c (Or.inr (Set.mem_iUnion.2 ⟨Ψ,
          Set.mem_iUnion.2 ⟨hΨ, ⟨hc, hcn⟩⟩⟩))
  exact ⟨forward h, forward (fun c hc => (h c hc).symm)⟩

end StateForm

namespace TransitionForm
variable {Clock Var : Type*}
theorem alphaOuter_nonPredicateSatisfies (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks, e c = c) :
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      (Φ.alphaOuter e).NonPredicateSatisfies σ P α k ↔ Φ.NonPredicateSatisfies σ P α k := by
  intro σ P α k
  have hagree := Φ.current.resets.apply_pullback_agree e
    ((⋃ Ψ ∈ Φ.current.locals, Ψ.freeClocks) ∪
      match Φ.nextPart with | none => ∅ | some N => N.freeClocks) hfix α
  simp only [alphaOuter, NonPredicateSatisfies, StateForm.alphaReset, StateForm.rename,
    Set.forall_mem_image, Judgement.nonPredicateSatisfies_rename,
    ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply and_congr
  · apply forall_congr'
    intro Ψ
    apply forall_congr'
    intro hΨ
    exact Judgement.nonPredicateSatisfies_congr_of_agree
      (fun c hc => hagree c (Or.inl (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩))) σ P k
  · cases hN : Φ.nextPart with
    | none => rfl
    | some N =>
        simp only [Option.map_some]
        split
        · rw [StateForm.nonPredicateSatisfies_rename]
          have hcomp : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
              (Judgement.duration P ⟨k.1, ‹_›⟩) ∘ e =
              ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
                (Judgement.duration P ⟨k.1, ‹_›⟩) := by
            funext c
            have he := congrFun (Φ.current.resets.apply_rename e α) c
            exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
          rw [hcomp]
          apply StateForm.nonPredicateSatisfies_congr_of_agree N ?_ σ P _
          intro c hc
          have he := hagree c (Or.inr (by simpa [hN] using hc))
          exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
        · rfl

theorem alphaNext_nonPredicateSatisfies (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      (Φ.alphaNext e).NonPredicateSatisfies σ P α k ↔ Φ.NonPredicateSatisfies σ P α k := by
  intro σ P α k
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, NonPredicateSatisfies, hn]
  | some N =>
      simp [alphaNext, NonPredicateSatisfies, hn, N.alphaReset_nonPredicateSatisfies e (hfix N hn)]

theorem alphaOuter_evaluatedInvariant (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks, e c = c) :
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      (Φ.alphaOuter e).evaluatedInvariant σ P α k ↔ Φ.evaluatedInvariant σ P α k := by
  intro σ P α k
  have hagree := Φ.current.resets.apply_pullback_agree e
    ((⋃ Ψ ∈ Φ.current.locals, Ψ.freeClocks) ∪
      match Φ.nextPart with | none => ∅ | some N => N.freeClocks) hfix α
  simp only [alphaOuter, evaluatedInvariant, StateForm.alphaReset, StateForm.rename,
    Set.forall_mem_image, Judgement.evaluatedInvariant_rename, ClockResetSet.apply_rename]
  apply and_congr
  · apply forall_congr'
    intro Ψ
    apply forall_congr'
    intro hΨ
    exact Judgement.evaluatedInvariant_congr_of_agree
      (fun c hc => hagree c (Or.inl (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩))) σ P k
  · cases hN : Φ.nextPart with
    | none => rfl
    | some N =>
        simp only [Option.map_some]
        split
        · change (N.rename e).evaluatedInvariant σ P _ _ ↔ N.evaluatedInvariant σ P _ _
          rw [StateForm.evaluatedInvariant_rename]
          have hcomp : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
              (Judgement.duration P ⟨k.1, ‹_›⟩) ∘ e =
              ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
                (Judgement.duration P ⟨k.1, ‹_›⟩) := by
            funext c
            have he := congrFun (Φ.current.resets.apply_rename e α) c
            exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
          rw [hcomp]
          apply StateForm.evaluatedInvariant_congr_of_agree N ?_ σ P _
          intro c hc
          have he := hagree c (Or.inr (by simpa [hN] using hc))
          exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
        · rfl

theorem alphaNext_evaluatedInvariant (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : Judgement.Position P),
      (Φ.alphaNext e).evaluatedInvariant σ P α k ↔ Φ.evaluatedInvariant σ P α k := by
  intro σ P α k
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, evaluatedInvariant, hn]
  | some N =>
      simp only [alphaNext, evaluatedInvariant, hn, Option.map_some]
      apply and_congr Iff.rfl
      split
      · exact N.alphaReset_evaluatedInvariant e (hfix N hn) σ P _ _
      · rfl

theorem AlphaEquivalent.nonPredicateSatisfies {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    Φ.NonPredicateSatisfies σ P α k ↔ Ψ.NonPredicateSatisfies σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_nonPredicateSatisfies e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_nonPredicateSatisfies e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem AlphaEquivalent.evaluatedInvariant {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    Φ.evaluatedInvariant σ P α k ↔ Ψ.evaluatedInvariant σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_evaluatedInvariant e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_evaluatedInvariant e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Any clock-name independent property of current predicates transports. -/
theorem AlphaEquivalent.allCurrentPredicates {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) (Q : IntervalPredicate Clock Var → Prop)
    (hQ : ∀ e p, Q (p.rename e) ↔ Q p) :
    ExpansionRules.AllCurrentPredicates Φ Q ↔ ExpansionRules.AllCurrentPredicates Ψ Q := by
  induction h with
  | refl => rfl
  | outer Φ e hf =>
      constructor
      · intro h p hp
        exact (hQ e p).1 (h (p.rename e) ⟨.predicate p, hp, rfl⟩)
      · intro h q hq
        obtain ⟨J, hJ, he⟩ := hq
        cases J with
        | predicate p =>
            have heq : p.rename e = q := Judgement.predicate.inj he
            subst q
            exact (hQ e p).2 (h p hJ)
        | _ => cases he
  | next Φ e hf => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem AlphaEquivalent.currentTableauReady {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) :
    ExpansionRules.AllCurrentPredicates Φ IntervalPredicate.TableauReady ↔
      ExpansionRules.AllCurrentPredicates Ψ IntervalPredicate.TableauReady :=
  h.allCurrentPredicates _ IntervalPredicate.tableauReady_rename

theorem evaluatedInvariant_iff_invariantAt (Φ : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size) :
    Φ.evaluatedInvariant σ P α k ↔ Φ.InvariantAt P α k hk := by
  have local_iff (S : StateForm Clock Var) (β : ClockValuation Clock)
      (j : Judgement.Position P) :
      (∀ J ∈ S.locals, Judgement.EvaluatedInvariant σ P β j J) ↔
      ∀ hj : j.1 < P.size, Judgement.SetInvariant (P.interval ⟨j.1, hj⟩) β S.locals := by
    constructor
    · intro h hj
      exact Judgement.setInvariant_of_evaluated σ P β j hj _ h
    · intro h J hJ
      have hl := S.locals_are_local J hJ
      cases J <;> simp_all only [Judgement.IsLocal, Judgement.EvaluatedInvariant]
      split
      · exact h _ _ hJ
      · trivial
  simp only [evaluatedInvariant, InvariantAt]
  rw [local_iff]
  apply and_congr
  · exact ⟨fun h => h hk, fun h _ => h⟩
  · cases hn : Φ.nextPart with
    | none => simp [NextInvariantAt, hn]
    | some N =>
        simp only [dif_pos hk]
        rw [local_iff]
        simp [NextInvariantAt, hn]

theorem AlphaEquivalent.invariantAt {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) {σ : FiniteSignal Var} (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size) :
    Φ.InvariantAt P α k hk ↔ Ψ.InvariantAt P α k hk := by
  rw [← Φ.evaluatedInvariant_iff_invariantAt σ P α k hk,
    ← Ψ.evaluatedInvariant_iff_invariantAt σ P α k hk]
  exact h.evaluatedInvariant σ P α k

end TransitionForm
end STLTableau
