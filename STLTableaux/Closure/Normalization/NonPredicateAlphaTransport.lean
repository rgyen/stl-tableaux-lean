import STLTableaux.Semantics.Invariants.NumericInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Local
@[simp] theorem nonPredicate_rename (e : Equiv.Perm Clock) (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (l.rename e).nonPredicateHolds σ P α k ↔ l.nonPredicateHolds σ P (α ∘ e) k := by
  cases l <;> rfl

theorem nonPredicate_congr_of_agree (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (_h : ∀ c ∈ l.freeClocks, α c = β c) :
    l.nonPredicateHolds σ P α k ↔ l.nonPredicateHolds σ P β k := by cases l <;> rfl
end Local
namespace StateForm

theorem nonPredicate_congr_of_agree (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ S.freeClocks, α c = β c) :
    S.nonPredicateHolds σ P α k ↔ S.nonPredicateHolds σ P β k := by
  unfold nonPredicateHolds
  apply and_congr
  · apply forall_congr'; intro g
    apply forall_congr'; intro hg
    simp only [Guard.holds,h g.clock (Or.inl ⟨g,hg,rfl⟩)]
  · apply forall_congr'; intro l
    apply forall_congr'; intro hl
    cases l <;> rfl
theorem nonPredicate_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.rename e).nonPredicateHolds σ P α k ↔ S.nonPredicateHolds σ P (α ∘ e) k := by
  simp only [rename, nonPredicateHolds, Set.forall_mem_image, Guard.holds_rename, Local.nonPredicate_rename,
    ClockResetSet.apply_rename]

theorem alphaReset_nonPredicate (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.alphaReset e).nonPredicateHolds σ P α k ↔ S.nonPredicateHolds σ P α k := by
  simp only [alphaReset, rename, nonPredicateHolds, Set.forall_mem_image, Local.nonPredicate_rename,
    ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  apply Local.nonPredicate_congr_of_agree
  exact fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c ⟨l,hl,hc⟩


end StateForm
namespace TransitionForm
theorem alphaNext_nonPredicate (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaNext e).nonPredicateHolds σ P α k ↔ Φ.nonPredicateHolds σ P α k := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, nonPredicateHolds, hn]
  | some N => simp [alphaNext, nonPredicateHolds, hn, N.alphaReset_nonPredicate e (hfix N hn)]

theorem alphaOuter_nonPredicate (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaOuter e).nonPredicateHolds σ P α k ↔ Φ.nonPredicateHolds σ P α k := by
  have hagree := Φ.current.resets.apply_pullback_agree e Φ.bodyFreeClocks hfix α
  simp only [alphaOuter, nonPredicateHolds, StateForm.alphaReset, StateForm.rename, StateForm.nonPredicateHolds,
    Set.forall_mem_image, Local.nonPredicate_rename, ClockResetSet.apply_rename]
  apply and_congr
  · apply and_congr Iff.rfl
    apply forall_congr'
    intro l
    apply forall_congr'
    intro hl
    exact Local.nonPredicate_congr_of_agree l σ P _ _ k
      (fun c hc => hagree c (Or.inl ⟨l,hl,hc⟩))
  · cases hn : Φ.nextPart with
    | none => rfl
    | some N =>
        simp only [Option.map_some]
        split
        · change (N.rename e).nonPredicateHolds σ P _ _ ↔ N.nonPredicateHolds σ P _ _
          rw [StateForm.nonPredicate_rename]
          have he : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
              (STLTableau.Judgement.duration P ⟨k.1,‹_›⟩) ∘ e =
              ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
                (STLTableau.Judgement.duration P ⟨k.1,‹_›⟩) := by
            funext c
            exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,‹_›⟩)
              (congrFun (Φ.current.resets.apply_rename e α) c)
          rw [he]
          apply StateForm.nonPredicate_congr_of_agree
          intro c hc
          exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,‹_›⟩)
            (hagree c (Or.inr (by simpa only [hn] using hc)))
        · rfl


theorem AlphaEquivalent.nonPredicate {Φ Ψ : TransitionForm Clock Var} (h : AlphaEquivalent Φ Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    Φ.nonPredicateHolds σ P α k ↔ Ψ.nonPredicateHolds σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_nonPredicate e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_nonPredicate e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
end TransitionForm
end STLTableau.Section3
