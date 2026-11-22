import STLTableaux.Semantics.Invariants.NumericInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Local
@[simp] theorem evaluatedNumeric_rename (l : Local Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (l.rename e).Numeric σ P α k ↔ l.Numeric σ P (α ∘ e) k := by
  cases l with
  | terminal => rfl
  | marker => rfl
  | predicate p => exact forall_congr' (fun hk => p.numeric_rename e (P.interval ⟨k.1,hk⟩) α)

theorem evaluatedNumeric_congr (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ l.freeClocks, α c = β c) :
    l.Numeric σ P α k ↔ l.Numeric σ P β k :=
  Judgement.numeric_congr l.toJudgement σ P α β k h
end Local
namespace StateForm
@[simp] theorem evaluatedNumeric_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.rename e).EvaluatedNumeric σ P α k ↔ S.EvaluatedNumeric σ P (α ∘ e) k := by
  simp only [rename, EvaluatedNumeric, Set.forall_mem_image,
    Local.evaluatedNumeric_rename, ClockResetSet.apply_rename]

theorem evaluatedNumeric_congr (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ S.freeClocks, α c = β c) :
    S.EvaluatedNumeric σ P α k ↔ S.EvaluatedNumeric σ P β k := by
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  apply Local.evaluatedNumeric_congr
  intro c hc
  cases he : S.resets.value c with
  | some a => simp [ClockResetSet.apply, he]
  | none =>
      have hn : c ∉ S.resets.clocks := by
        rintro ⟨a,ha⟩; rw [he] at ha; cases ha
      simpa only [ClockResetSet.apply,he] using h c (Or.inr ⟨⟨l,hl,hc⟩,hn⟩)

theorem alphaReset_evaluatedNumeric (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.alphaReset e).EvaluatedNumeric σ P α k ↔ S.EvaluatedNumeric σ P α k := by
  simp only [alphaReset,rename,EvaluatedNumeric,Set.forall_mem_image,
    Local.evaluatedNumeric_rename,ClockResetSet.apply_rename]
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  apply Local.evaluatedNumeric_congr
  exact fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c ⟨l,hl,hc⟩
end StateForm
namespace TransitionForm

theorem alphaNext_evaluatedNumeric (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaNext e).EvaluatedNumeric σ P α k ↔ Φ.EvaluatedNumeric σ P α k := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext,EvaluatedNumeric,hn]
  | some N => simp [alphaNext,EvaluatedNumeric,hn,N.alphaReset_evaluatedNumeric e (hfix N hn)]

theorem alphaOuter_evaluatedNumeric (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaOuter e).EvaluatedNumeric σ P α k ↔ Φ.EvaluatedNumeric σ P α k := by
  have hagree := Φ.current.resets.apply_pullback_agree e Φ.bodyFreeClocks hfix α
  simp only [alphaOuter,EvaluatedNumeric,StateForm.alphaReset,StateForm.rename,
    StateForm.EvaluatedNumeric,Set.forall_mem_image,Local.evaluatedNumeric_rename,
    ClockResetSet.apply_rename]
  apply and_congr
  · apply forall_congr'; intro l
    apply forall_congr'; intro hl
    exact Local.evaluatedNumeric_congr l σ P _ _ k
      (fun c hc => hagree c (Or.inl ⟨l,hl,hc⟩))
  · cases hn : Φ.nextPart with
    | none => simp
    | some N =>
        simp only [Option.map_some, Option.some.injEq, forall_eq']
        apply forall_congr'; intro hk
        change (N.rename e).EvaluatedNumeric σ P _ _ ↔ N.EvaluatedNumeric σ P _ _
        rw [StateForm.evaluatedNumeric_rename]
        have he : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩) ∘ e =
            ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
              (STLTableau.Judgement.duration P ⟨k.1,hk⟩) := by
          funext c
          exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,hk⟩)
            (congrFun (Φ.current.resets.apply_rename e α) c)
        rw [he]
        apply StateForm.evaluatedNumeric_congr
        intro c hc
        exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,hk⟩)
          (hagree c (Or.inr (by simpa only [hn] using hc)))

theorem AlphaEquivalent.evaluatedNumeric {Φ Ψ : TransitionForm Clock Var}
    (h : AlphaEquivalent Φ Ψ) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Φ.EvaluatedNumeric σ P α k ↔ Ψ.EvaluatedNumeric σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_evaluatedNumeric e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_evaluatedNumeric e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
end TransitionForm
end STLTableau.Section3
