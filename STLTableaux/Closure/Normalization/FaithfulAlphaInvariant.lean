import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization
import STLTableaux.Semantics.Invariants.EvaluatedInvariant

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace Local
@[simp] theorem evaluatedInvariant_rename (l : Local Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (l.rename e).EvaluatedInvariant σ P α k ↔ l.EvaluatedInvariant σ P (α ∘ e) k := by
  cases l with
  | terminal => rfl
  | marker => rfl
  | predicate p => exact forall_congr' (fun hk => p.invariant_rename e σ P α k hk)

theorem evaluatedInvariant_congr (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ l.freeClocks, α c = β c) :
    l.EvaluatedInvariant σ P α k ↔ l.EvaluatedInvariant σ P β k :=
  Judgement.evaluatedInvariant_congr_of_agree σ P l.toJudgement α β k h
end Local
namespace StateForm
@[simp] theorem evaluatedInvariant_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.rename e).EvaluatedInvariant σ P α k ↔ S.EvaluatedInvariant σ P (α ∘ e) k := by
  simp only [rename, EvaluatedInvariant, Set.forall_mem_image,
    Local.evaluatedInvariant_rename, ClockResetSet.apply_rename]

theorem evaluatedInvariant_congr (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ S.freeClocks, α c = β c) :
    S.EvaluatedInvariant σ P α k ↔ S.EvaluatedInvariant σ P β k := by
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  apply Local.evaluatedInvariant_congr
  intro c hc
  cases he : S.resets.value c with
  | some a => simp [ClockResetSet.apply, he]
  | none =>
      have hn : c ∉ S.resets.clocks := by
        rintro ⟨a,ha⟩; rw [he] at ha; cases ha
      simpa only [ClockResetSet.apply,he] using h c (Or.inr ⟨⟨l,hl,hc⟩,hn⟩)

theorem alphaReset_evaluatedInvariant (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.alphaReset e).EvaluatedInvariant σ P α k ↔ S.EvaluatedInvariant σ P α k := by
  simp only [alphaReset,rename,EvaluatedInvariant,Set.forall_mem_image,
    Local.evaluatedInvariant_rename,ClockResetSet.apply_rename]
  apply forall_congr'; intro l
  apply forall_congr'; intro hl
  apply Local.evaluatedInvariant_congr
  exact fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c ⟨l,hl,hc⟩
end StateForm
namespace TransitionForm

theorem alphaNext_evaluatedInvariant (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaNext e).EvaluatedInvariant σ P α k ↔ Φ.EvaluatedInvariant σ P α k := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext,EvaluatedInvariant,hn]
  | some N => simp [alphaNext,EvaluatedInvariant,hn,N.alphaReset_evaluatedInvariant e (hfix N hn)]

theorem alphaOuter_evaluatedInvariant (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaOuter e).EvaluatedInvariant σ P α k ↔ Φ.EvaluatedInvariant σ P α k := by
  have hagree := Φ.current.resets.apply_pullback_agree e Φ.bodyFreeClocks hfix α
  simp only [alphaOuter,EvaluatedInvariant,StateForm.alphaReset,StateForm.rename,
    StateForm.EvaluatedInvariant,Set.forall_mem_image,Local.evaluatedInvariant_rename,
    ClockResetSet.apply_rename]
  apply and_congr
  · apply forall_congr'; intro l
    apply forall_congr'; intro hl
    exact Local.evaluatedInvariant_congr l σ P _ _ k
      (fun c hc => hagree c (Or.inl ⟨l,hl,hc⟩))
  · cases hn : Φ.nextPart with
    | none => simp
    | some N =>
        simp only [Option.map_some, Option.some.injEq, forall_eq']
        apply forall_congr'; intro hk
        change (N.rename e).EvaluatedInvariant σ P _ _ ↔ N.EvaluatedInvariant σ P _ _
        rw [StateForm.evaluatedInvariant_rename]
        have he : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩) ∘ e =
            ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
              (STLTableau.Judgement.duration P ⟨k.1,hk⟩) := by
          funext c
          exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,hk⟩)
            (congrFun (Φ.current.resets.apply_rename e α) c)
        rw [he]
        apply StateForm.evaluatedInvariant_congr
        intro c hc
        exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,hk⟩)
          (hagree c (Or.inr (by simpa only [hn] using hc)))

theorem AlphaEquivalent.evaluatedInvariant {Φ Ψ : TransitionForm Clock Var}
    (h : AlphaEquivalent Φ Ψ) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Φ.EvaluatedInvariant σ P α k ↔ Ψ.EvaluatedInvariant σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_evaluatedInvariant e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_evaluatedInvariant e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
end TransitionForm
end STLTableau.Section3
