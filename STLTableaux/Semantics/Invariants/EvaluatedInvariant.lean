import STLTableaux.Tableau.Stability.GeneratorStability
import STLTableaux.Rules.Finite.Preservation

/-! The unified predicate invariant evaluated in the actual mixed reset/next
scopes, and its transport through concrete branch normalization. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace Predicate
theorem invariant_congr_of_agree (p : Predicate Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (h : ∀ c ∈ Judgement.freeClocks (.predicate p), α c = β c) :
    p.Invariant σ P α k hk ↔ p.Invariant σ P β k hk := by
  cases p with
  | plain φ => rfl
  | upper c b kind I φ =>
      have hc := h c (by simp [Judgement.freeClocks])
      cases I <;> cases kind <;>
        simp only [Predicate.Invariant, STLTableau.Invariant, STLTableau.PastSeparated,
          UnboundedClocked.Invariant, UnboundedClocked.PastSeparated, hc]
  | bounded c d b q kind I φ =>
      have hc := h c (by simp [Judgement.freeClocks])
      have hd := h d (by simp [Judgement.freeClocks])
      cases I <;> cases kind <;>
        simp only [Predicate.Invariant, STLTableau.Invariant, STLTableau.PastSeparated,
          UnboundedClocked.Invariant, UnboundedClocked.PastSeparated, hc, hd]
end Predicate

namespace Judgement
def EvaluatedInvariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : STLTableau.Judgement.Position P → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, p.Invariant σ P α k hk
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      EvaluatedInvariant σ P (ClockResetSet.elapse α
        (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ Ψ
  | k, .reset Λ Ψ => EvaluatedInvariant σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedInvariant σ P α k Φ ∧ EvaluatedInvariant σ P α k Ψ
  | _, _ => True

@[simp] theorem evaluatedInvariant_ofFinite (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (Ψ : STLTableau.Judgement Clock Var) :
    EvaluatedInvariant σ P α k (ofFinite Ψ) ↔ STLTableau.EvaluatedInvariant σ P α k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => cases p <;> rfl
  | next Ψ ih => exact forall_congr' (fun _ => ih _ _)
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | _ => rfl

@[simp] theorem evaluatedInvariant_ofUnbounded (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (Ψ : UnboundedClocked.Node Clock Var) :
    EvaluatedInvariant σ P α k (ofUnbounded Ψ) ↔
      UnboundedClocked.EvaluatedInvariant σ P α k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => cases p <;> rfl
  | plain φ => simp [ofUnbounded, EvaluatedInvariant, Predicate.Invariant, UnboundedClocked.EvaluatedInvariant]
  | next Ψ ih => exact forall_congr' (fun _ => ih _ _)
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | _ => rfl

theorem evaluatedInvariant_congr_of_agree (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (Ψ : Judgement Clock Var)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ Ψ.freeClocks, α c = β c) :
    EvaluatedInvariant σ P α k Ψ ↔ EvaluatedInvariant σ P β k Ψ := by
  induction Ψ generalizing α β k with
  | predicate p => exact forall_congr' (fun hk => p.invariant_congr_of_agree σ P α β k hk h)
  | next Ψ ih =>
      apply forall_congr'
      intro hk
      apply ih
      intro c hc
      simp only [ClockResetSet.elapse, h c hc]
  | reset Λ Ψ ih =>
      apply ih
      intro c hc
      cases hΛ : Λ.value c with
      | some a => simp [ClockResetSet.apply, hΛ]
      | none =>
          have hcnot : c ∉ Λ.clocks := by
            rintro ⟨a, ha⟩
            rw [hΛ] at ha
            cases ha
          simpa only [ClockResetSet.apply, hΛ] using h c ⟨hc, hcnot⟩
  | conj Φ Ψ ihΦ ihΨ =>
      exact and_congr (ihΦ _ _ _ (fun c hc => h c (Or.inl hc)))
        (ihΨ _ _ _ (fun c hc => h c (Or.inr hc)))
  | _ => rfl
end Judgement

namespace Local
def EvaluatedInvariant (l : Local Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Prop :=
  l.toJudgement.EvaluatedInvariant σ P α k
end Local

namespace StateForm
def EvaluatedInvariant (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Prop :=
  ∀ l ∈ S.locals, l.EvaluatedInvariant σ P (S.resets.apply α) k
end StateForm

namespace TransitionForm
def EvaluatedInvariant (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Prop :=
  Φ.current.EvaluatedInvariant σ P α k ∧ ∀ N, Φ.nextPart = some N →
    ∀ hk : k.1 < P.size,
      N.EvaluatedInvariant σ P
        (ClockResetSet.elapse (Φ.current.resets.apply α)
          (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩
end TransitionForm

end STLTableau.Section3
