import STLTableaux.Rules.Invariants.Section4RuleInvariants
import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! Derived numeric clauses for forward soundness. The unified
`Predicate.Invariant` is unchanged; no past-cover fact is asserted here. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace Predicate

def Numeric (J : MarkedInterval) (α : ClockValuation Clock) : Predicate Clock Var → Prop
  | .plain _ => True
  | .upper c b kind (.bounded I) φ =>
      IntervalPredicate.Invariant J α (.upper c b kind I φ) ∧
      STLTableau.AlwaysSafe J α (.upper c b kind I φ)
  | .bounded c d b q kind (.bounded I) φ =>
      IntervalPredicate.Invariant J α (.bounded c d b q kind I φ) ∧
      STLTableau.AlwaysSafe J α (.bounded c d b q kind I φ)
  | .upper c b .always (.unbounded a) _ | .bounded c _ b _ .always (.unbounded a) _ =>
      (α c : ℝ) <[Marker.imp b J.leftBoundary] (a : ℝ)
  | .upper c b .eventually (.unbounded _) _ =>
      (0 : ℝ) <[Marker.conj b J.rightBoundary] ((α c : ℝ) + J.right - J.left)
  | .bounded c d b q .eventually (.unbounded _) _ =>
      (α d : ℝ) <[Marker.conj b q] (α c : ℝ)

theorem numeric_congr (p : Predicate Clock Var) (J : MarkedInterval) (α β : ClockValuation Clock)
    (h : ∀ c ∈ Judgement.freeClocks (.predicate p), α c = β c) :
    p.Numeric J α ↔ p.Numeric J β := by
  cases p with
  | plain => rfl
  | upper c b kind I φ =>
      have hc := h c (by simp [Judgement.freeClocks])
      cases I <;> cases kind <;>
        simp only [Numeric,IntervalPredicate.Invariant,STLTableau.AlwaysSafe,hc]
  | bounded c d b q kind I φ =>
      have hc := h c (by simp [Judgement.freeClocks])
      have hd := h d (by simp [Judgement.freeClocks])
      cases I <;> cases kind <;> simp only [Numeric,IntervalPredicate.Invariant,STLTableau.AlwaysSafe,hc,hd]

@[simp] theorem numeric_rename (p : Predicate Clock Var) (e : Equiv.Perm Clock)
    (J : MarkedInterval) (α : ClockValuation Clock) :
    (p.rename e).Numeric J α ↔ p.Numeric J (α ∘ e) := by
  cases p with
  | plain => rfl
  | upper c b kind I φ => cases I <;> cases kind <;> rfl
  | bounded c d b q kind I φ => cases I <;> cases kind <;> rfl

theorem numeric_of_invariant (p : Predicate Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hi : p.Invariant σ P α k hk) : p.Numeric (P.interval ⟨k.1,hk⟩) α := by
  cases p with
  | plain => trivial
  | upper c b kind I φ =>
      cases I with
      | bounded I =>
          refine ⟨STLTableau.invariant_implies_residual σ P α k hk _ hi,?_⟩
          cases kind with
          | always => exact hi
          | eventually => trivial
      | unbounded a => cases kind with
        | always => exact hi
        | eventually => exact hi.1
  | bounded c d b q kind I φ =>
      cases I with
      | bounded I =>
          refine ⟨STLTableau.invariant_implies_residual σ P α k hk _ hi,?_⟩
          cases kind with
          | always => exact hi.1
          | eventually => trivial
      | unbounded a => cases kind with
        | always => exact hi
        | eventually => exact hi.1
end Predicate
namespace Judgement

def nonPredicateHolds (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : STLTableau.Judgement.Position P) → Judgement Clock Var → Prop
  | _, .predicate _ => True
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .marker m => if h : k.1 < P.size then
      (P.interval ⟨k.1,h⟩).leftBoundary = m else m = Marker.closed
  | k, .next Ψ => if h : k.1 < P.size then
      nonPredicateHolds σ P (ClockResetSet.elapse α
        (STLTableau.Judgement.duration P ⟨k.1,h⟩)) ⟨k.1+1,by omega⟩ Ψ else False
  | k, .reset Λ Ψ => nonPredicateHolds σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => nonPredicateHolds σ P α k Φ ∧ nonPredicateHolds σ P α k Ψ

def EvaluatedNumeric (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : STLTableau.Judgement.Position P) → Judgement Clock Var → Prop
  | k, .predicate p => ∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) α
  | k, .next Ψ => ∀ hk : k.1 < P.size,
      EvaluatedNumeric σ P (ClockResetSet.elapse α
        (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ Ψ
  | k, .reset Λ Ψ => EvaluatedNumeric σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedNumeric σ P α k Φ ∧ EvaluatedNumeric σ P α k Ψ
  | _, _ => True

theorem numeric_congr (Ψ : Judgement Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ Ψ.freeClocks, α c = β c) :
    EvaluatedNumeric σ P α k Ψ ↔ EvaluatedNumeric σ P β k Ψ := by
  induction Ψ generalizing α β k with
  | predicate p => exact forall_congr' (fun _ => p.numeric_congr _ _ _ h)
  | next Ψ ih =>
      exact forall_congr' (fun _ => ih _ _ _ (fun c hc =>
        congrArg (fun x => x+_) (h c hc)))
  | reset Λ Ψ ih =>
      apply ih
      intro c hc
      cases he : Λ.value c with
      | some a => simp only [ClockResetSet.apply,he]
      | none =>
          have hn : c ∉ Λ.clocks := by rintro ⟨a,ha⟩; rw [he] at ha; cases ha
          simpa only [ClockResetSet.apply,he] using h c ⟨hc,hn⟩
  | conj Φ Ψ ihΦ ihΨ =>
      exact and_congr (ihΦ _ _ _ (fun c hc => h c (Or.inl hc))) (ihΨ _ _ _ (fun c hc => h c (Or.inr hc)))
  | _ => rfl

@[simp] theorem nonPredicate_ofFinite (Ψ : STLTableau.Judgement Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    nonPredicateHolds σ P α k (ofFinite Ψ) ↔
      STLTableau.Judgement.NonPredicateSatisfies σ P α k Ψ := by
  induction Ψ generalizing α k with
  | next Ψ ih => dsimp [ofFinite,nonPredicateHolds,STLTableau.Judgement.NonPredicateSatisfies]; split <;> simp_all
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | _ => rfl

@[simp] theorem nonPredicate_ofUnbounded (Ψ : UnboundedClocked.Node Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    nonPredicateHolds σ P α k (ofUnbounded Ψ) ↔
      UnboundedClocked.Node.nonPredicateHolds σ P α k Ψ := by
  induction Ψ generalizing α k with
  | next Ψ ih => dsimp [ofUnbounded,nonPredicateHolds,UnboundedClocked.Node.nonPredicateHolds]; split <;> simp_all
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | _ => rfl

@[simp] theorem numeric_ofUnbounded (Ψ : UnboundedClocked.Node Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    EvaluatedNumeric σ P α k (ofUnbounded Ψ) ↔
      UnboundedClocked.EvaluatedNonpast σ P α k Ψ := by
  induction Ψ generalizing α k with
  | predicate p => cases p with
    | upper c b kind a φ => cases kind <;> rfl
    | bounded c d b q kind a φ => cases kind <;> rfl
  | plain => simp [ofUnbounded,EvaluatedNumeric,Predicate.Numeric,UnboundedClocked.EvaluatedNonpast]
  | next Ψ ih => exact forall_congr' (fun _ => ih _ _)
  | reset Λ Ψ ih => exact ih _ _
  | conj Φ Ψ ihΦ ihΨ => exact and_congr (ihΦ _ _) (ihΨ _ _)
  | _ => rfl
theorem numeric_ofFinite_of_parts (Ψ : STLTableau.Judgement Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : STLTableau.Judgement.EvaluatedInvariant σ P α k Ψ)
    (ha : STLTableau.AlwaysSafeAt σ P α k Ψ) :
    EvaluatedNumeric σ P α k (ofFinite Ψ) := by
  induction Ψ generalizing α k with
  | predicate p =>
      intro hk
      have hi' : IntervalPredicate.Invariant (P.interval ⟨k.1,hk⟩) α p := by
        simpa only [STLTableau.Judgement.EvaluatedInvariant,dif_pos hk] using hi
      have ha' := ha hk
      cases p <;> first | trivial | exact ⟨hi',ha'⟩
  | next Ψ ih =>
      intro hk
      apply ih
      · simpa only [STLTableau.Judgement.EvaluatedInvariant,dif_pos hk] using hi
      · exact ha hk
  | reset Λ Ψ ih => exact ih _ _ hi ha
  | conj Φ Ψ ihΦ ihΨ => exact ⟨ihΦ _ _ hi.1 ha.1,ihΨ _ _ hi.2 ha.2⟩
  | _ => trivial

end Judgement
namespace Local

def Numeric (l : Local Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  l.toJudgement.EvaluatedNumeric σ P α k

def nonPredicateHolds (l : Local Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  l.toJudgement.nonPredicateHolds σ P α k
end Local
namespace StateForm

def EvaluatedNumeric (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  ∀ l ∈ S.locals, l.Numeric σ P (S.resets.apply α) k

def nonPredicateHolds (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  (∀ g ∈ S.guards, g.holds α) ∧ ∀ l ∈ S.locals, l.nonPredicateHolds σ P (S.resets.apply α) k
end StateForm
namespace TransitionForm

def EvaluatedNumeric (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  Φ.current.EvaluatedNumeric σ P α k ∧ ∀ N, Φ.nextPart = some N → ∀ hk : k.1 < P.size,
    N.EvaluatedNumeric σ P (ClockResetSet.elapse (Φ.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩

def nonPredicateHolds (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :=
  Φ.current.nonPredicateHolds σ P α k ∧ match Φ.nextPart with
  | none => True
  | some N => if hk : k.1 < P.size then N.nonPredicateHolds σ P
      (ClockResetSet.elapse (Φ.current.resets.apply α) (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
      ⟨k.1+1,by omega⟩ else False
end TransitionForm
end STLTableau.Section3
