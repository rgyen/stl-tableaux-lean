import STLTableaux.Finiteness.Derivation.Pending.PendingSelectedStep
import STLTableaux.Finiteness.Derivation.Pending.PendingOrdinarySolo

/-! Singleton positive-step integration from the actual owned input. Semantic
source premises and the strict canonical measure are derived, not assumed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Literal residual absence forces a singleton current spine and no future
payloads. Guards and the inherited reset contribute no pending weight. -/
theorem owned_selected_solo_weight
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right)
    (hAbsent : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = none) :
    pendingWeight owned.canonical = pendingWeight (.predicate p) := by
  have hempty : left ++ right = [] ∧ owned.nextInputs = [] := by
    simpa only [foldCurrent_none_iff,List.append_eq_nil_iff,List.map_eq_nil_iff] using hAbsent
  obtain ⟨hleft,hright⟩ := List.append_eq_nil_iff.mp hempty.1
  have hlocals : owned.locals = [.predicate p] := by
    rw [hsplit,hleft,hright]
    rfl
  have hBody : foldCurrent (owned.locals.map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some (.predicate p) := by
    simp [hlocals,hempty.2,foldCurrent,optionalConj,Local.toJudgement]
  exact canonical_body_weight owned.shape hBody

variable [DecidableEq Clock] [Infinite Clock]

/-- The absent-residual step obtains every source semantic premise from the
ready, satisfied, fully invariant original owned input and strictly decreases
its actual canonical occurrence measure. The child is literally B. -/
theorem exists_ordinary_child_solo_of_input
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A)
    (p : Predicate Clock Var) (left right : List (Local Clock Var))
    (hsplit : owned.locals = left ++ .predicate p :: right) (hn : ¬ p.IsAtomic)
    (hAbsent : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = none)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hReady : J.Ready) (hHolds : Judgement.holds σ P α k J)
    (hInv : J.EvaluatedInvariant σ P α k) (hStable : J.UnderlyingStable σ P) :
    ∃ (x : Clock) (B : MixedJ Clock Var) (Rc : ClockResetSet Clock) (W' : Set Clock)
      (child : OwnedPending B Rc W'),
      x ∉ W ∧ RawBranch p B ∧ FreshWithoutContext p B ∧
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint Rc.clocks (A ∪ syntaxClocks (.predicate p)) ∧
      pendingWeight child.canonical < pendingWeight owned.canonical ∧
      B.Ready ∧ Judgement.holds σ P (R.apply α) k B ∧
      B.EvaluatedInvariant σ P (R.apply α) k ∧ B.UnderlyingStable σ P ∧ NextPrivate B := by
  have h := owned_selected_facts owned p left right hsplit σ P α k
    hReady hHolds hInv hStable
  rw [owned_selected_solo_weight owned p left right hsplit hAbsent]
  exact exists_ordinary_child_solo owned A hA hprotected p left right hsplit hn hAbsent
    σ P α k h.1 h.2.2.1 h.2.2.2.1 h.2.1

end STLTableau.Section4.Finiteness
