import STLTableaux.Closure.Subsumption.FaithfulClosureRestriction
import STLTableaux.Rules.Invariants.Section4RuleInvariants
import STLTableaux.Semantics.Invariants.NumericInvariant
import STLTableaux.Closure.Subsumption.NumericGuardSubsumption
import STLTableaux.Rules.Invariants.NumericGuardTypePreservation
import STLTableaux.Closure.Correctness.NumericFromInvariant
import STLTableaux.Closure.Expansion.BranchwiseClosure
import STLTableaux.Closure.Expansion.BranchwiseUnion

/-! Closure soundness and invariant preservation along an expansion path to
a fixed closure. Each step respects the current and next reset scopes. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}


namespace Local

theorem numeric_congr_of_agree (l : Local Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (he : ∀ c ∈ l.freeClocks, α c = β c) :
    l.Numeric σ P α k ↔ l.Numeric σ P β k :=
  Judgement.numeric_congr l.toJudgement σ P α β k he

end Local

namespace TransitionForm

def currentNumericFilter (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (l : Local Clock Var) : Prop :=
  l.Numeric σ P (F.current.resets.apply α) k

def nextNumericFilter (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (l : Local Clock Var) : Prop :=
  ∀ M, F.nextPart = some M → ∀ hk : k.1 < P.size,
    l.Numeric σ P (M.resets.apply (ClockResetSet.elapse (F.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1,hk⟩))) ⟨k.1+1,by omega⟩

def numericProjection (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : TransitionForm Clock Var :=
  F.restrictLocals (F.currentNumericFilter σ P α k) (F.nextNumericFilter σ P α k)

theorem numericProjection_numeric (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (F.numericProjection σ P α k).EvaluatedNumeric σ P α k := by
  constructor
  · intro l hl
    exact hl.2
  · intro N hn hk
    obtain ⟨M, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
    intro l hl
    exact hl.2 M hm hk

end TransitionForm

private theorem current_numeric_of_subsumed
    {B F : TransitionForm Clock Var} (h : SyntacticallySubsumed B F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : B.EvaluatedNumeric σ P α k) {l : Local Clock Var} (hl : l ∈ B.current.locals) :
    F.currentNumericFilter σ P α k l := by
  have he := reset_apply_agree h.current.resets α α B.bodyFreeClocks h.outerFresh
    (fun _ _ => rfl)
  exact (l.numeric_congr_of_agree σ P _ _ k
    (fun c hc => he c (Or.inl ⟨l, hl, hc⟩))).1 (hi.1 l hl)

private theorem next_numeric_of_subsumed
    {B F : TransitionForm Clock Var} (h : SyntacticallySubsumed B F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : B.EvaluatedNumeric σ P α k)
    {N : StateForm Clock Var} (hN : B.nextPart = some N)
    {l : Local Clock Var} (hl : l ∈ N.locals) : F.nextNumericFilter σ P α k l := by
  intro M hM hk
  obtain ⟨K, hK, hinc, hfresh⟩ := h.next N hN
  have heK : K = M := Option.some.inj (hK.symm.trans hM)
  subst K
  have he := reset_apply_agree h.current.resets α α B.bodyFreeClocks h.outerFresh
    (fun _ _ => rfl)
  have hn : N.freeClocks ⊆ B.bodyFreeClocks := by
    intro c hc
    exact Or.inr (by simpa only [TransitionForm.bodyFreeClocks, hN] using hc)
  have heN := reset_apply_agree hinc.resets
    (ClockResetSet.elapse (B.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1,hk⟩))
    (ClockResetSet.elapse (F.current.resets.apply α)
      (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) N.localClocks hfresh
    (fun c hc => by simp only [ClockResetSet.elapse, he c (hn (Or.inr hc))])
  exact (l.numeric_congr_of_agree σ P _ _ _ (fun c hc => heN c ⟨l, hl, hc⟩)).1
    (hi.2 N hN hk l hl)

/-- A numeric branch remains subsumed after all target predicates violating
numeric clauses are removed, including predicates in the next part. -/
theorem SyntacticallySubsumed.numericProjectionTarget
    {B F : TransitionForm Clock Var} (h : SyntacticallySubsumed B F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : B.EvaluatedNumeric σ P α k) :
    SyntacticallySubsumed B (F.numericProjection σ P α k) := by
  apply h.restrictLocalsTarget
  · intro l hl
    exact current_numeric_of_subsumed h σ P α k hi hl
  · intro N M hN hM l hl
    exact next_numeric_of_subsumed h σ P α k hi hN hl

private theorem evaluatedNumeric_union
    {F B : TransitionForm Clock Var} (h : F.UnionCompatible B)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hF : F.EvaluatedNumeric σ P α k) (hB : B.EvaluatedNumeric σ P α k) :
    (F.union B).EvaluatedNumeric σ P α k := by
  constructor
  · intro l hl
    change l ∈ F.current.locals ∪ B.current.locals at hl
    exact hl.elim (current_numeric_of_subsumed h.left σ P α k hF)
      (current_numeric_of_subsumed h.right σ P α k hB)
  · intro N hN hk l hl
    have hmem : (∃ M, F.nextPart = some M ∧ l ∈ M.locals) ∨
        (∃ M, B.nextPart = some M ∧ l ∈ M.locals) := by
      cases hFn : F.nextPart <;> cases hBn : B.nextPart
      · simp [TransitionForm.union, TransitionForm.unionNext, hFn, hBn] at hN
      · simp only [TransitionForm.union, TransitionForm.unionNext, hFn, hBn,
          Option.some.injEq] at hN
        subst N
        exact Or.inr ⟨_, rfl, hl⟩
      · simp only [TransitionForm.union, TransitionForm.unionNext, hFn, hBn,
          Option.some.injEq] at hN
        subst N
        exact Or.inl ⟨_, rfl, hl⟩
      · simp only [TransitionForm.union, TransitionForm.unionNext, hFn, hBn,
          Option.some.injEq] at hN
        subst N
        change l ∈ _ ∪ _ at hl
        exact hl.elim (fun hm => Or.inl ⟨_, rfl, hm⟩)
          (fun hm => Or.inr ⟨_, rfl, hm⟩)
    rcases hmem with ⟨M, hM, hm⟩ | ⟨M, hM, hm⟩
    · exact next_numeric_of_subsumed h.left σ P α k hF hM hm N hN hk
    · exact next_numeric_of_subsumed h.right σ P α k hB hM hm N hN hk

namespace ClosureCatalogue

/-- Minimality propagates all non-past numeric clauses using guards alone.
The local preservation hypothesis is a rule contract, not closure existence
or a predicate-truth assumption. -/
theorem minimal_closure_numeric (E : ClosureCatalogue Clock Var)
    (preserve : ∀ {p Λ B}, E.Branch p Λ B →
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α)) →
      B.nonPredicateHolds σ P α k → B.EvaluatedNumeric σ P α k)
    {anchor F : TransitionForm Clock Var} (hc : E.IsClosure anchor F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : anchor.EvaluatedNumeric σ P α k)
    (hs : F.nonPredicateHolds σ P α k) : F.EvaluatedNumeric σ P α k := by
  have hanchor := hc.extension.numericProjectionTarget σ P α k hi
  have hclosed : E.IsClosed (F.numericProjection σ P α k) := by
    intro p hp
    obtain ⟨hpF, hpn⟩ := hp
    rcases hc.closed p hpF with hn | ⟨B, hb, hB⟩
    · exact Or.inl hn
    · have hBn := preserve hb σ P α k hpn (hB.nonPredicateHolds σ P α k hs)
      exact Or.inr ⟨B, hb, hB.numericProjectionTarget σ P α k hBn⟩
  have heq := E.minimal_restriction_eq hc _ _ hanchor hclosed
  change F = F.numericProjection σ P α k at heq
  have hn := F.numericProjection_numeric σ P α k
  rw [← heq] at hn
  exact hn

/-- Closure soundness needs only the numeric clauses actually used by local
rule soundness. No clause for no past satisfaction is propagated along an arbitrary path. -/
theorem closed_holds_of_atomicProjection_numeric (E : ClosureCatalogue Clock Var)
    (sound : ∀ {p Λ B}, E.Branch p Λ B →
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
      (∀ hk : k.1 < P.size, p.Numeric (P.interval ⟨k.1,hk⟩) (Λ.apply α)) →
      B.holds σ P α k → Judgement.holds σ P (Λ.apply α) k (.predicate p))
    {F : TransitionForm Clock Var} (hc : E.IsClosed F)
    (hadmit : ∀ p, Local.predicate p ∈ F.current.locals → E.Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hin : F.EvaluatedNumeric σ P α k)
    (hs : F.atomicProjection.holds σ P α k) : F.holds σ P α k := by
  classical
  have hpSat : ∀ p : Predicate Clock Var, Local.predicate p ∈ F.current.locals →
      Judgement.holds σ P (F.current.resets.apply α) k (.predicate p) := by
    intro p
    induction p using (measure Predicate.complexity).wf.induction with
    | h p ih =>
      intro hp
      by_cases ha : p.IsAtomic
      · have h := hs.1.2 (.predicate p) ⟨hp, ha⟩
        exact h
      · rcases hc p hp with hn | ⟨B, hb, hsub⟩
        · exact (hn (E.branch_exists p (hadmit p hp) ha F.current.resets)).elim
        · have hsmall : (F.restrictCurrent (fun l => l ∈ B.current.locals)).holds σ P α k := by
            refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
            intro l hl
            obtain ⟨hlF, hlB⟩ := hl
            cases l with
            | terminal => exact hs.1.2 .terminal ⟨hlF, trivial⟩
            | marker m => exact hs.1.2 (.marker m) ⟨hlF, trivial⟩
            | predicate q =>
                have hq := ih q (E.branch_reduced hb q hlB) hlF
                simpa only [Local.holds, Local.toJudgement, TransitionForm.restrictCurrent] using hq
          have hsat := (hsub.restrictTarget (fun l => l ∈ B.current.locals)
            (fun _ h => h)).sound σ P α k hsmall
          exact sound hb σ P α k (hin.1 (.predicate p) hp) hsat
  refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
  intro l hl
  cases l with
  | terminal => exact hs.1.2 .terminal ⟨hl, trivial⟩
  | marker m => exact hs.1.2 (.marker m) ⟨hl, trivial⟩
  | predicate p =>
      exact hpSat p hl

end ClosureCatalogue

namespace Local

theorem nonPredicate_of_holds (l : Local Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : l.holds σ P α k) :
    l.nonPredicateHolds σ P α k := by
  cases l with
  | terminal => exact hs
  | marker m => exact hs
  | predicate p => trivial

end Local
namespace StateForm

theorem nonPredicate_of_holds (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : S.holds σ P α k) :
    S.nonPredicateHolds σ P α k :=
  ⟨hs.1, fun l hl => l.nonPredicate_of_holds σ P _ k (hs.2 l hl)⟩

end StateForm
namespace TransitionForm

theorem nonPredicate_of_holds (F : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : F.holds σ P α k) :
    F.nonPredicateHolds σ P α k := by
  constructor
  · exact F.current.nonPredicate_of_holds σ P α k hs.1
  · cases hn : F.nextPart with
    | none => trivial
    | some N =>
        change (if hk : k.1 < P.size then _ else False)
        have hnext := hs.2
        split_ifs with hk
        · simp only [hn, dif_pos hk] at hnext
          exact N.nonPredicate_of_holds σ P _ _ hnext
        · simp only [hn, dif_neg hk] at hnext

theorem nonPredicate_of_atomicProjection (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.atomicProjection.holds σ P α k) : F.nonPredicateHolds σ P α k := by
  constructor
  · refine ⟨hs.1.1, ?_⟩
    intro l hl
    cases l with
    | terminal => exact hs.1.2 .terminal ⟨hl, trivial⟩
    | marker m => exact hs.1.2 (.marker m) ⟨hl, trivial⟩
    | predicate p => trivial
  · exact (F.atomicProjection.nonPredicate_of_holds σ P α k hs).2

end TransitionForm

namespace ConcreteContextual

private theorem state_guardTypes_holds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : S.nonPredicateHolds σ P α k) :
    (S.restrictLocals Local.IsMarker).holds σ P α k := by
  refine ⟨hs.1, ?_⟩
  intro l hl
  cases l with
  | terminal => exact hl.2.elim
  | predicate p => exact hl.2.elim
  | marker m => exact hs.2 (.marker m) hl.1

private theorem guardTypes_holds (F : TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.nonPredicateHolds σ P α k) :
    (F.restrictLocals Local.IsMarker Local.IsMarker).holds σ P α k := by
  refine ⟨state_guardTypes_holds F.current σ P α k hs.1, ?_⟩
  cases hn : F.nextPart with
  | none => simp [TransitionForm.restrictLocals, hn]
  | some N =>
      have hnext := hs.2
      simp only [hn] at hnext
      simp only [TransitionForm.restrictLocals, hn, Option.map_some]
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hnext ⊢
        exact state_guardTypes_holds N σ P _ _ hnext
      · simp only [dif_neg hk] at hnext

private theorem branchwise_step_numeric [DecidableEq Clock]
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hp : Local.predicate p ∈ F.current.locals) (h : catalogue.BranchwisePExpansion p F G)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : F.EvaluatedNumeric σ P α k)
    (hs : (G.restrictLocals Local.IsMarker Local.IsMarker).holds σ P α k) :
    G.EvaluatedNumeric σ P α k := by
  rcases h.eq_union_or_identity with ⟨_, rfl⟩ | ⟨B, hb, hu, rfl⟩
  · exact hi
  · have hTypeB := hu.right.type_subsumption.2.sound σ P α k hs
    have hB := NumericBranch.contextual_preserves_of_guardTypes hb σ P α k
      (hi.1 (.predicate p) hp)
      ((B.restrictLocals Local.IsMarker Local.IsMarker).nonPredicate_of_holds σ P α k hTypeB)
    exact evaluatedNumeric_union hu σ P α k hi hB

private theorem branchwise_path_subsumed [DecidableEq Clock]
    {F G : TransitionForm Clock Var}
    (h : ExpansionFamily.CurrentExpansionPath catalogue.BranchwisePExpansion F G) :
    SyntacticallySubsumed F G := by
  induction h with
  | nil => exact .refl _
  | cons _ hs _ ih => exact hs.extension.trans ih

private theorem branchwise_path_numeric [DecidableEq Clock]
    {F G : TransitionForm Clock Var}
    (h : ExpansionFamily.CurrentExpansionPath catalogue.BranchwisePExpansion F G)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : F.EvaluatedNumeric σ P α k)
    (hs : (G.restrictLocals Local.IsMarker Local.IsMarker).holds σ P α k) :
    G.EvaluatedNumeric σ P α k := by
  induction h with
  | nil => exact hi
  | cons hp hstep htail ih =>
      have hs' := (branchwise_path_subsumed htail).type_subsumption.2.sound σ P α k hs
      exact ih (branchwise_step_numeric hp hstep σ P α k hi hs') hs

/-- The closure-invariant corollary: project to guards, resets and
type judgements at both positions. The final closure supplies this data
for each step, and the numeric conjuncts propagate along the literal path. -/
theorem minimal_closure_numeric_of_guardTypes [DecidableEq Clock]
    {anchor F : TransitionForm Clock Var} (hc : catalogue.IsClosure anchor F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : anchor.EvaluatedNumeric σ P α k)
    (hs : (F.restrictLocals Local.IsMarker Local.IsMarker).holds σ P α k) :
    F.EvaluatedNumeric σ P α k :=
  branchwise_path_numeric (minimal_closure_guided_path hc) σ P α k hi hs

/-- The non-predicate conditions of a trace imply the guard and marker
conditions used to propagate the numeric invariant. -/
theorem minimal_closure_numeric [DecidableEq Clock]
    {anchor F : TransitionForm Clock Var} (hc : catalogue.IsClosure anchor F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : anchor.EvaluatedNumeric σ P α k)
    (hs : F.nonPredicateHolds σ P α k) : F.EvaluatedNumeric σ P α k :=
  minimal_closure_numeric_of_guardTypes hc σ P α k hi (guardTypes_holds F σ P α k hs)

/-- Theorem 4.14 (closure soundness). If the atomic projection is satisfied,
the closure is satisfied. The numeric invariant is transported along an
expansion path. -/
theorem minimal_closure_holds_of_atomicProjection [DecidableEq Clock]
    {anchor F : TransitionForm Clock Var} (hc : catalogue.IsClosure anchor F)
    (hadmit : ∀ p, Local.predicate p ∈ F.current.locals → catalogue.Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : anchor.EvaluatedNumeric σ P α k)
    (hs : F.atomicProjection.holds σ P α k) : F.holds σ P α k := by
  have hnum := minimal_closure_numeric hc σ P α k hi
    (F.nonPredicate_of_atomicProjection σ P α k hs)
  exact catalogue.closed_holds_of_atomicProjection_numeric
    (fun hb => NumericBranch.contextual_sound hb) hc.closed hadmit σ P α k hnum hs

end ConcreteContextual

end STLTableau.Section3
