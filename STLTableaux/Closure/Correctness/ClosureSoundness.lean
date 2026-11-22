import STLTableaux.Syntax.TransitionForms
import STLTableaux.Semantics.Invariants.Invariants

/-! Faithful mixed-syntax closure soundness by current-predicate complexity.
The catalogue interface contains local rule soundness and syntactic rank
reduction, not closure soundness. Instantiating normalization/branch provenance
for the full concrete catalogue remains a separate obligation. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace Predicate

def formulaComplexity : Formula Var → ℕ
  | .truth | .atom _ => 0
  | .neg φ => formulaComplexity φ
  | .and φ ψ | .until _ φ ψ => formulaComplexity φ + formulaComplexity ψ + 2

def complexity : Predicate Clock Var → ℕ
  | .plain φ => formulaComplexity φ
  | .upper _ _ _ _ φ | .bounded _ _ _ _ _ _ φ => formulaComplexity φ + 1

def IsAtomic : Predicate Clock Var → Prop
  | .plain .truth | .plain (.neg .truth) | .plain (.atom _) => True
  | _ => False

/-- The invariant, for both finite and infinite timing. -/
def Invariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size) :
    Predicate Clock Var → Prop
  | .plain _ => True
  | .upper c b kind (.bounded I) φ => STLTableau.Invariant σ P α k hk (.upper c b kind I φ)
  | .bounded c d b q kind (.bounded I) φ =>
      STLTableau.Invariant σ P α k hk (.bounded c d b q kind I φ)
  | .upper c b kind (.unbounded a) φ =>
      UnboundedClocked.Invariant σ P α k hk (.upper c b kind a φ)
  | .bounded c d b q kind (.unbounded a) φ =>
      UnboundedClocked.Invariant σ P α k hk (.bounded c d b q kind a φ)

end Predicate

namespace TransitionForm

def restrictCurrent (Φ : TransitionForm Clock Var) (Q : Local Clock Var → Prop) :
    TransitionForm Clock Var :=
  { Φ with current := { Φ.current with
      locals := {l ∈ Φ.current.locals | Q l}
      locals_finite := Φ.current.locals_finite.subset (fun _ h => h.1) } }

def KeepAtomic : Local Clock Var → Prop
  | .predicate p => p.IsAtomic
  | _ => True

def atomicProjection (Φ : TransitionForm Clock Var) : TransitionForm Clock Var :=
  Φ.restrictCurrent KeepAtomic

theorem atomicProjection_holds {Φ : TransitionForm Clock Var}
    {σ : FiniteSignal Var} {P : IntervalPartition σ.domain}
    {α : ClockValuation Clock} {k : STLTableau.Judgement.Position P}
    (h : Φ.holds σ P α k) : Φ.atomicProjection.holds σ P α k :=
  ⟨⟨h.1.1, fun l hl => h.1.2 l hl.1⟩, h.2⟩

end TransitionForm

theorem SyntacticallySubsumed.restrictTarget {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (Q : Local Clock Var → Prop)
    (hkeep : ∀ l ∈ Φ.current.locals, Q l) :
    SyntacticallySubsumed Φ (Ψ.restrictCurrent Q) :=
  { h with current := { h.current with
      locals := fun l hl => ⟨h.current.locals hl, hkeep l hl⟩ } }

/-- A normalized local branch catalogue, parameterized by its admitted source
syntax. `Branch p Λ B` represents a branch of p under the enclosing reset Λ.
Its soundness contract is the Section 3 local rule theorem plus normalization. -/
structure ClosureCatalogue (Clock Var : Type*) where
  Admitted : Predicate Clock Var → Prop
  Branch : Predicate Clock Var → ClockResetSet Clock → TransitionForm Clock Var → Prop
  branch_exists : ∀ p, Admitted p → ¬ p.IsAtomic → ∀ Λ, ∃ B, Branch p Λ B
  branch_reduced : ∀ {p Λ B}, Branch p Λ B → ∀ q,
    Local.predicate q ∈ B.current.locals → q.complexity < p.complexity
  branch_sound : ∀ {p Λ B}, Branch p Λ B →
    ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
      (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size),
      p.Invariant σ P (Λ.apply α) k hk → B.holds σ P α k →
        p.holds σ (P.interval ⟨k.1, hk⟩) (Λ.apply α)

namespace ClosureCatalogue

def RuleClosedFor (E : ClosureCatalogue Clock Var) (Φ : TransitionForm Clock Var)
    (p : Predicate Clock Var) : Prop :=
  (¬ ∃ B, E.Branch p Φ.current.resets B) ∨
    ∃ B, E.Branch p Φ.current.resets B ∧ SyntacticallySubsumed B Φ

def IsClosed (E : ClosureCatalogue Clock Var) (Φ : TransitionForm Clock Var) : Prop :=
  ∀ p, Local.predicate p ∈ Φ.current.locals → E.RuleClosedFor Φ p

/-- Theorem 4.14, with the local catalogue obligations explicit.
The proof reconstructs each removed predicate by strictly decreasing
complexity, while retaining the entire next part of the atomic projection. -/
theorem closed_holds_of_atomicProjection (E : ClosureCatalogue Clock Var)
    {Φ : TransitionForm Clock Var} (hc : E.IsClosed Φ)
    (hadmit : ∀ p, Local.predicate p ∈ Φ.current.locals → E.Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hinv : ∀ p, Local.predicate p ∈ Φ.current.locals →
      p.Invariant σ P (Φ.current.resets.apply α) k hk)
    (hs : Φ.atomicProjection.holds σ P α k) : Φ.holds σ P α k := by
  classical
  have hpSat : ∀ p : Predicate Clock Var, Local.predicate p ∈ Φ.current.locals →
      p.holds σ (P.interval ⟨k.1, hk⟩) (Φ.current.resets.apply α) := by
    intro p
    induction p using (measure Predicate.complexity).wf.induction with
    | h p ih =>
        intro hp
        by_cases ha : p.IsAtomic
        · have h := hs.1.2 (.predicate p) ⟨hp, ha⟩
          simpa only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos hk,
        TransitionForm.atomicProjection, TransitionForm.restrictCurrent] using h
        · rcases hc p hp with hn | ⟨B, hB, hsub⟩
          · exact (hn (E.branch_exists p (hadmit p hp) ha Φ.current.resets)).elim
          · have hsmall : (Φ.restrictCurrent (fun l => l ∈ B.current.locals)).holds σ P α k := by
              refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
              intro l hl
              rcases hl with ⟨hlΦ, hlB⟩
              cases l with
              | terminal => exact hs.1.2 .terminal ⟨hlΦ, trivial⟩
              | marker m => exact hs.1.2 (.marker m) ⟨hlΦ, trivial⟩
              | predicate q =>
                  have hq := ih q (E.branch_reduced hB q hlB) hlΦ
                  simpa only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos hk,
        TransitionForm.atomicProjection, TransitionForm.restrictCurrent] using hq
            have hsB := (hsub.restrictTarget (fun l => l ∈ B.current.locals)
              (fun _ h => h)).sound σ P α k hsmall
            exact E.branch_sound hB σ P α k hk (hinv p hp) hsB
  refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
  intro l hl
  cases l with
  | terminal => exact hs.1.2 .terminal ⟨hl, trivial⟩
  | marker m => exact hs.1.2 (.marker m) ⟨hl, trivial⟩
  | predicate p =>
      simpa only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos hk,
        TransitionForm.atomicProjection, TransitionForm.restrictCurrent] using hpSat p hl

theorem closed_atomicProjection_iff (E : ClosureCatalogue Clock Var)
    {Φ : TransitionForm Clock Var} (hc : E.IsClosed Φ)
    (hadmit : ∀ p, Local.predicate p ∈ Φ.current.locals → E.Admitted p)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (hinv : ∀ p, Local.predicate p ∈ Φ.current.locals →
      p.Invariant σ P (Φ.current.resets.apply α) k hk) :
    Φ.atomicProjection.holds σ P α k ↔ Φ.holds σ P α k :=
  ⟨E.closed_holds_of_atomicProjection hc hadmit σ P α k hk hinv,
    TransitionForm.atomicProjection_holds⟩

end ClosureCatalogue
end STLTableau.Section3
