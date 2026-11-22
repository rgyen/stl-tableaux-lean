import STLTableaux.Tableau.Construction.TableauState
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder
import STLTableaux.Semantics.Invariants.EvaluatedInvariant
import STLTableaux.Closure.Normalization.NormalizedStability
import STLTableaux.Closure.Correctness.FaithfulClosureCompleteness

/-! Tableau construction (Definition 4.28) and generator path existence
(Lemma 4.33). Backward induction on partition positions uses a satisfied
closure at each step. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}

namespace Generated

def labels (s : ClosureState Clock Var) : Set (Local Clock Var) :=
  {l ∈ s.form.current.locals | Section3.TransitionForm.KeepAtomic l}

theorem labels_finite (s : ClosureState Clock Var) : (labels s).Finite :=
  s.form.current.locals_finite.subset (fun _ h => h.1)

/-- The tableau of Definition 4.28 for a given closure relation. A state is
final when its closure has no next-part. -/
def tableau (X : Set Var) (Xc : Set Clock)
    (initialGenerator : Section3.StateForm Clock Var)
    (closure : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop) :
    Tableau Clock Var (ClosureState Clock Var) where
  realVariables := X
  clocks := Xc
  states := {s | closure s.generator s.form}
  edges := {e | closure e.1.generator e.1.form ∧
    closure e.2.2.generator e.2.2.form ∧ e.1.edge e.2.1 e.2.2}
  initial := {e | closure e.2.generator e.2.form ∧
    e.2.generator = initialGenerator ∧ e.1 = e.2.incoming}
  final := {s | s.form.nextPart = none}
  label := labels
  label_atomic := fun _ _ h => h.2

end Generated

namespace Path

/-- Definition 4.30 (full trace). Each state contributes all its local
judgements, including non-atomic interval predicates. -/
def fullTrace : Path Clock (ClosureState Clock Var) → Trace Clock Var :=
  trace (fun s => s.form.current.locals) (fun s => s.form.current.locals_finite)

theorem first_mem_of_valid (T : Tableau Clock Var (ClosureState Clock Var))
    (p : Path Clock (ClosureState Clock Var)) (hp : p.valid T) : p.firstState ∈ T.states := by
  cases p with
  | last e s => exact hp
  | step e s t => exact hp.1

end Path

namespace Generated

/-- Backward induction for Lemma 4.33. Select a satisfied closure whose
next-part, if present, satisfies `Good` at the next position after applying
the closure's resets and elapsing the current interval. -/
theorem generator_path_exists_of_closure_selection
    (X : Set Var) (Xc : Set Clock)
    (initialGenerator : Section3.StateForm Clock Var)
    (closure : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (Good : ClockValuation Clock → STLTableau.Judgement.Position P →
      Section3.StateForm Clock Var → Prop)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (S : Section3.StateForm Clock Var), Good α k S → S.holds σ P α k →
      ∃ Φ : Section3.TransitionForm Clock Var, closure S Φ ∧ Φ.holds σ P α k ∧
        ∀ (N : Section3.StateForm Clock Var), Φ.nextPart = some N →
          ∀ hk : k.1 < P.size,
            Good (ClockResetSet.elapse (Φ.current.resets.apply α)
              (STLTableau.Judgement.duration P ⟨k.1,hk⟩)) ⟨k.1+1,by omega⟩ N)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (S : Section3.StateForm Clock Var) (hg : Good α k S) (hs : S.holds σ P α k) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.firstState.generator = S ∧ p.firstIncoming = p.firstState.incoming ∧
      p.accepting (tableau X Xc initialGenerator closure) ∧ p.fullTrace.holds σ P α k := by
  have main : ∀ n : ℕ, ∀ (k : STLTableau.Judgement.Position P)
      (α : ClockValuation Clock) (S : Section3.StateForm Clock Var),
      P.size - k.1 = n → Good α k S → S.holds σ P α k →
      ∃ p : Path Clock (ClosureState Clock Var),
        p.firstState.generator = S ∧ p.firstIncoming = p.firstState.incoming ∧
        p.accepting (tableau X Xc initialGenerator closure) ∧ p.fullTrace.holds σ P α k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k α S hn hg hs
      obtain ⟨Φ, hc, hΦ, hnextGood⟩ := select α k S hg hs
      let s : ClosureState Clock Var := ⟨Φ,S⟩
      cases hnext : Φ.nextPart with
      | none =>
          refine ⟨.last s.incoming s, rfl, rfl, ?_, ?_⟩
          · exact ⟨hc, hnext⟩
          · exact hΦ.1
      | some N =>
          have hk : k.1 < P.size := by
            by_contra hnot
            have hf := hΦ.2
            simp only [hnext, dif_neg hnot] at hf
          let k' : STLTableau.Judgement.Position P := ⟨k.1+1,by omega⟩
          let β := ClockResetSet.elapse (Φ.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1,hk⟩)
          have hsN : N.holds σ P β k' := by
            simpa only [hnext, dif_pos hk] using hΦ.2
          have hlt : P.size - k'.1 < n := by dsimp [k']; omega
          obtain ⟨p, hpS, hpE, hpA, hpH⟩ :=
            ih (P.size - k'.1) hlt k' β N rfl (hnextGood N hnext hk) hsN
          refine ⟨.step s.incoming s p, rfl, rfl, ?_, ?_⟩
          · refine ⟨⟨hc, hpA.1, ?_⟩, hpA.2⟩
            refine ⟨hc, Path.first_mem_of_valid _ p hpA.1, ?_⟩
            exact ⟨hnext.trans (congrArg some hpS.symm), hpE⟩
          · change Φ.current.holds σ P α k ∧
              (if h : k.1 < P.size then _ else False)
            exact ⟨hΦ.1, by
              simpa only [dif_pos hk, Trace.holds, Path.fullTrace, β, k', s,
                ClosureState.incoming] using hpH⟩
  exact main (P.size - k.1) k α S rfl hg hs

/-- Definition 4.28 using the closure relation of an expansion rule catalogue. -/
def closureTableau (E : ClosureCatalogue Clock Var) (X : Set Var) (Xc : Set Clock)
    (initialGenerator : Section3.StateForm Clock Var) :
    Tableau Clock Var (ClosureState Clock Var) :=
  tableau X Xc initialGenerator (fun S Φ => E.IsClosure (Section3.TransitionForm.ofState S) Φ)

/-- In the induction for Lemma 4.33, a satisfied closure that preserves
stability and the evaluated invariant supplies both conditions for its
successor generator. -/
theorem generator_path_exists_of_preserving_closures
    (E : ClosureCatalogue Clock Var) (X : Set Var) (Xc : Set Clock)
    (initialGenerator : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (select : ∀ (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
      (S : Section3.StateForm Clock Var),
      S.UnderlyingStable σ P → S.EvaluatedInvariant σ P α k → S.holds σ P α k →
      ∃ Φ : Section3.TransitionForm Clock Var,
        E.IsClosure (Section3.TransitionForm.ofState S) Φ ∧ Φ.holds σ P α k ∧
        Φ.EvaluatedInvariant σ P α k ∧ Φ.UnderlyingStable σ P)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (S : Section3.StateForm Clock Var) (hst : S.UnderlyingStable σ P)
    (hi : S.EvaluatedInvariant σ P α k) (hs : S.holds σ P α k) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.firstState.generator = S ∧ p.firstIncoming = p.firstState.incoming ∧
      p.accepting (closureTableau E X Xc initialGenerator) ∧ p.fullTrace.holds σ P α k := by
  apply generator_path_exists_of_closure_selection X Xc initialGenerator
    (fun S Φ => E.IsClosure (Section3.TransitionForm.ofState S) Φ) σ P
    (fun α k S => S.UnderlyingStable σ P ∧ S.EvaluatedInvariant σ P α k) ?_ α k S ⟨hst,hi⟩ hs
  intro β j G hgood hG
  obtain ⟨Φ, hc, hΦ, hiΦ, hstΦ⟩ := select β j G hgood.1 hgood.2 hG
  refine ⟨Φ, hc, hΦ, ?_⟩
  intro N hN hj
  exact ⟨hstΦ.next N hN, hiΦ.2 N hN hj⟩

/-- Lemma 4.33 (generator path existence). A satisfied state-form judgement
with stable underlying formulas and evaluated invariants has an accepting
path whose full trace is satisfied. -/
theorem generator_path_exists [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (initialGenerator : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (S : Section3.StateForm Clock Var) (hst : S.UnderlyingStable σ P)
    (hi : S.EvaluatedInvariant σ P α k) (hs : S.holds σ P α k) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.firstState.generator = S ∧ p.firstIncoming = p.firstState.incoming ∧
      p.accepting (closureTableau ConcreteContextual.catalogue X Xc initialGenerator) ∧
      p.fullTrace.holds σ P α k :=
  generator_path_exists_of_preserving_closures ConcreteContextual.catalogue X Xc
    initialGenerator σ P (fun β j G hstG hiG hsG =>
      FaithfulClosure.satisfied_closure_exists G σ P β j hsG hiG hstG) α k S hst hi hs

/-- Lemma 4.33 with the starting state exhibited as a closure and generator pair. -/
theorem generator_path_exists_with_closure [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (Xc : Set Clock) (initialGenerator : Section3.StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (S : Section3.StateForm Clock Var) (hst : S.UnderlyingStable σ P)
    (hi : S.EvaluatedInvariant σ P α k) (hs : S.holds σ P α k) :
    ∃ (Φ : Section3.TransitionForm Clock Var) (p : Path Clock (ClosureState Clock Var)),
      ConcreteContextual.catalogue.IsClosure (Section3.TransitionForm.ofState S) Φ ∧
      p.firstState = ⟨Φ,S⟩ ∧ p.firstIncoming = p.firstState.incoming ∧
      p.accepting (closureTableau ConcreteContextual.catalogue X Xc initialGenerator) ∧
      p.fullTrace.holds σ P α k := by
  obtain ⟨p, hpS, hpE, hpA, hpH⟩ :=
    generator_path_exists X Xc initialGenerator σ P α k S hst hi hs
  have hc := Path.first_mem_of_valid _ p hpA.1
  change ConcreteContextual.catalogue.IsClosure
    (Section3.TransitionForm.ofState p.firstState.generator) p.firstState.form at hc
  rw [hpS] at hc
  refine ⟨p.firstState.form, p, hc, ?_, hpE, hpA, hpH⟩
  cases h : p.firstState with
  | mk F G =>
      have : G = S := by simpa only [h] using hpS
      simp only [h, this]

end Generated
end STLTableau.Section4
