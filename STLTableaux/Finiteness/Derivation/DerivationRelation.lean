import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Finiteness.Derivation.DerivationNumeric
import STLTableaux.Finiteness.Correctness.JudgementTableauSoundness

/-! The derivation relation admits an original closure of a ready input or
a safely normalized finite resolution tree. The soundness results derive
semantic preservation from these syntactic premises. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

inductive Derives : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop
  | original {N F} : ConcreteContextual.catalogue.IsClosure (.ofState N) F →
      N.Ready → Derives N F
  | resolved {N F J H A} : Resolve J H A →
      SafeNormalization J (.ofState N) → SafeNormalization H F →
      SafeNormalization A F.atomicProjection → Derives N F

omit [DecidableEq Clock] in
 theorem atomicProjection_nonPredicate_iff (F : Section3.TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    F.atomicProjection.nonPredicateHolds σ P α k ↔ F.nonPredicateHolds σ P α k := by
  constructor
  · intro h
    refine ⟨⟨h.1.1,?_⟩,h.2⟩
    intro l hl
    cases l with
    | terminal => exact h.1.2 .terminal ⟨hl,trivial⟩
    | marker m => exact h.1.2 (.marker m) ⟨hl,trivial⟩
    | predicate p => trivial
  · intro h
    exact ⟨⟨h.1.1,fun l hl => h.1.2 l hl.1⟩,h.2⟩

 theorem derives_localLaws [Nontrivial Clock] : JudgementTableau.LocalLaws (Derives (Clock := Clock) (Var := Var)) := by
  constructor
  · intro N F h σ P α k hs
    cases h with
    | original hc hr => exact (hc.extension.nonPredicateHolds σ P α k hs).1
    | resolved D hJ hH hA =>
      have ha := (hA.nonPredicate σ P α k).1 ((atomicProjection_nonPredicate_iff F σ P α k).2 hs)
      exact ((hJ.nonPredicate σ P α k).2 (D.nonPredicate_recover σ P α k ha).1).1
  · intro N F h σ P α k hi hs
    have hin : (Section3.TransitionForm.ofState N).EvaluatedNumeric σ P α k :=
      ⟨hi,by intro M hm; cases hm⟩
    cases h with
    | original hc hr => exact ConcreteContextual.minimal_closure_numeric hc σ P α k hin hs
    | resolved D hJ hH hA =>
      have ha := (hA.nonPredicate σ P α k).1 ((atomicProjection_nonPredicate_iff F σ P α k).2 hs)
      exact (hH.numeric σ P α k).2
        (D.numeric_occurrences_and_outputs σ P α k ((hJ.numeric σ P α k).1 hin) ha).2.1
  · intro N F h σ P α k hi hs
    have hin : (Section3.TransitionForm.ofState N).EvaluatedNumeric σ P α k :=
      ⟨hi,by intro M hm; cases hm⟩
    cases h with
    | original hc hr =>
      have hready := ConcreteContextual.closure_ready hc
        ((Section3.TransitionForm.ready_ofState N).2 hr)
      have hf := ConcreteContextual.minimal_closure_holds_of_atomicProjection hc
        (fun p hp => (hready.1 (.predicate p) hp).admitted) σ P α k hin hs
      exact ⟨hf,(hc.extension.sound σ P α k hf).1⟩
    | resolved D hJ hH hA =>
      have hh := D.recover_from_input_numeric σ P α k ((hJ.numeric σ P α k).1 hin)
        ((hA.holds σ P α k).1 hs)
      exact ⟨(hH.holds σ P α k).2 hh.2, ((hJ.holds σ P α k).2 hh.1).1⟩

/-- Recognition soundness for the instantiated structural graph. -/
theorem derives_formula_of_recognizes [Nontrivial Clock]
    (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (JudgementTableau.tableau X Q (Section3.StateForm.ofLocal (.predicate (.plain φ)))
      Derives).recognizes JudgementTableau.labels_finite σ P) :
    σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ :=
  JudgementTableau.formula_of_recognizes Derives derives_localLaws X Q φ σ P hs

 theorem derives_fullTrace_and_root [Nontrivial Clock]
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (JudgementTableau.tableau X Q root Derives))
    (ha : p.accepting (JudgementTableau.tableau X Q root Derives))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hi : root.EvaluatedNumeric σ P α k)
    (hs : (p.trace JudgementTableau.labels JudgementTableau.labels_finite).holds σ P α k) :
    (JudgementTableau.fullTrace p).holds σ P α k ∧
      p.firstState.holds σ P α k ∧ root.holds σ P α k :=
  JudgementTableau.fullTrace_and_root_of_accepting_run Derives derives_localLaws
    X Q root p hr ha σ P α k hi hs

end STLTableau.Section4.Finiteness
