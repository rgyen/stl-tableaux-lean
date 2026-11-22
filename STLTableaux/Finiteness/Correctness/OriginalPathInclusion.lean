import STLTableaux.Finiteness.Derivation.DerivationRelation

/-! Original path inclusion from a ready root. Readiness is propagated along
actual closures; no assertion that arbitrary original generators are ready. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

 theorem original_valid_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (p : Path Clock (ClosureState Clock Var))
    (hp : p.valid (Generated.closureTableau ConcreteContextual.catalogue X Q root))
    (hr : p.firstState.generator.Ready) :
    (JudgementTableau.forgetGenerator p).valid (JudgementTableau.tableau X Q root Derives) := by
  induction p with
  | last e s => exact ⟨s.generator,Derives.original hp hr⟩
  | step e s t ih =>
    have hready := ConcreteContextual.closure_ready hp.1
      ((Section3.TransitionForm.ready_ofState s.generator).2 hr)
    have hedge : s.form.nextPart = some t.firstState.generator ∧
        t.firstIncoming = t.firstState.incoming := hp.2.2.2.2
    have ht := ih hp.2.1 (hready.2 t.firstState.generator hedge.1)
    refine ⟨⟨s.generator,Derives.original hp.1 hr⟩,ht,?_⟩
    rw [JudgementTableau.first_state,JudgementTableau.first_incoming]
    refine ⟨⟨s.generator,Derives.original hp.1 hr⟩,?_,t.firstState.generator,
      hedge.1,?_,hedge.2⟩
    · exact ⟨t.firstState.generator,Derives.original (Path.first_mem_of_valid _ t hp.2.1)
        (hready.2 t.firstState.generator hedge.1)⟩
    · exact Derives.original (Path.first_mem_of_valid _ t hp.2.1)
        (hready.2 t.firstState.generator hedge.1)

 theorem original_run_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (hroot : root.Ready)
    (p : Path Clock (ClosureState Clock Var))
    (hp : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q root)) :
    (JudgementTableau.forgetGenerator p).run (JudgementTableau.tableau X Q root Derives) := by
  have hr : p.firstState.generator.Ready := hp.2.2.1 ▸ hroot
  refine ⟨original_valid_forward X Q root p hp.1 hr,?_⟩
  rw [JudgementTableau.first_state,JudgementTableau.first_incoming]
  refine ⟨?_,hp.2.2.2⟩
  have hc := hp.2.1
  rw [hp.2.2.1] at hc
  exact Derives.original hc hroot

 theorem original_accepting_run_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (hroot : root.Ready)
    (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (Generated.closureTableau ConcreteContextual.catalogue X Q root))
    (ha : p.accepting (Generated.closureTableau ConcreteContextual.catalogue X Q root)) :
    (JudgementTableau.forgetGenerator p).run (JudgementTableau.tableau X Q root Derives) ∧
      (JudgementTableau.forgetGenerator p).accepting (JudgementTableau.tableau X Q root Derives) := by
  have hrun := original_run_forward X Q root hroot p hr
  refine ⟨hrun,hrun.1,?_⟩
  change (JudgementTableau.forgetGenerator p).lastState.nextPart = none
  rw [JudgementTableau.last_state]
  exact ha.2

 theorem original_recognizes_forward (X : Set Var) (Q : Set Clock)
    (root : Section3.StateForm Clock Var) (hroot : root.Ready)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (Generated.closureTableau ConcreteContextual.catalogue X Q root).recognizes
      Generated.labels_finite σ P) :
    (JudgementTableau.tableau X Q root Derives).recognizes JudgementTableau.labels_finite σ P := by
  obtain ⟨p,hr,ha,ht⟩ := hs
  have hm := original_accepting_run_forward X Q root hroot p hr ha
  refine ⟨JudgementTableau.forgetGenerator p,hm.1,hm.2,?_⟩
  intro α
  change ((JudgementTableau.forgetGenerator p).trace JudgementTableau.labels
    JudgementTableau.labels_finite).holds σ P α ⟨0,by omega⟩
  rw [JudgementTableau.ordinary_trace_forward]
  exact ht α

end STLTableau.Section4.Finiteness
