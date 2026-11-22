import STLTableaux.Finiteness.Correctness.JudgementTableau
import STLTableaux.Tableau.Correctness.TableauSoundness

/-! Conditional graph induction for judgement states. These are local algebraic
laws of a relation, not an instantiation of the new structural relation or a
representative-path existence theorem. -/
namespace STLTableau.Section4.Finiteness.JudgementTableau
open Section3
variable {Clock Var : Type*}

/-- Three local laws to discharge for the eventual structural derivation relation.
No path soundness or global representative assumption occurs in this interface. -/
structure LocalLaws (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop) : Prop where
  nonPredicate : ∀ {N F}, R N F → ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
    F.nonPredicateHolds σ P α k → N.nonPredicateHolds σ P α k
  numeric : ∀ {N F}, R N F → ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
    N.EvaluatedNumeric σ P α k → F.nonPredicateHolds σ P α k → F.EvaluatedNumeric σ P α k
  recover : ∀ {N F}, R N F → ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P),
    N.EvaluatedNumeric σ P α k → F.atomicProjection.holds σ P α k →
      F.holds σ P α k ∧ N.holds σ P α k

private theorem current_nonPredicate_of_atomic (F : Section3.TransitionForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : (∀ g ∈ F.current.guards, g.holds α) ∧
      ∀ l ∈ labels F, l.holds σ P (F.current.resets.apply α) k) :
    F.current.nonPredicateHolds σ P α k := by
  refine ⟨h.1,?_⟩
  intro l hl
  cases l with
  | terminal => exact h.2 .terminal ⟨hl,trivial⟩
  | marker m => exact h.2 (.marker m) ⟨hl,trivial⟩
  | predicate p => trivial

 theorem nonPredicate_of_atomic_trace
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (laws : LocalLaws R) (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (ha : p.accepting (tableau X Q root R))
    (he : p.firstIncoming = incoming p.firstState)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hs : (p.trace labels labels_finite).holds σ P α k) :
    p.firstState.nonPredicateHolds σ P α k := by
  induction p generalizing α k with
  | last e F =>
    change F.nonPredicateHolds σ P α k
    change e = incoming F at he
    subst e
    refine ⟨current_nonPredicate_of_atomic F σ P α k hs,?_⟩
    have hn : F.nextPart = none := ha.2
    simp only [hn]
  | step e F t ih =>
    change F.nonPredicateHolds σ P α k
    obtain ⟨_,_,N,hn,hR,hedge⟩ := ha.1.2.2
    have ht : t.accepting (tableau X Q root R) := ⟨ha.1.2.1,ha.2⟩
    change e = incoming F at he
    subst e
    change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
    refine ⟨current_nonPredicate_of_atomic F σ P α k hs.1,?_⟩
    rw [hn]
    by_cases hk : k.1 < P.size
    · simp only [dif_pos hk] at hs ⊢
      exact laws.nonPredicate hR σ P _ _ (ih ht hedge _ _ hs.2)
    · simpa only [dif_neg hk] using hs.2

/-- Backward guard recovery, forward numeric propagation, then backward truth
recovery along the actual graph edges and incoming resets. -/
 theorem fullTrace_and_input_of_atomic_trace
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (laws : LocalLaws R) (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (ha : p.accepting (tableau X Q root R))
    (he : p.firstIncoming = incoming p.firstState)
    (N : Section3.StateForm Clock Var) (hR : R N p.firstState)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hi : N.EvaluatedNumeric σ P α k)
    (hs : (p.trace labels labels_finite).holds σ P α k) :
    (fullTrace p).holds σ P α k ∧ p.firstState.holds σ P α k ∧ N.holds σ P α k := by
  induction p generalizing N α k with
  | last e F =>
    change e = incoming F at he
    subst e
    have hat : F.atomicProjection.holds σ P α k := by
      refine ⟨hs,?_⟩
      have hn : F.nextPart = none := ha.2
      simp only [Section3.TransitionForm.atomicProjection,Section3.TransitionForm.restrictCurrent,hn]
    have hf := laws.recover hR σ P α k hi hat
    exact ⟨hf.1.1,hf⟩
  | step e F t ih =>
    have hnp := nonPredicate_of_atomic_trace R laws X Q root (.step e F t) ha he σ P α k hs
    obtain ⟨_,_,M,hn,hM,hedge⟩ := ha.1.2.2
    have ht : t.accepting (tableau X Q root R) := ⟨ha.1.2.1,ha.2⟩
    have hnum := laws.numeric hR σ P α k hi hnp
    change e = incoming F at he
    subst e
    change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
    by_cases hk : k.1 < P.size
    · simp only [dif_pos hk] at hs
      have tail := ih ht hedge M hM _ _ (hnum.2 M hn hk) hs.2
      have hat : F.atomicProjection.holds σ P α k := by
        refine ⟨hs.1,?_⟩
        change match F.nextPart with | none => True | some N => _
        rw [hn]
        simpa only [Path.firstState,dif_pos hk,Section3.TransitionForm.atomicProjection,
          Section3.TransitionForm.restrictCurrent] using tail.2.2
      have hf := laws.recover hR σ P α k hi hat
      refine ⟨?_,hf⟩
      change F.current.holds σ P α k ∧ (if h : k.1 < P.size then _ else False)
      exact ⟨hf.1.1,by simpa only [Path.firstState,dif_pos hk,Trace.holds,fullTrace,incoming] using tail.1⟩
    · simp only [dif_neg hk] at hs
      exact hs.2.elim

/-- Initial membership supplies the root relation and exact incoming label. -/
theorem fullTrace_and_root_of_accepting_run
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (laws : LocalLaws R) (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (tableau X Q root R)) (ha : p.accepting (tableau X Q root R))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hi : root.EvaluatedNumeric σ P α k)
    (hs : (p.trace labels labels_finite).holds σ P α k) :
    (fullTrace p).holds σ P α k ∧ p.firstState.holds σ P α k ∧ root.holds σ P α k :=
  fullTrace_and_input_of_atomic_trace R laws X Q root p ha hr.2.2 root hr.2.1 σ P α k hi hs

/-- Recognition soundness for the root `[φ]` under the local rule laws. -/
theorem formula_of_recognizes
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (laws : LocalLaws R) (X : Set Var) (Q : Set Clock) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (tableau X Q (Section3.StateForm.ofLocal (.predicate (.plain φ))) R).recognizes
      labels_finite σ P) : σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ := by
  obtain ⟨p,hr,ha,htrace⟩ := hs
  let α : ClockValuation Clock := fun _ => 0
  have hi : (Section3.StateForm.ofLocal (.predicate (.plain φ))).EvaluatedNumeric
      σ P α ⟨0,by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain φ) := hl
    subst l
    intro hk
    trivial
  have hroot := (fullTrace_and_root_of_accepting_run R laws X Q _ p hr ha σ P α
    ⟨0,by omega⟩ hi (htrace α)).2.2
  have hplain := hroot.2 (.predicate (.plain φ)) (by simp [Section3.StateForm.ofLocal])
  have hk := Generated.partition_size_pos σ P
  change (if h : 0 < P.size then _ else False) at hplain
  simp only [dif_pos hk] at hplain
  exact hplain ⟨0,le_rfl,σ.horizon_pos⟩ (Generated.zero_mem_first_interval σ P)

end STLTableau.Section4.Finiteness.JudgementTableau
