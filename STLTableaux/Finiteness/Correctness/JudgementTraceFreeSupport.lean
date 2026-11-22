import STLTableaux.Finiteness.Correctness.JudgementTableau

/-! Free-clock safety of an actual linked judgement-tableau path. This is a
proof about a supplied relation, with no change to tableau edges or states. -/
namespace STLTableau.Section4.Finiteness.JudgementTableau
open Section3
variable {Clock Var : Type*}

/-- Incoming edge labels must be the actual current guards and resets. -/
theorem fullTrace_free_subset_input
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (hR : ∀ N F,R N F→F.freeClocks⊆N.freeClocks)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hv : p.valid (tableau X Q root R))
    (he : p.firstIncoming=incoming p.firstState)
    (N : Section3.StateForm Clock Var) (hN : R N p.firstState) :
    (fullTrace p).freeClocks⊆N.freeClocks := by
  induction p generalizing N with
  | last e F =>
    change e=incoming F at he
    subst e
    intro c hc
    apply hR N F hN
    change c∈F.current.freeClocks at hc
    rcases hc with hc | ⟨hc,hn⟩
    · exact Or.inl hc
    · exact Or.inr ⟨Or.inl hc,hn⟩
  | step e F tail ih =>
    obtain ⟨_,_,M,hnext,hM,hincoming⟩ := hv.2.2
    have ht := ih hv.2.1 hincoming M hM
    change e=incoming F at he
    subst e
    intro c hc
    apply hR N F hN
    rcases hc with hc | ⟨hc,hn⟩
    · exact Or.inl hc
    · refine Or.inr ⟨?_,hn⟩
      rcases hc with hc | hc
      · exact Or.inl hc
      · right
        change c∈(match F.nextPart with | none=>∅ | some S=>S.freeClocks)
        rw [hnext]
        exact ht hc

/-- Free-safe initial edges close the entire full trace when the root is closed. -/
theorem fullTrace_closed_of_run
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (hR : ∀ N F,R N F→F.freeClocks⊆N.freeClocks)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (tableau X Q root R)) (hc : root.freeClocks=∅) :
    (fullTrace p).freeClocks=∅ := by
  apply Set.eq_empty_of_subset_empty
  rw [←hc]
  exact fullTrace_free_subset_input X Q root R hR p hr.1 hr.2.2 root hr.2.1

/-- A fixed path, not a valuation-dependent selection, works for every valuation. -/
theorem fullTrace_holds_all_valuations
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var→Section3.TransitionForm Clock Var→Prop)
    (hR : ∀ N F,R N F→F.freeClocks⊆N.freeClocks)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (tableau X Q root R)) (hc : root.freeClocks=∅)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : (fullTrace p).holds σ P α k) :
    ∀β : ClockValuation Clock,(fullTrace p).holds σ P β k := by
  intro β
  exact ((fullTrace p).holds_independent_of_initial_clocks σ P
    (fullTrace_closed_of_run X Q root R hR p hr hc) α β k).1 hs
end STLTableau.Section4.Finiteness.JudgementTableau

namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*}

/-- Dropping non-atomic labels does not introduce any free clock reads. -/
theorem ordinaryTrace_free_subset_fullTrace
    (p : Path Clock (Section3.TransitionForm Clock Var)) :
    (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks ⊆
      (JudgementTableau.fullTrace p).freeClocks := by
  induction p with
  | last l F =>
    rintro c (hg | ⟨⟨a, ha, hc⟩, hn⟩)
    · exact Or.inl hg
    · exact Or.inr ⟨⟨a, ha.1, hc⟩, hn⟩
  | step l F p ih =>
    rintro c (hg | ⟨hc, hn⟩)
    · exact Or.inl hg
    · refine Or.inr ⟨?_, hn⟩
      rcases hc with ⟨a, ha, hc⟩ | hc
      · exact Or.inl ⟨a, ha.1, hc⟩
      · exact Or.inr (ih hc)

end STLTableau.Section4.Finiteness
