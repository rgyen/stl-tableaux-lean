import STLTableaux.Closure.Normalization.NonPredicateAlphaTransport

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace StateForm
theorem nonPredicate_of_included {S T : StateForm Clock Var} (h : ComponentsIncluded S T)
    (hfresh : Disjoint T.resets.clocks (S.localClocks \ S.resets.clocks))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ S.freeClocks, α c = β c) (hs : T.nonPredicateHolds σ P β k) :
    S.nonPredicateHolds σ P α k := by
  constructor
  · intro g hg
    have hc := hagree g.clock (Or.inl ⟨g, hg, rfl⟩)
    simpa only [Guard.holds, hc] using hs.1 g (h.guards hg)
  · have he := reset_apply_agree h.resets α β S.localClocks hfresh
      (fun c hc => hagree c (Or.inr hc))
    intro l hl
    exact (l.nonPredicate_congr_of_agree σ P _ _ k (fun c hc => he c ⟨l, hl, hc⟩)).2
      (hs.2 l (h.locals hl))

end StateForm

theorem SyntacticallySubsumed.nonPredicateHolds {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : Ψ.nonPredicateHolds σ P α k) :
    Φ.nonPredicateHolds σ P α k := by
  have hcurrentFresh : Disjoint Ψ.current.resets.clocks
      (Φ.current.localClocks \ Φ.current.resets.clocks) := by
    apply Set.disjoint_left.2
    intro c hc hcΦ
    apply Set.disjoint_left.1 h.outerFresh hc
    exact ⟨Or.inl hcΦ.1, hcΦ.2⟩
  refine ⟨StateForm.nonPredicate_of_included h.current hcurrentFresh σ P α α k
    (fun _ _ => rfl) hs.1, ?_⟩
  cases hn : Φ.nextPart with
  | none => trivial
  | some N =>
      obtain ⟨M, hm, hNM, hfresh⟩ := h.next N hn
      simp only [TransitionForm.nonPredicateHolds, hm] at hs
      dsimp only
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs ⊢
        apply StateForm.nonPredicate_of_included hNM hfresh σ P _ _ _ ?_ hs.2
        have he := reset_apply_agree h.current.resets α α Φ.bodyFreeClocks h.outerFresh
          (fun _ _ => rfl)
        intro c hc
        have hb : c ∈ Φ.bodyFreeClocks := by
          change c ∈ Φ.current.localClocks ∪ _
          exact Or.inr (by simpa only [hn] using hc)
        simp only [ClockResetSet.elapse, he c hb]
      · simp only [dif_neg hk] at hs ⊢
        exact hs.2

end STLTableau.Section3
