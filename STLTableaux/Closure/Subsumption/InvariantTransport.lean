import STLTableaux.Semantics.Invariants.EvaluatedInvariant
import STLTableaux.Closure.Normalization.NormalizedStability

/-! Removing judgments by genuine no-capture subsumption preserves the full
invariant at the smaller form's own reset valuations. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

theorem Local.evaluatedInvariant_congr_of_agree (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ l.freeClocks, α c = β c) :
    l.EvaluatedInvariant σ P α k ↔ l.EvaluatedInvariant σ P β k :=
  Judgement.evaluatedInvariant_congr_of_agree σ P l.toJudgement α β k h

theorem StateForm.evaluatedInvariant_of_included
    {S T : StateForm Clock Var} (h : ComponentsIncluded S T)
    (hfresh : Disjoint T.resets.clocks (S.localClocks \ S.resets.clocks))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ S.freeClocks, α c = β c)
    (hi : T.EvaluatedInvariant σ P β k) : S.EvaluatedInvariant σ P α k := by
  have he := reset_apply_agree h.resets α β S.localClocks hfresh
    (fun c hc => hagree c (Or.inr hc))
  intro l hl
  exact (l.evaluatedInvariant_congr_of_agree σ P _ _ k
    (fun c hc => he c ⟨l, hl, hc⟩)).2 (hi l (h.locals hl))

theorem SyntacticallySubsumed.evaluatedInvariant {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hi : Ψ.EvaluatedInvariant σ P α k) : Φ.EvaluatedInvariant σ P α k := by
  have hcurFresh : Disjoint Ψ.current.resets.clocks
      (Φ.current.localClocks \ Φ.current.resets.clocks) :=
    Set.disjoint_left.2 (fun c hc hd => Set.disjoint_left.1 h.outerFresh hc
      ⟨Or.inl hd.1, hd.2⟩)
  constructor
  · exact StateForm.evaluatedInvariant_of_included h.current hcurFresh σ P α α k
      (fun _ _ => rfl) hi.1
  · intro N hN hk
    obtain ⟨M, hM, hinc, hfresh⟩ := h.next N hN
    have hn : N.freeClocks ⊆ Φ.bodyFreeClocks := by
      intro c hc
      exact Or.inr (by simpa [TransitionForm.bodyFreeClocks, hN] using hc)
    have he := reset_apply_agree h.current.resets α α Φ.bodyFreeClocks
      h.outerFresh (fun _ _ => rfl)
    exact StateForm.evaluatedInvariant_of_included hinc hfresh σ P _ _ _
      (fun c hc => by simp only [ClockResetSet.elapse, he c (hn hc)]) (hi.2 M hM hk)

theorem StateForm.underlyingStable_of_included
    {S T : StateForm Clock Var} (h : ComponentsIncluded S T)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hst : T.UnderlyingStable σ P) : S.UnderlyingStable σ P := by
  rintro φ ⟨p, hp, rfl⟩
  exact hst _ ⟨p, h.locals hp, rfl⟩

theorem SyntacticallySubsumed.underlyingStable {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hst : Ψ.UnderlyingStable σ P) :
    Φ.UnderlyingStable σ P := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · rcases hφ with ⟨p, hp, rfl⟩
    exact hst _ (Or.inl ⟨p, h.current.locals hp, rfl⟩)
  · cases hN : Φ.nextPart with
    | none => simp [TransitionForm.underlyingFormulas, hN] at hφ
    | some N =>
        obtain ⟨M, hM, hinc, _⟩ := h.next N hN
        have hφN : φ ∈ N.underlyingFormulas := by
          simpa [TransitionForm.underlyingFormulas, hN] using hφ
        rcases hφN with ⟨p, hp, rfl⟩
        apply hst _
        right
        simpa [TransitionForm.underlyingFormulas, hM] using
          (show p.formula ∈ M.underlyingFormulas from ⟨p, hinc.locals hp, rfl⟩)

end STLTableau.Section3
