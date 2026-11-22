import STLTableaux.Closure.Normalization.FaithfulUnion

namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace StateForm

theorem union_holds_of_agree (S T : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β γ : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hS : ∀ c ∈ S.localClocks, S.resets.apply α c = (S.union T).resets.apply γ c)
    (hT : ∀ c ∈ T.localClocks, T.resets.apply β c = (S.union T).resets.apply γ c)
    (hgS : ∀ c ∈ S.guardClocks, α c = γ c)
    (hgT : ∀ c ∈ T.guardClocks, β c = γ c)
    (hs : S.holds σ P α k) (ht : T.holds σ P β k) : (S.union T).holds σ P γ k := by
  constructor
  · intro g hg
    rcases hg with hg | hg
    · simpa only [Guard.holds,← hgS g.clock ⟨g,hg,rfl⟩] using hs.1 g hg
    · simpa only [Guard.holds,← hgT g.clock ⟨g,hg,rfl⟩] using ht.1 g hg
  · intro l hl
    rcases hl with hl | hl
    · exact (l.holds_congr_of_agree σ P _ _ k (fun c hc => hS c ⟨l,hl,hc⟩)).1 (hs.2 l hl)
    · exact (l.holds_congr_of_agree σ P _ _ k (fun c hc => hT c ⟨l,hl,hc⟩)).1 (ht.2 l hl)

theorem union_invariant_of_agree (S T : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α β γ : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hS : ∀ c ∈ S.localClocks, S.resets.apply α c = (S.union T).resets.apply γ c)
    (hT : ∀ c ∈ T.localClocks, T.resets.apply β c = (S.union T).resets.apply γ c)
    (hs : S.EvaluatedInvariant σ P α k) (ht : T.EvaluatedInvariant σ P β k) :
    (S.union T).EvaluatedInvariant σ P γ k := by
  intro l hl
  rcases hl with hl | hl
  · exact (l.evaluatedInvariant_congr σ P _ _ k (fun c hc => hS c ⟨l,hl,hc⟩)).1 (hs l hl)
  · exact (l.evaluatedInvariant_congr σ P _ _ k (fun c hc => hT c ⟨l,hl,hc⟩)).1 (ht l hl)
end StateForm
namespace TransitionForm
private theorem outer_agree {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (α : ClockValuation Clock) :
    ∀ c ∈ Φ.bodyFreeClocks, Φ.current.resets.apply α c = Ψ.current.resets.apply α c :=
  reset_apply_agree h.current.resets α α Φ.bodyFreeClocks h.outerFresh (fun _ _ => rfl)

private theorem current_agree {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (α : ClockValuation Clock) :
    ∀ c ∈ Φ.current.localClocks, Φ.current.resets.apply α c = Ψ.current.resets.apply α c :=
  fun c hc => outer_agree h α c (Or.inl hc)

private theorem next_incoming_agree {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) {N : StateForm Clock Var} (hn : Φ.nextPart = some N)
    (α : ClockValuation Clock) (δ : NNReal) :
    ∀ c ∈ N.freeClocks,
      ClockResetSet.elapse (Φ.current.resets.apply α) δ c =
      ClockResetSet.elapse (Ψ.current.resets.apply α) δ c := by
  intro c hc
  exact congrArg (fun x => x+δ) (outer_agree h α c (Or.inr (by simpa only [hn] using hc)))

theorem UnionCompatible.holds {Φ Ψ : TransitionForm Clock Var} (h : Φ.UnionCompatible Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.union Ψ).holds σ P α k ↔ Φ.holds σ P α k ∧ Ψ.holds σ P α k := by
  constructor
  · intro hs; exact ⟨h.left.sound σ P α k hs,h.right.sound σ P α k hs⟩
  · rintro ⟨hf,hg⟩
    refine ⟨StateForm.union_holds_of_agree _ _ σ P α α α k
      (current_agree h.left α) (current_agree h.right α)
      (fun _ _ => rfl) (fun _ _ => rfl) hf.1 hg.1,?_⟩
    cases hn : Φ.nextPart with
    | none =>
        cases hm : Ψ.nextPart with
        | none => simp [union,unionNext,hn,hm]
        | some M =>
            simp only [TransitionForm.holds,hm] at hg
            simp only [union,unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hg ⊢
              exact (M.holds_congr_of_agree σ P _ _ _ (next_incoming_agree h.right hm α _)).1 hg.2
            · simpa only [dif_neg hk] using hg.2
    | some N =>
        simp only [TransitionForm.holds,hn] at hf
        cases hm : Ψ.nextPart with
        | none =>
            simp only [union,unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hf ⊢
              exact (N.holds_congr_of_agree σ P _ _ _ (next_incoming_agree h.left hn α _)).1 hf.2
            · simpa only [dif_neg hk] using hf.2
        | some M =>
            simp only [TransitionForm.holds,hm] at hg
            simp only [union,unionNext,hn,hm]
            by_cases hk : k.1 < P.size
            · simp only [dif_pos hk] at hf hg ⊢
              obtain ⟨K,hK,hNK,hfreshN⟩ := h.left.next N hn
              obtain ⟨L,hL,hML,hfreshM⟩ := h.right.next M hm
              have hKN : K = N.union M := by simpa [union,unionNext,hn,hm] using hK.symm
              have hLM : L = N.union M := by simpa [union,unionNext,hn,hm] using hL.symm
              subst K; subst L
              apply StateForm.union_holds_of_agree _ _ σ P _ _ _ _ _ _ _ _ hf.2 hg.2
              · exact reset_apply_agree hNK.resets _ _ N.localClocks hfreshN
                  (fun c hc => next_incoming_agree h.left hn α _ c (Or.inr hc))
              · exact reset_apply_agree hML.resets _ _ M.localClocks hfreshM
                  (fun c hc => next_incoming_agree h.right hm α _ c (Or.inr hc))
              · exact fun c hc => next_incoming_agree h.left hn α _ c (Or.inl hc)
              · exact fun c hc => next_incoming_agree h.right hm α _ c (Or.inl hc)
            · simpa only [dif_neg hk] using hf.2
theorem UnionCompatible.evaluatedInvariant {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.UnionCompatible Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hf : Φ.EvaluatedInvariant σ P α k) (hg : Ψ.EvaluatedInvariant σ P α k) :
    (Φ.union Ψ).EvaluatedInvariant σ P α k := by
  refine ⟨StateForm.union_invariant_of_agree _ _ σ P α α α k
    (current_agree h.left α) (current_agree h.right α) hf.1 hg.1,?_⟩
  intro K hK hk
  cases hn : Φ.nextPart with
  | none =>
      cases hm : Ψ.nextPart with
      | none => simp [union,unionNext,hn,hm] at hK
      | some M =>
          have he : K = M := by simpa [union,unionNext,hn,hm] using hK.symm
          subst K
          exact (M.evaluatedInvariant_congr σ P _ _ _
            (next_incoming_agree h.right hm α _)).1 (hg.2 M hm hk)
  | some N =>
      cases hm : Ψ.nextPart with
      | none =>
          have he : K = N := by simpa [union,unionNext,hn,hm] using hK.symm
          subst K
          exact (N.evaluatedInvariant_congr σ P _ _ _
            (next_incoming_agree h.left hn α _)).1 (hf.2 N hn hk)
      | some M =>
          have he : K = N.union M := by simpa [union,unionNext,hn,hm] using hK.symm
          subst K
          obtain ⟨K,hKN,hNK,hfreshN⟩ := h.left.next N hn
          obtain ⟨L,hLM,hML,hfreshM⟩ := h.right.next M hm
          have hKN' : K = N.union M := by simpa [union,unionNext,hn,hm] using hKN.symm
          have hLM' : L = N.union M := by simpa [union,unionNext,hn,hm] using hLM.symm
          subst K; subst L
          apply StateForm.union_invariant_of_agree _ _ σ P _ _ _ _ _ _ (hf.2 N hn hk) (hg.2 M hm hk)
          · exact reset_apply_agree hNK.resets _ _ N.localClocks hfreshN
              (fun c hc => next_incoming_agree h.left hn α _ c (Or.inr hc))
          · exact reset_apply_agree hML.resets _ _ M.localClocks hfreshM
              (fun c hc => next_incoming_agree h.right hm α _ c (Or.inr hc))
end TransitionForm
end STLTableau.Section3
