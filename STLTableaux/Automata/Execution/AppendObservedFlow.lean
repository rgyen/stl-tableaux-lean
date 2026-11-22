import STLTableaux.Automata.Execution.HybridAutomata

namespace STLTableau.HybridAutomaton.Execution
variable {M L V : Type*} {H : HybridAutomaton M L V} {σ : FiniteSignal V}

/-- Append a positive flow after a nonempty final jump block. The new
signal can differ outside the retained prefix. -/
theorem append_observed_flow (e : H.Execution σ) (ρ : FiniteSignal V)
    (T : ℝ) (hT : T = e.boundary ⟨e.count,by omega⟩)
    (d : NNReal) (hd : 0 < d) (hhor : T+d ≤ ρ.horizon) (b : H.State)
    (γ : Set.Icc (0 : ℝ) d → V → ℝ) (hc : H.ContinuousStep e.finalState b d γ)
    (hj : Relation.TransGen H.DiscreteStep (e.finish ⟨e.count-1,by have := e.nonempty; omega⟩) e.finalState)
    (old : ∀ (t : ρ.Time) (u : σ.Time), t.val = u.val → t.val < T → ρ.value t = σ.value u)
    (seg : ∀ (t : ρ.Time) (hl : T ≤ t.val) (hr : t.val ≤ T+d),
      ρ.value t = γ ⟨t.val-T,sub_nonneg.mpr hl,by linarith⟩) :
    ∃ (e' : H.Execution ρ) (i : Fin e'.count), e'.start i = e.finalState ∧
      e'.boundary i.castSucc = T ∧ e'.boundary i.succ = T+d := by
  let bounds (j : Fin (e.count+2)) := if hj : j.val ≤ e.count then
    e.boundary ⟨j.val,by omega⟩ else T+d
  have b_old (j : Fin (e.count+2)) (hj : j.val ≤ e.count) :
      bounds j = e.boundary ⟨j.val,by omega⟩ := dif_pos hj
  have b_end (j : Fin (e.count+2)) (hj : j.val = e.count+1) :
      bounds j = T+d := dif_neg (by omega)
  have increasing : StrictMono bounds := by
    intro i j hij
    have hv : i.val < j.val := hij
    have hi : i.val ≤ e.count := by have := j.isLt; omega
    rw [b_old i hi]
    by_cases h : j.val ≤ e.count
    · rw [b_old j h]
      exact e.increasing hv
    · rw [b_end j (by have := j.isLt; omega),hT]
      exact (e.increasing.monotone (show (⟨i.val,by omega⟩ : Fin (e.count+1)) ≤
        ⟨e.count,by omega⟩ from hi)).trans_lt (lt_add_of_pos_right _ hd)
  let st (i : Fin (e.count+1)) := if hi : i.val < e.count then e.start ⟨i.val,hi⟩ else e.finalState
  let en (i : Fin (e.count+1)) := if hi : i.val < e.count then e.finish ⟨i.val,hi⟩ else b
  let dur (i : Fin (e.count+1)) := if hi : i.val < e.count then e.duration ⟨i.val,hi⟩ else d
  let curves (i : Fin (e.count+1)) (t : Set.Icc (0 : ℝ) (dur i)) : V → ℝ :=
    if hi : i.val < e.count then
      e.curve ⟨i.val,hi⟩ ⟨t.val,t.property.1,by simpa [dur,hi] using t.property.2⟩
    else γ ⟨t.val,t.property.1,by simpa [dur,hi] using t.property.2⟩
  have dr (i : Fin (e.count+1)) : (dur i : ℝ) = bounds i.succ - bounds i.castSucc := by
    by_cases hi : i.val < e.count
    · simpa [dur,bounds,hi,show i.val+1 ≤ e.count by omega,hi.le] using e.duration_eq ⟨i.val,hi⟩
    · have he : i.val = e.count := by have := i.isLt; omega
      rw [b_end _ (show i.val+1 = e.count+1 by omega), b_old _ (show i.val ≤ e.count by omega)]
      have hh : (⟨i.val,by omega⟩ : Fin (e.count+1)) = ⟨e.count,by omega⟩ := Fin.ext he
      simp [dur,hi,hh,hT]
  have cont (i : Fin (e.count+1)) : H.ContinuousStep (st i) (en i) (dur i) (curves i) := by
    by_cases hi : i.val < e.count
    · simpa [HybridAutomaton.ContinuousStep,st,en,dur,curves,hi] using e.continuousStep ⟨i.val,hi⟩
    · simpa [HybridAutomaton.ContinuousStep,st,en,dur,curves,hi] using hc
  let out : H.Execution ρ := {
    count := e.count+1, nonempty := by omega
    initialState := e.initialState, initial_mem := e.initial_mem
    initial_signal_eq := by
      have positive : 0 < T := by
        rw [hT, ← e.first_zero]
        exact e.increasing (by change 0 < e.count; exact e.nonempty)
      exact (old ⟨0, le_rfl, ρ.horizon_pos⟩ ⟨0, le_rfl, σ.horizon_pos⟩ rfl positive).trans
        e.initial_signal_eq
    start := st, finish := en, boundary := bounds
    first_zero := by simpa [bounds] using e.first_zero
    increasing := increasing
    last_le_horizon := by rw [b_end _ rfl]; exact hhor
    duration := dur, duration_eq := dr
    curve := curves, continuousStep := cont
    initialSteps := by simpa [st,e.nonempty] using e.initialSteps
    discreteSteps := by
      intro i hn
      have hi : i.val < e.count := by omega
      by_cases hn' : i.val+1 < e.count
      · simpa [en,st,hi,hn'] using e.discreteSteps ⟨i.val,hi⟩ hn'
      · have he : (⟨i.val,hi⟩ : Fin e.count) = ⟨e.count-1,by omega⟩ := by
          apply Fin.ext; change i.val = e.count-1; omega
        simpa [en,st,hi,hn',he] using hj
    finalState := b
    finalSteps := by simpa [en] using (Relation.ReflTransGen.refl : Relation.ReflTransGen H.DiscreteStep b b)
    final_signal_eq := by
      intro t ht
      rw [b_end _ rfl] at ht
      have hl : T ≤ t.val := by rw [ht]; exact le_add_of_nonneg_right d.coe_nonneg
      rw [seg t hl ht.le]
      exact (congrArg γ (Subtype.ext (show t.val - T = d by linarith))).trans hc.2.2.1
    signal_eq := by
      intro i t ht positive
      by_cases hi : i.val < e.count
      · have hl := b_old i.castSucc (show i.val ≤ e.count by omega)
        have hr := b_old i.succ (show i.val+1 ≤ e.count by omega)
        have hc' := (e.increasing.monotone (show (⟨i.val+1,by omega⟩ : Fin (e.count+1)) ≤
          ⟨e.count,by omega⟩ from by change i.val+1 ≤ e.count; omega))
        have htT := (ht.2.trans_eq hr).trans_le (hc'.trans_eq hT.symm)
        let u : σ.Time := ⟨t.val,t.property.1,htT.trans_le (hT ▸ e.last_le_horizon)⟩
        rw [old t u rfl htT,e.signal_eq ⟨i.val,hi⟩ u ⟨hl ▸ ht.1,hr ▸ ht.2⟩ positive]
        simp only [curves,dif_pos hi]
        apply congrArg (e.curve _)
        exact Subtype.ext (congrArg (t.val - ·) hl.symm)
      · have he : i.val = e.count := by have := i.isLt; omega
        have hl : bounds i.castSucc = T := by
          rw [b_old _ (show i.val ≤ e.count by omega),hT]
          exact congrArg e.boundary (Fin.ext he)
        have hr := b_end i.succ (show i.val+1 = e.count+1 by omega)
        rw [seg t (hl ▸ ht.1) ((ht.2.trans_eq hr).le)]
        simp only [curves,dif_neg hi]
        exact congrArg γ (Subtype.ext (congrArg (t.val - ·) hl.symm)) }
  let i : Fin out.count := ⟨e.count,by change e.count < e.count+1; omega⟩
  refine ⟨out,i,?_,?_,?_⟩
  · change st _ = _
    simp [st,i]
  · change bounds _ = _
    rw [b_old _ (show e.count ≤ e.count from le_rfl)]
    exact hT.symm
  · exact b_end _ rfl

end STLTableau.HybridAutomaton.Execution
