import STLTableaux.Tableau.Construction.Tableau

/-! Trace satisfaction is preserved between partitions with equal intervals
at all visited positions on a nonterminal prefix. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}

theorem local_holds_of_same_interval (σ : FiniteSignal Var)
    (P Q : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (j : STLTableau.Judgement.Position Q)
    (hk : k.val < P.size) (hj : j.val < Q.size)
    (he : P.interval ⟨k.val, hk⟩ = Q.interval ⟨j.val, hj⟩)
    (l : Local Clock Var) : l.holds σ P α k ↔ l.holds σ Q α j := by
  cases l with
  | terminal =>
    simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds,
      ne_of_lt hk, ne_of_lt hj]
  | marker m =>
    simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds,
      dif_pos hk, dif_pos hj, he]
  | predicate p =>
    simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds,
      dif_pos hk, dif_pos hj, he]

theorem Trace.holdsWith_prefix_congr
    (labels : Section3.StateForm Clock Var → Set (Local Clock Var))
    (σ : FiniteSignal Var) (P Q : IntervalPartition σ.domain)
    (t : Trace Clock Var) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (j : STLTableau.Judgement.Position Q)
    (hk : k.val + t.length ≤ P.size) (hj : j.val + t.length ≤ Q.size)
    (he : ∀ r (hr : r < t.length),
      P.interval ⟨k.val + r, by omega⟩ = Q.interval ⟨j.val + r, by omega⟩) :
    t.holdsWith labels σ P α k ↔ t.holdsWith labels σ Q α j := by
  induction t generalizing α k j with
  | last S =>
    have hk' : k.val < P.size := by simp only [Trace.length] at hk; omega
    have hj' : j.val < Q.size := by simp only [Trace.length] at hj; omega
    have he' : P.interval ⟨k.val, hk'⟩ = Q.interval ⟨j.val, hj'⟩ := by
      simpa only [Nat.add_zero] using he 0 (by simp [Trace.length])
    simp only [Trace.holdsWith]
    apply and_congr Iff.rfl
    exact forall_congr' fun l => forall_congr' fun _ =>
      local_holds_of_same_interval σ P Q _ k j hk' hj' he' l
  | step S t ih =>
    have hlen := t.length_pos
    have hk' : k.val < P.size := by simp only [Trace.length] at hk; omega
    have hj' : j.val < Q.size := by simp only [Trace.length] at hj; omega
    have he' : P.interval ⟨k.val, hk'⟩ = Q.interval ⟨j.val, hj'⟩ := by
      simpa only [Nat.add_zero] using he 0 (by simp [Trace.length])
    have hd : STLTableau.Judgement.duration P ⟨k.val, hk'⟩ =
        STLTableau.Judgement.duration Q ⟨j.val, hj'⟩ := by
      simp only [STLTableau.Judgement.duration, he']
    simp only [Trace.holdsWith, dif_pos hk', dif_pos hj']
    apply and_congr
    · apply and_congr Iff.rfl
      exact forall_congr' fun l => forall_congr' fun _ =>
        local_holds_of_same_interval σ P Q _ k j hk' hj' he' l
    · rw [hd]
      have hkNext : k.val + 1 + t.length ≤ P.size := by
        simp only [Trace.length] at hk
        omega
      have hjNext : j.val + 1 + t.length ≤ Q.size := by
        simp only [Trace.length] at hj
        omega
      exact ih _ _ _ hkNext hjNext fun r hr => by
        simpa only [Nat.add_assoc, Nat.add_comm 1 r] using
          he (r + 1) (by simp only [Trace.length]; omega)

theorem Trace.holds_prefix_congr
    (σ : FiniteSignal Var) (P Q : IntervalPartition σ.domain)
    (t : Trace Clock Var) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (j : STLTableau.Judgement.Position Q)
    (hk : k.val + t.length ≤ P.size) (hj : j.val + t.length ≤ Q.size)
    (he : ∀ r (hr : r < t.length),
      P.interval ⟨k.val + r, by omega⟩ = Q.interval ⟨j.val + r, by omega⟩) :
    t.holds σ P α k ↔ t.holds σ Q α j :=
  t.holdsWith_prefix_congr Section3.StateForm.locals σ P Q α k j hk hj he

end STLTableau.Section4
