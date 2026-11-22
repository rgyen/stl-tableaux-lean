import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

namespace STLTableau.IntervalPartition
variable {L R τ : ℝ}

/-- Append precisely the unexecuted suffix; old singleton visits stay singleton. -/
def cutSuffixPiece (P : IntervalPartition (Set.Ico L R)) (τ : ℝ)
    (i : Fin (P.size + 1)) : MarkedInterval :=
  if hi : i.val < P.size then P.interval ⟨i.val, hi⟩ else ⟨R, τ, ●, ○⟩

private theorem old_before_cut (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size)
    {x : ℝ} (hx : x ∈ (P.interval i).carrier) : x ∈ Set.Ico L R := by
  rw [← P.covers]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

def appendCutSuffix (P : IntervalPartition (Set.Ico L R)) (hl : L ≤ R)
    (hr : R < τ) (hend : ∀ i, (P.interval i).right ≤ R) :
    IntervalPartition (Set.Ico L τ) where
  size := P.size + 1
  interval := cutSuffixPiece P τ
  nonempty := by
    intro i
    unfold cutSuffixPiece
    split
    · exact P.nonempty _
    · simpa [MarkedInterval.carrier_eq] using Set.nonempty_Ico.mpr hr
  pairwiseDisjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    unfold cutSuffixPiece at hx hy
    split_ifs at hx hy with hi hj
    · exact Set.disjoint_left.mp (P.pairwiseDisjoint (show
        (⟨i.val, hi⟩ : Fin P.size) ≠ ⟨j.val, hj⟩ from
        fun e => hij (Fin.ext (congrArg (fun k : Fin P.size => k.val) e)))) hx hy
    · have h := (old_before_cut P _ hx).2
      simp only [MarkedInterval.carrier_eq, Set.mem_Ico] at hy
      exact (not_lt_of_ge hy.1) h
    · have h := (old_before_cut P _ hy).2
      simp only [MarkedInterval.carrier_eq, Set.mem_Ico] at hx
      exact (not_lt_of_ge hx.1) h
    · exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
  covers := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      unfold cutSuffixPiece at hx
      split at hx
      · have hm := old_before_cut P _ hx
        exact ⟨hm.1, hm.2.trans hr⟩
      · simp only [MarkedInterval.carrier_eq, Set.mem_Ico] at hx
        exact ⟨hl.trans hx.1, hx.2⟩
    · intro hx
      by_cases hb : x < R
      · have hm : x ∈ Set.Ico L R := ⟨hx.1, hb⟩
        rw [← P.covers, Set.mem_iUnion] at hm
        obtain ⟨i, hi⟩ := hm
        exact ⟨i.castSucc, by simpa [cutSuffixPiece, i.isLt] using hi⟩
      · refine ⟨Fin.last P.size, ?_⟩
        simpa [cutSuffixPiece, MarkedInterval.carrier_eq] using And.intro (le_of_not_gt hb) hx.2
  ordered := by
    intro i j hij
    have hv : i.val < j.val := hij
    unfold cutSuffixPiece
    split_ifs with hi hj
    · exact P.ordered hv
    · exact hend _
    · omega
    · have := j.isLt
      omega

@[simp] theorem appendCutSuffix_old (P : IntervalPartition (Set.Ico L R))
    (hl : L ≤ R) (hr : R < τ) (hend : ∀ i, (P.interval i).right ≤ R) (i : Fin P.size) :
    (P.appendCutSuffix hl hr hend).interval i.castSucc = P.interval i := by
  simp [appendCutSuffix, cutSuffixPiece, i.isLt]

@[simp] theorem appendCutSuffix_last (P : IntervalPartition (Set.Ico L R))
    (hl : L ≤ R) (hr : R < τ) (hend : ∀ i, (P.interval i).right ≤ R) :
    (P.appendCutSuffix hl hr hend).interval (Fin.last P.size) = ⟨R, τ, ●, ○⟩ := by
  simp [appendCutSuffix, cutSuffixPiece]

/-- Complete the visited boundary data at either kind of cut. The indexed
pieces below are exactly the original marked pieces, even at repeated times. -/
theorem completeVisitBounds {n : ℕ} (b : Fin (n+1) → ℝ) (hb : Monotone b)
    (m : Fin (n+1) → Marker) (hz : SingletonCompatible b m)
    (hf : m 0 = ●) (he : m (Fin.last n) = ●) (hcut : b (Fin.last n) ≤ τ) :
    ∃ (Q : IntervalPartition (Set.Ico (b 0) τ)) (hn : n ≤ Q.size),
      (∀ i : Fin n, Q.interval ⟨i.val, i.isLt.trans_le hn⟩ = markedBoundaryPiece b m i) ∧
      (b (Fin.last n) = τ → Q.size = n) ∧
      (b (Fin.last n) < τ → ∃ hj : n < Q.size, Q.size = n+1 ∧
        Q.interval ⟨n,hj⟩ = ⟨b (Fin.last n), τ, ●, ○⟩) := by
  let P := ofSingletonBoundaries b hb m hz hf he
  rcases lt_or_eq_of_le hcut with hlt | rfl
  · have hend : ∀ i, (P.interval i).right ≤ b (Fin.last n) := by
      intro i
      exact hb (show (⟨i.val+1, by have := i.isLt; change i.val < n at this; omega⟩ :
        Fin (n+1)) ≤ Fin.last n from Fin.le_last _)
    have hl : b 0 ≤ b (Fin.last n) := hb (Fin.zero_le _)
    refine ⟨P.appendCutSuffix hl hlt hend, Nat.le_succ n, ?_, ?_, ?_⟩
    · intro i
      exact appendCutSuffix_old P hl hlt hend i
    · exact fun h => (hlt.ne h).elim
    · intro _
      exact ⟨Nat.lt_succ_self n, rfl, appendCutSuffix_last P hl hlt hend⟩
  · exact ⟨P, le_rfl, fun _ => rfl, fun _ => rfl, fun h => (lt_irrefl _ h).elim⟩

end STLTableau.IntervalPartition
