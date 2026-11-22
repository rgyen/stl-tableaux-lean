import STLTableaux.Semantics.Partitions.Partition

/-! Append a stopping point and an open suffix without refining any old piece. -/
namespace STLTableau.IntervalPartition
variable {L R S : ℝ}

def pointSuffixPiece (P : IntervalPartition (Set.Ico L R)) (S : ℝ)
    (i : Fin (P.size + 2)) : MarkedInterval :=
  if hi : i.val < P.size then P.interval ⟨i.val, hi⟩
  else if i.val = P.size then ⟨R, R, ●, ●⟩ else ⟨R, S, ○, ○⟩

private theorem old_mem (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) {x : ℝ} (hx : x ∈ (P.interval i).carrier) : L ≤ x ∧ x < R := by
  change x ∈ Set.Ico L R
  rw [← P.covers]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

def appendPointSuffix (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R) :
    IntervalPartition (Set.Ico L S) where
  size := P.size + 2
  interval := pointSuffixPiece P S
  nonempty := by
    intro i
    unfold pointSuffixPiece
    split_ifs with hi he
    · exact P.nonempty _
    · simp [MarkedInterval.carrier_eq]
    · simpa [MarkedInterval.carrier_eq] using Set.nonempty_Ioo.mpr hRS
  pairwiseDisjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    unfold pointSuffixPiece at hx hy
    split_ifs at hx hy with hi he hj hf
    · apply Set.disjoint_left.mp (P.pairwiseDisjoint
        (i := ⟨i.val, by assumption⟩) (j := ⟨j.val, by assumption⟩) ?_) hx hy
      intro heq
      exact hij (Fin.ext (congrArg (fun z : Fin P.size => z.val) heq))
    · have := old_mem P _ hx
      simp only [MarkedInterval.carrier_eq, Set.mem_Icc] at hy
      linarith [hy.1]
    · have := old_mem P _ hx
      simp only [MarkedInterval.carrier_eq, Set.mem_Ioo] at hy
      linarith [hy.1]
    · have := old_mem P _ hy
      simp only [MarkedInterval.carrier_eq, Set.mem_Icc] at hx
      linarith [hx.1]
    · exact hij (Fin.ext (by omega))
    · simp only [MarkedInterval.carrier_eq, Set.mem_Icc, Set.mem_Ioo] at hx hy
      linarith [hx.2, hy.1]
    · have := old_mem P _ hy
      simp only [MarkedInterval.carrier_eq, Set.mem_Ioo] at hx
      linarith [hx.1]
    · simp only [MarkedInterval.carrier_eq, Set.mem_Icc, Set.mem_Ioo] at hx hy
      linarith [hx.1, hy.2]
    · exact hij (Fin.ext (by have := i.isLt; have := j.isLt; omega))
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      unfold pointSuffixPiece at hx
      split_ifs at hx with hi he
      · have hh := old_mem P _ hx
        exact ⟨hh.1, hh.2.trans hRS⟩
      · simp only [MarkedInterval.carrier_eq, Set.mem_Icc] at hx
        exact ⟨hLR.trans hx.1, hx.2.trans_lt hRS⟩
      · simp only [MarkedInterval.carrier_eq, Set.mem_Ioo] at hx
        exact ⟨hLR.trans hx.1.le, hx.2⟩
    · intro hx
      by_cases hl : x < R
      · have hm : x ∈ Set.Ico L R := ⟨hx.1, hl⟩
        rw [← P.covers, Set.mem_iUnion] at hm
        obtain ⟨i, hi⟩ := hm
        exact ⟨⟨i.val, by omega⟩, by simpa [pointSuffixPiece, i.isLt] using hi⟩
      · by_cases he : x = R
        · refine ⟨⟨P.size, by omega⟩, ?_⟩
          simp [pointSuffixPiece, he, MarkedInterval.carrier_eq]
        · refine ⟨⟨P.size + 1, by omega⟩, ?_⟩
          have hr : R < x := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
          simpa [pointSuffixPiece, MarkedInterval.carrier_eq] using And.intro hr hx.2
  ordered := by
    intro i j hij
    have hv : i.val < j.val := hij
    unfold pointSuffixPiece
    split_ifs with hi hj he hf
    · exact P.ordered hv
    · exact hright _
    · exact hright _
    · omega
    · exact le_rfl
    · exact le_rfl
    · omega
    · omega
    · have := i.isLt; have := j.isLt; omega

@[simp] theorem appendPointSuffix_old (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R)
    (i : Fin P.size) :
    (P.appendPointSuffix hLR hRS hright).interval ⟨i.val, by change i.val < P.size + 2; omega⟩ =
      P.interval i := by simp [appendPointSuffix, pointSuffixPiece, i.isLt]

@[simp] theorem appendPointSuffix_point (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R) :
    (P.appendPointSuffix hLR hRS hright).interval
      ⟨P.size, by change P.size < P.size + 2; omega⟩ = ⟨R, R, ●, ●⟩ := by
  simp [appendPointSuffix, pointSuffixPiece]

@[simp] theorem appendPointSuffix_suffix (P : IntervalPartition (Set.Ico L R))
    (hLR : L ≤ R) (hRS : R < S) (hright : ∀ i, (P.interval i).right ≤ R) :
    (P.appendPointSuffix hLR hRS hright).interval
      ⟨P.size + 1, by change P.size + 1 < P.size + 2; omega⟩ = ⟨R, S, ○, ○⟩ := by
  simp [appendPointSuffix, pointSuffixPiece]

end STLTableau.IntervalPartition
