import STLTableaux.Semantics.Partitions.Partition

/-! The left endpoint belongs to the first piece of a partition of [L,R).
Closedness is derived from coverage and ordering, not an extra assumption. -/
namespace STLTableau.IntervalPartition

theorem size_pos_of_domain_nonempty {D : Set ℝ} (P : IntervalPartition D)
    (hD : D.Nonempty) : 0 < P.size := by
  obtain ⟨x, hx⟩ := hD
  rw [← P.covers] at hx
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact Nat.zero_lt_of_lt i.isLt

theorem left_endpoint_mem_first {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (hsize : 0 < P.size) (hLR : L < R) :
    L ∈ (P.interval ⟨0, hsize⟩).carrier := by
  have hcover : L ∈ ⋃ j, (P.interval j).carrier := by
    rw [P.covers]
    exact ⟨le_rfl, hLR⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcover
  by_cases hz : j.val = 0
  · have he : j = ⟨0, hsize⟩ := Fin.ext hz
    simpa only [he] using hj
  · obtain ⟨x, hx⟩ := P.nonempty ⟨0, hsize⟩
    have hxD : x ∈ Set.Ico L R := by
      rw [← P.covers]
      exact Set.mem_iUnion.mpr ⟨⟨0, hsize⟩, hx⟩
    have horder := P.ordered (show (⟨0, hsize⟩ : Fin P.size) < j by
      change 0 < j.val; omega)
    have hxL : x ≤ L := (MarkedInterval.le_right_of_mem hx).trans
      (horder.trans (MarkedInterval.left_le_of_mem hj))
    have he : x = L := le_antisymm hxL hxD.1
    simpa only [he] using hx

theorem first_left_eq_domain_left {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (hsize : 0 < P.size) (hLR : L < R) :
    (P.interval ⟨0, hsize⟩).left = L := by
  have hm := P.left_endpoint_mem_first hsize hLR
  apply le_antisymm (MarkedInterval.left_le_of_mem hm)
  by_contra hn
  have hlt : (P.interval ⟨0, hsize⟩).left < L := lt_of_not_ge hn
  obtain ⟨x, hlx, hxL⟩ := exists_between hlt
  have hxr : x < (P.interval ⟨0, hsize⟩).right :=
    hxL.trans_le (MarkedInterval.le_right_of_mem hm)
  have hx : x ∈ (P.interval ⟨0, hsize⟩).carrier := ⟨Or.inl hlx, Or.inl hxr⟩
  have hxD : x ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨⟨0, hsize⟩, hx⟩
  exact (not_lt_of_ge hxD.1) hxL

/-- Both an initial singleton and an initial positive-length interval must
have a closed left marker. No tableau or automaton assumptions are involved. -/
theorem first_leftBoundary_closed {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (hsize : 0 < P.size) (hLR : L < R) :
    (P.interval ⟨0, hsize⟩).leftBoundary = ● := by
  have hm := (MarkedInterval.mem_iff.mp (P.left_endpoint_mem_first hsize hLR)).1
  rw [P.first_left_eq_domain_left hsize hLR] at hm
  have hi : (P.interval ⟨0, hsize⟩).leftBoundary.Includes := by simpa using hm
  cases he : (P.interval ⟨0, hsize⟩).leftBoundary <;>
    simp_all [Marker.Includes]

end STLTableau.IntervalPartition
