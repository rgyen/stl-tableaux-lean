import STLTableaux.Semantics.Partitions.PartitionFirstBoundary
import STLTableaux.Automata.Recognition.ExecutionPathTiming

/-! Numerical boundary alignment from partition coverage and piece durations.
No marker assignment or execution-label satisfaction is assumed. -/
namespace STLTableau.IntervalPartition

/-- No nonempty piece of a partition of a half-open domain extends past
the domain's right endpoint, regardless of its boundary markers. -/
theorem right_le_domain_right {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) : (P.interval i).right ≤ R := by
  obtain ⟨x, hx⟩ := P.nonempty i
  have hxD : x ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  by_contra hn
  obtain ⟨y, hRy, hyr⟩ := exists_between (lt_of_not_ge hn)
  have hy : y ∈ (P.interval i).carrier :=
    ⟨Or.inl ((MarkedInterval.left_le_of_mem hx).trans_lt (hxD.2.trans hRy)), Or.inl hyr⟩
  have hyD : y ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  exact (not_lt_of_ge hRy.le) hyD.2

theorem last_right_eq_domain_right {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) (hlast : i.val + 1 = P.size) : (P.interval i).right = R := by
  obtain ⟨x, hx⟩ := P.nonempty i
  have hxD : x ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  apply le_antisymm
  · exact P.right_le_domain_right i
  · by_contra hn
    obtain ⟨y, hry, hyR⟩ := exists_between (lt_of_not_ge hn)
    have hxy : x < y := (MarkedInterval.le_right_of_mem hx).trans_lt hry
    have hy := P.mem_last_of_le i hlast hx ⟨hxD.1.trans hxy.le, hyR⟩ hxy.le
    exact (not_lt_of_ge (MarkedInterval.le_right_of_mem hy)) hry

theorem residenceBoundary_eq_left {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (ds : List NNReal)
    (hd : ∀ (i : ℕ) (hi : i < P.size) (hi' : i + 1 < ds.length),
      (ds[i] : ℝ) = Judgement.duration P ⟨i, hi⟩)
    (i : ℕ) (hi : i < P.size) (hi' : i < ds.length) :
    STLTableau.Section4.Tableau.residenceBoundary ds i = (P.interval ⟨i, hi⟩).left := by
  induction i with
  | zero =>
    rw [STLTableau.Section4.Tableau.residenceBoundary_zero,
      P.first_left_eq_domain_left hi σ.horizon_pos]
  | succ i ih =>
    have hip : i < P.size := by omega
    have hid : i < ds.length := by omega
    have hprev := ih hip hid
    have hstep := STLTableau.Section4.Tableau.residenceBoundary_step ds i hid
    have htime := hd i hip hi'
    change (ds[i] : ℝ) = (P.interval ⟨i, hip⟩).right - (P.interval ⟨i, hip⟩).left at htime
    have hadj := P.adjacent_right_eq_left ⟨i, hip⟩ hi
    change (P.interval ⟨i, hip⟩).right = (P.interval ⟨i + 1, hi⟩).left at hadj
    linarith

theorem residenceBoundary_eq_horizon {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (ds : List NNReal) (hlen : P.size < ds.length)
    (hd : ∀ (i : ℕ) (hi : i < P.size) (hi' : i + 1 < ds.length),
      (ds[i] : ℝ) = Judgement.duration P ⟨i, hi⟩) :
    STLTableau.Section4.Tableau.residenceBoundary ds P.size = σ.horizon := by
  have hn := P.size_pos_of_domain_nonempty
    (show σ.domain.Nonempty from ⟨0, le_rfl, σ.horizon_pos⟩)
  let i := P.size - 1
  have hi : i < P.size := by dsimp [i]; omega
  have hsucc : i + 1 = P.size := by dsimp [i]; omega
  have hl := P.residenceBoundary_eq_left σ ds hd i hi (by omega)
  have hs := STLTableau.Section4.Tableau.residenceBoundary_step ds i (by omega)
  have ht := hd i hi (by omega)
  change (ds[i] : ℝ) = (P.interval ⟨i, hi⟩).right - (P.interval ⟨i, hi⟩).left at ht
  have hr := P.last_right_eq_domain_right ⟨i, hi⟩ hsucc
  rw [hsucc] at hs
  linarith

/-- All nonfinal right boundaries are fixed by the duration equations.
For the final frame only, its partition piece must end no later than the
observed stopping time; the guard/reset equations do not constrain that dwell. -/
theorem interval_subset_residenceBounds {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (ds : List NNReal)
    (hd : ∀ (i : ℕ) (hi : i < P.size) (hi' : i + 1 < ds.length),
      (ds[i] : ℝ) = Judgement.duration P ⟨i, hi⟩)
    (i : ℕ) (hi : i < P.size) (hi' : i < ds.length)
    (hfinal : i + 1 = ds.length →
      (P.interval ⟨i, hi⟩).right ≤ (ds.sum : ℝ)) :
    (P.interval ⟨i, hi⟩).carrier ⊆ Set.Icc
      (STLTableau.Section4.Tableau.residenceBoundary ds i)
      (STLTableau.Section4.Tableau.residenceBoundary ds (i + 1)) := by
  have hl := P.residenceBoundary_eq_left σ ds hd i hi hi'
  have hr : (P.interval ⟨i, hi⟩).right ≤
      STLTableau.Section4.Tableau.residenceBoundary ds (i + 1) := by
    by_cases hn : i + 1 < ds.length
    · have hs := STLTableau.Section4.Tableau.residenceBoundary_step ds i hi'
      have ht := hd i hi hn
      change (ds[i] : ℝ) =
        (P.interval ⟨i, hi⟩).right - (P.interval ⟨i, hi⟩).left at ht
      linarith
    · have he : i + 1 = ds.length := by omega
      rw [he, STLTableau.Section4.Tableau.residenceBoundary_last]
      exact hfinal he
  intro x hx
  exact ⟨hl.symm ▸ MarkedInterval.left_le_of_mem hx,
    (MarkedInterval.le_right_of_mem hx).trans hr⟩

end STLTableau.IntervalPartition
