import STLTableaux.Semantics.Partitions.MarkedBoundaryPartition

/-! Marker-aware partitions allowing singleton pieces. Repeated boundaries
represent a selected zero-time state, not every jump in an execution.
At a repeated boundary both endpoints of that piece must be closed; the
next piece consequently starts open. No graph-path selection is assumed. -/
namespace STLTableau.IntervalPartition

/-- Exactly the marker condition making a zero-width piece nonempty. -/
def SingletonCompatible {n : ℕ} (b : Fin (n + 1) → ℝ)
    (m : Fin (n + 1) → Marker) : Prop :=
  ∀ i : Fin n, b ⟨i.val, by omega⟩ = b ⟨i.val + 1, by omega⟩ →
    m ⟨i.val, by omega⟩ = ● ∧ m ⟨i.val + 1, by omega⟩ = ○

theorem markedBoundaryPiece_nonempty_of_monotone {n : ℕ}
    (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m) (i : Fin n) :
    (markedBoundaryPiece b m i).carrier.Nonempty := by
  have hle := hb (show (⟨i.val, by omega⟩ : Fin (n + 1)) ≤
    ⟨i.val + 1, by omega⟩ by simp)
  rcases lt_or_eq_of_le hle with hlt | he
  · obtain ⟨x, hl, hr⟩ := exists_between hlt
    exact ⟨x, Or.inl hl, Or.inl hr⟩
  · obtain ⟨hm, hm'⟩ := hz i he
    refine ⟨b ⟨i.val, by omega⟩, ?_⟩
    simp [markedBoundaryPiece, MarkedInterval.carrier_eq, hm, hm', he,
      Marker.complement]

theorem markedBoundaryPiece_disjoint_of_monotone {n : ℕ}
    (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    {i j : Fin n} (hij : i < j) :
    Disjoint (markedBoundaryPiece b m i).carrier (markedBoundaryPiece b m j).carrier := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi := markedBoundaryPiece_subset_closed b m i hxi
  have hj := markedBoundaryPiece_subset_closed b m j hxj
  have hle := hb (show (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≤
    ⟨j.val, by omega⟩ by change i.val + 1 ≤ j.val; exact hij)
  have he : b ⟨i.val + 1, by omega⟩ = b ⟨j.val, by omega⟩ :=
    le_antisymm hle (hj.1.trans hi.2)
  have hx : x = b ⟨i.val + 1, by omega⟩ := le_antisymm hi.2 (he ▸ hj.1)
  have hr := (MarkedInterval.mem_iff.mp hxi).2
  have hl := (MarkedInterval.mem_iff.mp hxj).1
  have hm : m ⟨i.val + 1, by omega⟩ = ○ := by
    cases hm : m ⟨i.val + 1, by omega⟩ <;>
      simp_all [markedBoundaryPiece, Marker.complement, Marker.Includes]
  by_cases hadj : i.val + 1 = j.val
  · have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨j.val, by omega⟩ := Fin.ext hadj
    rw [hidx] at hm hx
    simp [markedBoundaryPiece, hx, hm, Marker.Includes] at hl
  · have hlt : i.val + 1 < j.val := by change i.val < j.val at hij; omega
    let k : Fin n := ⟨i.val + 1, by omega⟩
    have hek : b ⟨k.val, by omega⟩ = b ⟨k.val + 1, by omega⟩ := by
      apply le_antisymm (hb (by simp))
      calc b ⟨k.val + 1, by omega⟩ ≤ b ⟨j.val, by omega⟩ :=
             hb (by change i.val + 1 + 1 ≤ j.val; omega)
           _ = b ⟨k.val, by omega⟩ := he.symm
    have hmk := (hz k hek).1
    change m ⟨i.val + 1, by omega⟩ = ● at hmk
    rw [hm] at hmk
    cases hmk

/-- The singleton/open-interval construction on weakly increasing
times. The result has the original indexing: no pieces or states are added. -/
def ofSingletonBoundaries {n : ℕ} (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨n, by omega⟩ = ●) :
    IntervalPartition (Set.Ico (b ⟨0, by omega⟩) (b ⟨n, by omega⟩)) where
  size := n
  interval := markedBoundaryPiece b m
  nonempty := markedBoundaryPiece_nonempty_of_monotone b hb m hz
  pairwiseDisjoint := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact markedBoundaryPiece_disjoint_of_monotone b hb m hz hlt
    · exact (markedBoundaryPiece_disjoint_of_monotone b hb m hz hgt).symm
  covers := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have hx := markedBoundaryPiece_subset_closed b m i hi
      refine ⟨(hb (by change 0 ≤ i.val; omega)).trans hx.1, ?_⟩
      have hupper := hb (show (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≤
        ⟨n, by omega⟩ by change i.val + 1 ≤ n; omega)
      by_contra hn
      have he : b ⟨i.val + 1, by omega⟩ = b ⟨n, by omega⟩ := by linarith [hx.2]
      have hxe : x = b ⟨i.val + 1, by omega⟩ := by linarith [hx.2]
      have hr := (MarkedInterval.mem_iff.mp hi).2
      have hm : m ⟨i.val + 1, by omega⟩ = ○ := by
        cases hm : m ⟨i.val + 1, by omega⟩ <;>
          simp_all [markedBoundaryPiece, Marker.complement, Marker.Includes]
      by_cases hiend : i.val + 1 = n
      · have hidx : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext hiend
        rw [hidx, hlast] at hm
        cases hm
      · let k : Fin n := ⟨i.val + 1, by omega⟩
        have hek : b ⟨k.val, by omega⟩ = b ⟨k.val + 1, by omega⟩ := by
          apply le_antisymm (hb (by simp))
          exact (hb (show (⟨k.val + 1, by omega⟩ : Fin (n + 1)) ≤
            ⟨n, by omega⟩ by change i.val + 1 + 1 ≤ n; omega)).trans he.symm.le
        have hmk := (hz k hek).1
        change m ⟨i.val + 1, by omega⟩ = ● at hmk
        rw [hm] at hmk
        cases hmk
    · intro hx
      obtain ⟨i, hlo, hhi⟩ := exists_boundary_piece b hx
      by_cases he : b ⟨i.val, by omega⟩ = x
      · cases hm : m ⟨i.val, by omega⟩ with
        | closed =>
          exact ⟨i, Or.inr ⟨he, by simp [markedBoundaryPiece, hm, Marker.Includes]⟩,
            Or.inl hhi⟩
        | «open» =>
          have hipos : 0 < i.val := by
            by_contra hn
            have hidx : (⟨i.val, by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ :=
              Fin.ext (by change i.val = 0; omega)
            rw [hidx, hfirst] at hm
            cases hm
          let j : Fin n := ⟨i.val - 1, by omega⟩
          have hidx : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨i.val, by omega⟩ :=
            Fin.ext (by dsimp [j]; omega)
          refine ⟨j, ?_, Or.inr ?_⟩
          · have hle : b ⟨j.val, by omega⟩ ≤ b ⟨i.val, by omega⟩ :=
              hb (by change i.val - 1 ≤ i.val; omega)
            rcases lt_or_eq_of_le hle with hlt | heq
            · exact Or.inl (he ▸ hlt)
            · have hmj := (hz j (heq.trans (congrArg b hidx.symm))).1
              exact Or.inr ⟨heq.trans he, by simp [markedBoundaryPiece, hmj, Marker.Includes]⟩
          · change x = b ⟨j.val + 1, by omega⟩ ∧ (Marker.complement (m _)).Includes
            rw [hidx]
            exact ⟨he.symm, by simp [hm, Marker.complement, Marker.Includes]⟩
      · exact ⟨i, Or.inl (lt_of_le_of_ne hlo he), Or.inl hhi⟩
  ordered := by
    intro i j hij
    exact hb (by change i.val + 1 ≤ j.val; exact hij)

/-- The initial assignment uses a singleton for zero duration and a
left-closed, right-open interval for positive duration. -/
def rawBoundaryPiece {n : ℕ} (b : Fin (n + 1) → ℝ) (i : Fin n) : Set ℝ :=
  if b ⟨i.val, by omega⟩ = b ⟨i.val + 1, by omega⟩ then
    {b ⟨i.val, by omega⟩}
  else Set.Ico (b ⟨i.val, by omega⟩) (b ⟨i.val + 1, by omega⟩)

/-- Opening a positive piece after a singleton only removes its left point;
the singleton keeps that point. No endpoint is added to a raw piece. -/
theorem markedBoundaryPiece_subset_raw {n : ℕ}
    (b : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Marker) (i : Fin n)
    (hright : b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●) :
    (markedBoundaryPiece b m i).carrier ⊆ rawBoundaryPiece b i := by
  intro x hx
  have hc := markedBoundaryPiece_subset_closed b m i hx
  unfold rawBoundaryPiece
  split_ifs with he
  · exact Set.mem_singleton_iff.mpr (le_antisymm (he ▸ hc.2) hc.1)
  · refine ⟨hc.1, ?_⟩
    have hr := (MarkedInterval.mem_iff.mp hx).2
    simpa [markedBoundaryPiece, hright he, Marker.complement, Marker.Includes] using hr

/-- Pointwise atomic obligations transfer by restriction, exactly as in the
label argument. This does not assert satisfaction of a whole trace. -/
theorem markedBoundaryPiece_preserves_predicate {n : ℕ}
    (b : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Marker) (i : Fin n)
    (hright : b ⟨i.val, by omega⟩ ≠ b ⟨i.val + 1, by omega⟩ →
      m ⟨i.val + 1, by omega⟩ = ●)
    (P : ℝ → Prop) (hP : ∀ t ∈ rawBoundaryPiece b i, P t) :
    ∀ t ∈ (markedBoundaryPiece b m i).carrier, P t :=
  fun t ht => hP t (markedBoundaryPiece_subset_raw b m i hright ht)

@[simp] theorem markedBoundaryPiece_left_marker {n : ℕ}
    (b : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Marker) (i : Fin n) :
    (markedBoundaryPiece b m i).leftBoundary = m ⟨i.val, by omega⟩ := rfl

@[simp] theorem markedBoundaryPiece_width {n : ℕ}
    (b : Fin (n + 1) → ℝ) (m : Fin (n + 1) → Marker) (i : Fin n) :
    (markedBoundaryPiece b m i).right - (markedBoundaryPiece b m i).left =
      b ⟨i.val + 1, by omega⟩ - b ⟨i.val, by omega⟩ := rfl

/-- Every ordinary piece starts before the excluded final boundary, including
singleton pieces. This follows from nonemptiness at the last boundary. -/
theorem singletonCompatible_boundary_lt_last {n : ℕ}
    (b : Fin (n + 1) → ℝ) (hb : Monotone b)
    (m : Fin (n + 1) → Marker) (hz : SingletonCompatible b m)
    (hlast : m ⟨n, by omega⟩ = ●) (i : Fin n) :
    b ⟨i.val, by omega⟩ < b ⟨n, by omega⟩ := by
  have hn : 0 < n := by have := i.isLt; omega
  let j : Fin n := ⟨n - 1, by omega⟩
  have hidx : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ :=
    Fin.ext (by change n - 1 + 1 = n; omega)
  have hne : b ⟨j.val, by omega⟩ ≠ b ⟨n, by omega⟩ := by
    intro he
    have hm := (hz j (he.trans (congrArg b hidx.symm))).2
    rw [hidx, hlast] at hm
    cases hm
  have hjlt : b ⟨j.val, by omega⟩ < b ⟨n, by omega⟩ :=
    lt_of_le_of_ne (hb (by change n - 1 ≤ n; omega)) hne
  exact (hb (show (⟨i.val, by omega⟩ : Fin (n + 1)) ≤ ⟨j.val, by omega⟩
    by change i.val ≤ n - 1; have := i.isLt; omega)).trans_lt hjlt

end STLTableau.IntervalPartition
