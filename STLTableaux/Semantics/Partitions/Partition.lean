/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Syntax.Time.Interval

/-!
# Finite interval partitions

Ordered finite interval partitions and refinement (Section 2 and Appendix A.1).
-/

namespace STLTableau

/-- A finite, ordered partition of a real-time domain into nonempty marked
intervals. The `Fin n` indexing matches the manuscript's `J₁, …, Jₙ`. -/
structure IntervalPartition (domain : Set ℝ) where
  size : ℕ
  interval : Fin size → MarkedInterval
  nonempty : ∀ i, (interval i).carrier.Nonempty
  pairwiseDisjoint : Pairwise fun i j => Disjoint (interval i).carrier (interval j).carrier
  covers : (⋃ i, (interval i).carrier) = domain
  ordered : ∀ {i j}, i < j → (interval i).right ≤ (interval j).left

namespace IntervalPartition

/-- A nonempty zero-width piece is exactly its endpoint, regardless of how
the markers were initially presented. -/
theorem carrier_eq_singleton_of_endpoints_eq {domain : Set ℝ}
    (P : IntervalPartition domain) (i : Fin P.size)
    (he : (P.interval i).right = (P.interval i).left) :
    (P.interval i).carrier = {(P.interval i).left} := by
  have hpoint : ∀ x ∈ (P.interval i).carrier, x = (P.interval i).left := by
    intro x hx
    apply le_antisymm
    · simpa only [he] using MarkedInterval.le_right_of_mem hx
    · exact MarkedInterval.left_le_of_mem hx
  obtain ⟨x, hx⟩ := P.nonempty i
  ext y
  constructor
  · exact fun hy => Set.mem_singleton_iff.mpr (hpoint y hy)
  · intro hy
    have hy' : y = x := (Set.mem_singleton_iff.mp hy).trans (hpoint x hx).symm
    simpa only [hy'] using hx

/-- Two partition pieces cannot represent the same boundary point. This is
about interval geometry, not about erasing any automaton jump. -/
theorem eq_of_shared_point {domain : Set ℝ} (P : IntervalPartition domain)
    {i j : Fin P.size} {t : ℝ}
    (hi : t ∈ (P.interval i).carrier) (hj : t ∈ (P.interval j).carrier) : i = j := by
  by_contra hn
  exact Set.disjoint_left.mp (P.pairwiseDisjoint hn) hi hj

/-- Every nonempty piece has ordered real endpoints, irrespective of its
markers. -/
theorem left_le_right {domain : Set ℝ} (P : IntervalPartition domain)
    (i : Fin P.size) : (P.interval i).left ≤ (P.interval i).right := by
  obtain ⟨x, hx⟩ := P.nonempty i
  exact (MarkedInterval.left_le_of_mem hx).trans
    (MarkedInterval.le_right_of_mem hx)

/-- Consecutive pieces of a partition of a real interval meet at the same
endpoint.  This is derived from coverage rather than stored redundantly in
`IntervalPartition`. -/
theorem adjacent_right_eq_left {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size)
    (hi : i.1 + 1 < P.size) :
    (P.interval i).right =
      (P.interval ⟨i.1 + 1, hi⟩).left := by
  let j : Fin P.size := ⟨i.1 + 1, hi⟩
  have hij : i < j := by
    change i.1 < i.1 + 1
    omega
  have hle := P.ordered hij
  apply le_antisymm hle
  by_contra hnot
  have hgap : (P.interval i).right < (P.interval j).left :=
    lt_of_not_ge hnot
  let x := ((P.interval i).right + (P.interval j).left) / 2
  have hix : (P.interval i).right < x := by dsimp [x]; linarith
  have hxj : x < (P.interval j).left := by dsimp [x]; linarith
  obtain ⟨a, ha⟩ := P.nonempty i
  obtain ⟨b, hb⟩ := P.nonempty j
  have haD : a ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, ha⟩
  have hbD : b ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨j, hb⟩
  have hxD : x ∈ Set.Ico L R := by
    constructor
    · exact haD.1.trans ((MarkedInterval.le_right_of_mem ha).trans hix.le)
    · exact (hxj.trans_le (MarkedInterval.left_le_of_mem hb)).trans hbD.2
  have hxUnion : x ∈ ⋃ q, (P.interval q).carrier := by
    rw [P.covers]
    exact hxD
  obtain ⟨q, hqx⟩ := Set.mem_iUnion.1 hxUnion
  have hqi_or_hjq : q.1 ≤ i.1 ∨ j.1 ≤ q.1 := by
    dsimp [j]
    omega
  rcases hqi_or_hjq with hqi | hjq
  · have hxri : x ≤ (P.interval i).right := by
      rcases eq_or_lt_of_le hqi with hqi | hqi
      · have hq : q = i := Fin.ext hqi
        simpa [hq] using MarkedInterval.le_right_of_mem hqx
      · have hordered : (P.interval q).right ≤ (P.interval i).left :=
          P.ordered hqi
        exact (MarkedInterval.le_right_of_mem hqx).trans
          (hordered.trans (P.left_le_right i))
    exact (not_lt_of_ge hxri) hix
  · have hljx : (P.interval j).left ≤ x := by
      rcases eq_or_lt_of_le hjq with hjq | hjq
      · have hq : j = q := Fin.ext hjq
        simpa [hq] using MarkedInterval.left_le_of_mem hqx
      · have hordered : (P.interval j).right ≤ (P.interval q).left :=
          P.ordered hjq
        exact (P.left_le_right j).trans
          (hordered.trans (MarkedInterval.left_le_of_mem hqx))
    exact (not_lt_of_ge hljx) hxj

/-- In a partition of a connected time domain, consecutive pieces cannot
both have zero width. Thus successive zero-time modes cannot simply be
assigned separate singleton pieces at their common timestamp. -/
theorem adjacent_not_both_zero_width {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size)
    (hi : i.val + 1 < P.size)
    (hz : (P.interval i).right = (P.interval i).left) :
    (P.interval ⟨i.val + 1, hi⟩).right ≠ (P.interval ⟨i.val + 1, hi⟩).left := by
  intro hz'
  let j : Fin P.size := ⟨i.val + 1, hi⟩
  have he : (P.interval i).left = (P.interval j).left :=
    hz.symm.trans (P.adjacent_right_eq_left i hi)
  have hmem : (P.interval i).left ∈ (P.interval i).carrier := by
    rw [P.carrier_eq_singleton_of_endpoints_eq i hz]
    exact Set.mem_singleton _
  have hmem' : (P.interval i).left ∈ (P.interval j).carrier := by
    rw [P.carrier_eq_singleton_of_endpoints_eq j hz', he]
    exact Set.mem_singleton _
  have hij := P.eq_of_shared_point hmem hmem'
  have hv := congrArg Fin.val hij
  change i.val = i.val + 1 at hv
  omega

/-- At a common endpoint of consecutive partition pieces, exactly one piece
contains the endpoint. Hence their endpoint markers are complementary. -/
theorem adjacent_rightBoundary_eq_complement_leftBoundary {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size)
    (hi : i.1 + 1 < P.size) :
    (P.interval i).rightBoundary =
      Marker.complement (P.interval ⟨i.1 + 1, hi⟩).leftBoundary := by
  let j : Fin P.size := ⟨i.1 + 1, hi⟩
  have hij : i < j := by
    change i.1 < i.1 + 1
    omega
  have he : (P.interval i).right = (P.interval j).left := by
    simpa [j] using P.adjacent_right_eq_left i hi
  have hnotboth : ¬((P.interval i).rightBoundary.Includes ∧
      (P.interval j).leftBoundary.Includes) := by
    rintro ⟨hri, hlj⟩
    have hei := MarkedInterval.right_mem (P.interval i) (P.nonempty i) hri
    have hej := MarkedInterval.left_mem (P.interval j) (P.nonempty j) hlj
    exact (P.pairwiseDisjoint hij.ne).notMem_of_mem_left hei (he ▸ hej)
  have hor : (P.interval i).rightBoundary.Includes ∨
      (P.interval j).leftBoundary.Includes := by
    let e := (P.interval i).right
    obtain ⟨a, ha⟩ := P.nonempty i
    obtain ⟨b, hb⟩ := P.nonempty j
    have haD : a ∈ Set.Ico L R := by
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i, ha⟩
    have hbD : b ∈ Set.Ico L R := by
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨j, hb⟩
    have heD : e ∈ Set.Ico L R := by
      constructor
      · exact haD.1.trans (MarkedInterval.le_right_of_mem ha)
      · exact (he ▸ MarkedInterval.left_le_of_mem hb).trans_lt hbD.2
    have heUnion : e ∈ ⋃ q, (P.interval q).carrier := by
      rw [P.covers]
      exact heD
    obtain ⟨q, hqe⟩ := Set.mem_iUnion.1 heUnion
    have hqi_or_hjq : q.1 ≤ i.1 ∨ j.1 ≤ q.1 := by
      dsimp [j]
      omega
    rcases hqi_or_hjq with hqi | hjq
    · rcases eq_or_lt_of_le hqi with hqi | hqi
      · have hq : q = i := Fin.ext hqi
        subst q
        rcases hqe.2 with hlt | ⟨_, hinc⟩
        · exact (lt_irrefl e hlt).elim
        · exact Or.inl hinc
      · have hordered : (P.interval q).right ≤ (P.interval i).left :=
          P.ordered hqi
        have hleftEq : (P.interval i).left = e := by
          apply le_antisymm
          · exact P.left_le_right i
          · exact (MarkedInterval.le_right_of_mem hqe).trans hordered
        obtain ⟨z, hz⟩ := P.nonempty i
        have hzEq : z = e := le_antisymm (MarkedInterval.le_right_of_mem hz)
          (hleftEq ▸ MarkedInterval.left_le_of_mem hz)
        have : False := (P.pairwiseDisjoint (Fin.ne_of_lt hqi)).notMem_of_mem_left
          hqe (hzEq ▸ hz)
        exact this.elim
    · rcases eq_or_lt_of_le hjq with hjq | hjq
      · have hq : j = q := Fin.ext hjq
        subst q
        rcases hqe.1 with hlt | ⟨heq, hinc⟩
        · exact (ne_of_lt hlt he.symm).elim
        · exact Or.inr hinc
      · have hordered : (P.interval j).right ≤ (P.interval q).left :=
          P.ordered hjq
        have hrightEq : (P.interval j).right = e := by
          apply le_antisymm
          · exact hordered.trans (MarkedInterval.left_le_of_mem hqe)
          · change (P.interval i).right ≤ (P.interval j).right
            rw [he]
            exact P.left_le_right j
        obtain ⟨z, hz⟩ := P.nonempty j
        have hzEq : z = e := le_antisymm
          ((MarkedInterval.le_right_of_mem hz).trans_eq hrightEq)
          (by
            change (P.interval i).right ≤ z
            rw [he]
            exact MarkedInterval.left_le_of_mem hz)
        have : False := (P.pairwiseDisjoint (Fin.ne_of_lt hjq)).notMem_of_mem_left
          hz (hzEq ▸ hqe)
        exact this.elim
  generalize hri : (P.interval i).rightBoundary = ri at *
  generalize hlj : (P.interval j).leftBoundary = lj at *
  cases ri <;> cases lj <;>
    simp [Marker.Includes, Marker.complement] at hor hnotboth ⊢

/-- Every domain point after a point of the last piece still belongs to
that piece. This follows from coverage and ordering, even for singleton pieces. -/
theorem mem_last_of_le {D : Set ℝ} (P : IntervalPartition D)
    (i : Fin P.size) (hlast : i.1 + 1 = P.size)
    {t x : ℝ} (ht : t ∈ P.interval i) (hx : x ∈ D) (htx : t ≤ x) :
    x ∈ P.interval i := by
  rw [← P.covers] at hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hx
  by_cases hji : j = i
  · subst j
    exact hxj
  · have hjlt : j < i := by
      have hj := j.isLt
      have hne : j.1 ≠ i.1 := fun heq => hji (Fin.ext heq)
      change j.1 < i.1
      omega
    have hxt : x ≤ t := (MarkedInterval.le_right_of_mem hxj).trans
      ((P.ordered hjlt).trans (MarkedInterval.left_le_of_mem ht))
    have heq : x = t := le_antisymm hxt htx
    simpa only [heq] using ht

/-- The suffix of the last piece, restricted to the partition domain,
contains no points outside that piece. -/
theorem mem_last_of_left_condition {D : Set ℝ} (P : IntervalPartition D)
    (i : Fin P.size) (hlast : i.1 + 1 = P.size) {x : ℝ} (hx : x ∈ D)
    (hl : (P.interval i).left < x ∨
      ((P.interval i).left = x ∧ (P.interval i).leftBoundary.Includes)) :
    x ∈ P.interval i := by
  obtain ⟨a, ha⟩ := P.nonempty i
  by_cases hax : a ≤ x
  · exact P.mem_last_of_le i hlast ha hx hax
  · exact ⟨hl, Or.inl ((lt_of_not_ge hax).trans_le (MarkedInterval.le_right_of_mem ha))⟩

/-- In a half-open domain, a point of the last piece is strictly below
that piece's right endpoint. -/
theorem lt_right_of_mem_last {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) (hlast : i.1 + 1 = P.size) {x : ℝ}
    (hx : x ∈ P.interval i) : x < (P.interval i).right := by
  have hxD : x ∈ Set.Ico L R := by
    rw [← P.covers]
    exact Set.mem_iUnion.2 ⟨i, hx⟩
  obtain ⟨y, hxy, hyR⟩ := exists_between hxD.2
  have hy := P.mem_last_of_le i hlast hx ⟨hxD.1.trans hxy.le, hyR⟩ hxy.le
  exact hxy.trans_le (MarkedInterval.le_right_of_mem hy)

/-- The last piece of a half-open domain has an open right endpoint. -/
theorem rightBoundary_last {L R : ℝ} (P : IntervalPartition (Set.Ico L R))
    (i : Fin P.size) (hlast : i.1 + 1 = P.size) :
    (P.interval i).rightBoundary = Marker.open := by
  cases hb : (P.interval i).rightBoundary with
  | «open» => rfl
  | closed =>
    have hm : (P.interval i).rightBoundary.Includes := by rw [hb]; trivial
    have hx := MarkedInterval.right_mem (P.interval i) (P.nonempty i) hm
    exact (lt_irrefl _ (P.lt_right_of_mem_last i hlast hx)).elim

/-- The zero-based notation `intvOf J i`. -/
def intervalAt {domain : Set ℝ} (P : IntervalPartition domain) (i : Fin P.size) :
    MarkedInterval :=
  P.interval i

@[simp] theorem intervalAt_eq {domain : Set ℝ} (P : IntervalPartition domain)
    (i : Fin P.size) : P.intervalAt i = P.interval i := rfl

/-- A partition `Q` is finer than `P` when every interval of `Q` is contained
in an interval of `P`. This is the relation `Q ⊑ P` in the manuscript. -/
def FinerThan {domain : Set ℝ} (Q P : IntervalPartition domain) : Prop :=
  ∀ j, ∃ i, (Q.interval j).carrier ⊆ (P.interval i).carrier

/-- Refinement notation from the manuscript. -/
scoped[STL] infix:50 " ⊑ " => STLTableau.IntervalPartition.FinerThan

open scoped STL

theorem finerThan_refl {domain : Set ℝ} (P : IntervalPartition domain) :
    P ⊑ P := by
  intro i
  exact ⟨i, Set.Subset.rfl⟩

theorem finerThan_trans {domain : Set ℝ} {P Q R : IntervalPartition domain}
    (hRQ : R ⊑ Q) (hQP : Q ⊑ P) : R ⊑ P := by
  intro k
  obtain ⟨j, hkj⟩ := hRQ k
  obtain ⟨i, hji⟩ := hQP j
  exact ⟨i, hkj.trans hji⟩

/-- Coarseness is the converse of refinement. -/
def CoarserThan {domain : Set ℝ} (P Q : IntervalPartition domain) : Prop :=
  Q ⊑ P

/-- Coarsening notation from the manuscript. -/
scoped[STL] infix:50 " ⊒ " => STLTableau.IntervalPartition.CoarserThan

end IntervalPartition

end STLTableau
