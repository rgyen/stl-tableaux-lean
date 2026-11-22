import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Lattice

/-! Downward induction on the complexities selected by an expansion sequence.
The qualitative argument is used before passing to prefix orbits in C.15.
The finite-sequence cardinal bound is a separate quantitative consequence. -/
namespace STLTableau.Section3.BranchwiseLength

def bound (b width : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => b + width * bound b width t

private theorem initial_or_introduced {Pred : Type*} [DecidableEq Pred]
    (labels : ℕ → Finset Pred) (i : ℕ) {p : Pred} (hp : p ∈ labels i) :
    p ∈ labels 0 ∨ ∃ j < i, p ∈ labels (j + 1) \ labels j := by
  induction i with
  | zero => exact Or.inl hp
  | succ i ih =>
    by_cases hold : p ∈ labels i
    · rcases ih hold with h | ⟨j, hj, hnew⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj.trans (Nat.lt_succ_self i), hnew⟩
    · exact Or.inr ⟨i, Nat.lt_succ_self i, Finset.mem_sdiff.mpr ⟨hp, hold⟩⟩

/-- The downward induction, strengthened with explicit cardinal bounds.
The selected predicates are pairwise distinct and each step introduces at most
`width` new predicates, all strictly less complex than that step's selection. -/
theorem length_le {Pred : Type*} [DecidableEq Pred]
    (labels : ℕ → Finset Pred) (selected : ℕ → Pred) (complexity : Pred → ℕ)
    (b m width n : ℕ) (initial_card : (labels 0).card ≤ b)
    (initial_complexity : ∀ p ∈ labels 0, complexity p ≤ m)
    (selected_mem : ∀ i < n, selected i ∈ labels i)
    (distinct : Set.InjOn selected (Set.Iio n))
    (new_smaller : ∀ i < n, ∀ p ∈ labels (i + 1) \ labels i,
      complexity p < complexity (selected i))
    (new_card : ∀ i < n, (labels (i + 1) \ labels i).card ≤ width) :
    n ≤ bound b width (m + 1) := by
  let I := fun d => (Finset.range n).filter (fun i => d ≤ complexity (selected i))
  have labels_bounded : ∀ i ≤ n, ∀ p ∈ labels i, complexity p ≤ m := by
    intro i
    induction i with
    | zero => exact fun _ => initial_complexity
    | succ i ih =>
      intro hi p hp
      have hin : i < n := Nat.lt_of_succ_le hi
      have old_bound := ih hin.le
      by_cases hold : p ∈ labels i
      · exact old_bound p hold
      · exact (new_smaller i hin p (Finset.mem_sdiff.mpr ⟨hp, hold⟩)).le.trans
          (old_bound (selected i) (selected_mem i hin))
  have top_empty : I (m + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hin, hl⟩ := Finset.mem_filter.mp hi
    have hin' := Finset.mem_range.mp hin
    have hu := labels_bounded i hin'.le (selected i) (selected_mem i hin')
    omega
  have recurrence (d : ℕ) : (I d).card ≤ b + width * (I (d + 1)).card := by
    let new := fun j => labels (j + 1) \ labels j
    let introduced := (I (d + 1)).biUnion new
    have subset : (I d).image selected ⊆ labels 0 ∪ introduced := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hin, hcomp⟩ := Finset.mem_filter.mp hi
      have hin' := Finset.mem_range.mp hin
      rcases initial_or_introduced labels i (selected_mem i hin') with h | ⟨j, hj, hnew⟩
      · exact Finset.mem_union_left _ h
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hj.trans hin'),
            Nat.succ_le_of_lt (hcomp.trans_lt (new_smaller j (hj.trans hin') _ hnew))⟩, hnew⟩
    have heq : ((I d).image selected).card = (I d).card :=
      Finset.card_image_of_injOn fun i hi j hj h => distinct
        (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) h
    have hnew : introduced.card ≤ (I (d + 1)).card * width := by
      apply Finset.card_biUnion_le_card_mul (I (d + 1)) new width
      intro j hj
      exact new_card j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    calc
      (I d).card = ((I d).image selected).card := heq.symm
      _ ≤ (labels 0 ∪ introduced).card := Finset.card_le_card subset
      _ ≤ (labels 0).card + introduced.card := Finset.card_union_le _ _
      _ ≤ b + width * (I (d + 1)).card :=
        Nat.add_le_add initial_card (by simpa only [Nat.mul_comm] using hnew)
  have descending : ∀ t ≤ m + 1, (I (m + 1 - t)).card ≤ bound b width t := by
    intro t
    induction t with
    | zero => intro _; simp [bound, top_empty]
    | succ t ih =>
      intro ht
      have he : m + 1 - (t + 1) + 1 = m + 1 - t := by omega
      exact (recurrence (m + 1 - (t + 1))).trans (by
        rw [he, bound]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left width (ih (by omega))) b)
  have h := descending (m + 1) le_rfl
  simpa [I] using h

/-- The qualitative part of C.15. An infinite sequence cannot select distinct
current predicates and introduce current predicates only below the selected
predicate's complexity. No bound on the number of new predicates per step is used. -/
theorem no_infinite_expansions {Pred : Type*} [DecidableEq Pred]
    (labels : ℕ → Finset Pred) (selected : ℕ → Pred) (complexity : Pred → ℕ)
    (selected_mem : ∀ i, selected i ∈ labels i) (distinct : Function.Injective selected)
    (new_smaller : ∀ i, ∀ p ∈ labels (i + 1) \ labels i,
      complexity p < complexity (selected i)) : False := by
  classical
  let I : ℕ → Set ℕ := fun d => {i | d ≤ complexity (selected i)}
  obtain ⟨m, hm⟩ := ((labels 0).finite_toSet.image complexity).bddAbove
  have bounded : ∀ i, ∀ p ∈ labels i, complexity p ≤ m := by
    intro i
    induction i with
    | zero => exact fun p hp => hm ⟨p, hp, rfl⟩
    | succ i ih =>
      intro p hp
      by_cases hold : p ∈ labels i
      · exact ih p hold
      · exact (new_smaller i p (Finset.mem_sdiff.mpr ⟨hp, hold⟩)).le.trans
          (ih (selected i) (selected_mem i))
  have top : (I (m + 1)).Finite := by
    refine Set.finite_empty.subset ?_
    intro i hi
    have htop : m + 1 ≤ complexity (selected i) := hi
    have hle := bounded i (selected i) (selected_mem i)
    omega
  have descend (d : ℕ) (hd : (I (d + 1)).Finite) : (I d).Finite := by
    let candidates := (labels 0 : Set Pred) ∪ ⋃ j ∈ I (d + 1), (labels (j + 1) : Set Pred)
    have hc : candidates.Finite :=
      (labels 0).finite_toSet.union (hd.biUnion fun j _ => (labels (j + 1)).finite_toSet)
    refine (hc.preimage distinct.injOn).subset ?_
    intro i hi
    change selected i ∈ candidates
    rcases initial_or_introduced labels i (selected_mem i) with hold | ⟨j, hj, hnew⟩
    · exact Or.inl hold
    · have hdi : d ≤ complexity (selected i) := hi
      have hdj : j ∈ I (d + 1) :=
        Nat.succ_le_of_lt (hdi.trans_lt (new_smaller j _ hnew))
      exact Or.inr (Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨hdj, (Finset.mem_sdiff.mp hnew).1⟩⟩)
  have allDepths : ∀ r ≤ m + 1, (I (m + 1 - r)).Finite := by
    intro r
    induction r with
    | zero => intro _; simpa only [Nat.sub_zero] using top
    | succ r ih =>
      intro hr
      apply descend
      have he : m + 1 - (r + 1) + 1 = m + 1 - r := by omega
      rw [he]
      exact ih (by omega)
  have hzero : (I 0).Finite := by
    simpa only [Nat.sub_self] using allDepths (m + 1) le_rfl
  exact Set.infinite_univ (hzero.subset fun i _ => Nat.zero_le _)

end STLTableau.Section3.BranchwiseLength
