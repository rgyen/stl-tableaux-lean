import STLTableaux.Finiteness.Bounds.TruthIntervalCount
import STLTableaux.Semantics.Stability.Stability

/-! Maximal blocks of partition pieces on which the formula is true.
The partition is finite and stable for the formula. Blocks may include
singletons and exclude their right endpoints. -/
namespace STLTableau.Section4.Finiteness.TruthPartitionIntervals
variable {Var : Type*}

/-- Every position between i and j is true, including both ends. -/
def Connected {n : ℕ} (p : Fin n → Prop) (i j : Fin n) : Prop :=
  ∀ k, min i.val j.val ≤ k.val → k.val ≤ max i.val j.val → p k

theorem connected_left {n : ℕ} {p : Fin n → Prop} {i j : Fin n}
    (h : Connected p i j) : p i := h i (Nat.min_le_left _ _) (Nat.le_max_left _ _)

theorem connected_right {n : ℕ} {p : Fin n → Prop} {i j : Fin n}
    (h : Connected p i j) : p j := h j (Nat.min_le_right _ _) (Nat.le_max_right _ _)

theorem connected_refl {n : ℕ} {p : Fin n → Prop} (i : Fin n) (hi : p i) : Connected p i i := by
  intro k hl hr
  have he : k = i := Fin.ext (by simpa using le_antisymm hr hl)
  exact he ▸ hi

theorem connected_symm {n : ℕ} {p : Fin n → Prop} {i j : Fin n}
    (h : Connected p i j) : Connected p j i := by simpa [Connected,min_comm,max_comm] using h

theorem connected_trans {n : ℕ} {p : Fin n → Prop} {i j l : Fin n}
    (h : Connected p i j) (g : Connected p j l) : Connected p i l := by
  intro k hl hr
  by_cases hk : min i.val j.val ≤ k.val ∧ k.val ≤ max i.val j.val
  · exact h k hk.1 hk.2
  · exact g k (by omega) (by omega)

theorem connected_adjacent {n : ℕ} {p : Fin n → Prop} {i j : Fin n}
    (hij : j.val = i.val+1) (hi : p i) (hj : p j) : Connected p i j := by
  intro k hl hr
  have hk : k = i ∨ k = j := by
    have : k.val = i.val ∨ k.val = j.val := by omega
    exact this.imp Fin.ext Fin.ext
  rcases hk with rfl | rfl <;> assumption

/-- A run is identified canonically by its last true partition position.
Its complete consecutive range is all positions connected to that endpoint. -/
def IsEnd {n : ℕ} (p : Fin n → Prop) (e : Fin n) : Prop :=
  p e ∧ ∀ j : Fin n, j.val = e.val+1 → ¬ p j

abbrev Block {n : ℕ} (p : Fin n → Prop) := {e : Fin n // IsEnd p e}

theorem end_unique {n : ℕ} {p : Fin n → Prop} (b c : Block p)
    (h : Connected p b.val c.val) : b = c := by
  apply Subtype.ext
  by_contra hne
  have hv : b.val.val ≠ c.val.val := fun he => hne (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hbc | hcb
  · let j : Fin n := ⟨b.val.val+1,by omega⟩
    exact b.property.2 j rfl (h j (by dsimp [j]; omega) (by dsimp [j]; omega))
  · let j : Fin n := ⟨c.val.val+1,by omega⟩
    exact c.property.2 j rfl (h j (by dsimp [j]; omega) (by dsimp [j]; omega))

theorem exists_block {n : ℕ} (p : Fin n → Prop) (i : Fin n) (hi : p i) :
    ∃ b : Block p, Connected p i b.val := by
  classical
  let S := Finset.univ.filter (Connected p i)
  have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,connected_refl i hi⟩
  have hs : S.Nonempty := ⟨i,hm⟩
  let e := S.max' hs
  have he : Connected p i e := (Finset.mem_filter.mp (Finset.max'_mem S hs)).2
  have hend : IsEnd p e := by
    refine ⟨connected_right he,?_⟩
    intro j hj hjp
    have hconn := connected_trans he (connected_adjacent hj (connected_right he) hjp)
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hconn⟩
    have hle := Finset.le_max' S j hjS
    change j.val ≤ e.val at hle
    omega
  exact ⟨⟨e,hend⟩,he⟩

noncomputable def blockOf {n : ℕ} (p : Fin n → Prop) (i : Fin n) (hi : p i) : Block p :=
  Classical.choose (exists_block p i hi)

theorem blockOf_connected {n : ℕ} (p : Fin n → Prop) (i : Fin n) (hi : p i) :
    Connected p i (blockOf p i hi).val := Classical.choose_spec (exists_block p i hi)

theorem blockOf_unique {n : ℕ} (p : Fin n → Prop) (i : Fin n) (hi : p i)
    (b : Block p) (h : Connected p i b.val) : blockOf p i hi = b :=
  end_unique _ _ (connected_trans (connected_symm (blockOf_connected p i hi)) h)

theorem blockOf_eq_of_connected {n : ℕ} (p : Fin n → Prop) (i j : Fin n)
    (hi : p i) (hj : p j) (h : Connected p i j) : blockOf p i hi = blockOf p j hj :=
  blockOf_unique p i hi _ (connected_trans h (blockOf_connected p j hj))

theorem blockOf_adjacent {n : ℕ} (p : Fin n → Prop) (i j : Fin n)
    (hi : p i) (hj : p j) (hij : j.val=i.val+1) : blockOf p i hi = blockOf p j hj :=
  blockOf_eq_of_connected p i j hi hj (connected_adjacent hij hi hj)

/-- Uniform formula truth on one actual partition piece. -/
def PieceTrue (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (i : Fin P.size) : Prop :=
  ∀ x : σ.Time, x.val ∈ P.interval i → σ.Satisfies θ x

abbrev TruthBlock (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var) :=
  Block (PieceTrue σ P θ)

def source (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (b : TruthBlock σ P θ) : Set σ.Time :=
  {x | ∃ i, Connected (PieceTrue σ P θ) i b.val ∧ x.val ∈ P.interval i}

def endpoint (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (b : TruthBlock σ P θ) : ℝ := (P.interval b.val).right

theorem source_true (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (b : TruthBlock σ P θ) {x : σ.Time} (hx : x ∈ source σ P θ b) : σ.Satisfies θ x := by
  obtain ⟨i,hi,hx⟩ := hx
  exact connected_left hi x hx

theorem connected_le_end {n : ℕ} {p : Fin n → Prop} (b : Block p) (i : Fin n)
    (h : Connected p i b.val) : i.val ≤ b.val.val := by
  by_contra hnot
  let j : Fin n := ⟨b.val.val+1,by omega⟩
  exact b.property.2 j rfl (h j (by dsimp [j]; omega) (by dsimp [j]; omega))

theorem piece_subset_domain (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) {x : ℝ} (hx : x ∈ P.interval i) : x ∈ σ.domain := by
  rw [← P.covers]
  exact Set.mem_iUnion.mpr ⟨i,hx⟩

theorem piece_point (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) : ∃ x : σ.Time, x.val ∈ P.interval i := by
  obtain ⟨x,hx⟩ := P.nonempty i
  exact ⟨⟨x,piece_subset_domain σ P i hx⟩,hx⟩

/-- Disjointness makes point order strict even at shared marked endpoints. -/
theorem point_lt_of_index_lt {D : Set ℝ} (P : IntervalPartition D)
    {i j : Fin P.size} (hij : i < j) {x y : ℝ}
    (hx : x ∈ P.interval i) (hy : y ∈ P.interval j) : x < y := by
  have hle := (MarkedInterval.le_right_of_mem hx).trans
    ((P.ordered hij).trans (MarkedInterval.left_le_of_mem hy))
  apply lt_of_le_of_ne hle
  intro he
  exact (P.pairwiseDisjoint (ne_of_lt hij)).notMem_of_mem_left hx (he.symm ▸ hy)

theorem index_le_of_point_le {D : Set ℝ} (P : IntervalPartition D)
    {i j : Fin P.size} {x y : ℝ} (hx : x ∈ P.interval i) (hy : y ∈ P.interval j)
    (hxy : x ≤ y) : i ≤ j := by
  by_contra hnot
  have hji : j < i := lt_of_not_ge hnot
  exact (not_lt_of_ge hxy) (point_lt_of_index_lt P hji hy hx)

theorem source_nonempty (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (b : TruthBlock σ P θ) : (source σ P θ b).Nonempty := by
  obtain ⟨x,hx⟩ := piece_point σ P b.val
  exact ⟨x,b.val,connected_refl _ b.property.1,hx⟩

theorem source_upper (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (b : TruthBlock σ P θ) {x : σ.Time}
    (hx : x ∈ source σ P θ b) : x.val ≤ endpoint σ P θ b := by
  obtain ⟨i,hi,hx⟩ := hx
  have hle := connected_le_end b i hi
  rcases eq_or_lt_of_le hle with he | he
  · have hei : i = b.val := Fin.ext he
    simpa only [hei,endpoint] using MarkedInterval.le_right_of_mem hx
  · exact (MarkedInterval.le_right_of_mem hx).trans
      ((P.ordered he).trans (P.left_le_right b.val))

/-- Right cofinality for every nonempty marked interval. A singleton uses its
included endpoint; otherwise an interior point suffices, even if right is open. -/
theorem piece_right_cofinal (J : MarkedInterval) (hne : J.carrier.Nonempty)
    (v : ℝ) (hv : v < J.right) : ∃ x ∈ J.carrier, v < x := by
  obtain ⟨x,hx⟩ := hne
  by_cases hvx : v < x
  · exact ⟨x,hx,hvx⟩
  · obtain ⟨y,hvy,hyr⟩ := exists_between hv
    exact ⟨y,⟨Or.inl ((MarkedInterval.left_le_of_mem hx).trans_lt
      ((le_of_not_gt hvx).trans_lt hvy)),Or.inl hyr⟩,hvy⟩

theorem source_cofinal (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (b : TruthBlock σ P θ) (v : ℝ)
    (hv : v < endpoint σ P θ b) : ∃ x ∈ source σ P θ b, v < x.val := by
  obtain ⟨x,hx,hvx⟩ := piece_right_cofinal (P.interval b.val) (P.nonempty b.val) v hv
  exact ⟨⟨x,piece_subset_domain σ P b.val hx⟩,
    ⟨b.val,connected_refl _ b.property.1,hx⟩,hvx⟩

/-- Local formula stability transfers one true origin to its whole piece. -/
theorem pieceTrue_of_mem (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (hst : ∀ i, σ.Stable (P.interval i) θ)
    (i : Fin P.size) (x : σ.Time) (hx : x.val ∈ P.interval i)
    (ht : σ.Satisfies θ x) : PieceTrue σ P θ i := by
  intro y hy
  exact (hst i x y hx hy).1 ht

theorem sameTruthBlock_symm (σ : FiniteSignal Var) (θ : Formula Var) (x y : σ.Time)
    (h : SameTruthBlock σ θ x y) : SameTruthBlock σ θ y x := by
  simpa [SameTruthBlock,min_comm,max_comm] using h

/-- The pointwise truth-block relation yields the actual consecutive true
positions. Stability is used at the two partial end pieces and nowhere else. -/
theorem connected_of_sameTruthBlock_ordered
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) θ) (i j : Fin P.size) (hij : i ≤ j)
    (x y : σ.Time) (hx : x.val ∈ P.interval i) (hy : y.val ∈ P.interval j)
    (h : SameTruthBlock σ θ x y) : Connected (PieceTrue σ P θ) i j := by
  intro k hl hr
  by_cases hki : k = i
  · subst k
    exact pieceTrue_of_mem σ P θ hst i x hx (h x (min_le_left _ _) (le_max_left _ _))
  · by_cases hkj : k = j
    · subst k
      exact pieceTrue_of_mem σ P θ hst j y hy (h y (min_le_right _ _) (le_max_right _ _))
    · have hik : i < k := by have hne : k.val ≠ i.val := fun he => hki (Fin.ext he); omega
      have hkj' : k < j := by have hne : k.val ≠ j.val := fun he => hkj (Fin.ext he); omega
      obtain ⟨z,hz⟩ := piece_point σ P k
      have hxz := point_lt_of_index_lt P hik hx hz
      have hzy := point_lt_of_index_lt P hkj' hz hy
      exact pieceTrue_of_mem σ P θ hst k z hz
        (h z ((min_le_left _ _).trans hxz.le) (hzy.le.trans (le_max_right _ _)))

theorem connected_of_sameTruthBlock
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) θ) (i j : Fin P.size)
    (x y : σ.Time) (hx : x.val ∈ P.interval i) (hy : y.val ∈ P.interval j)
    (h : SameTruthBlock σ θ x y) : Connected (PieceTrue σ P θ) i j := by
  rcases le_total i j with hij | hji
  · exact connected_of_sameTruthBlock_ordered σ P θ hst i j hij x y hx hy h
  · exact connected_symm (connected_of_sameTruthBlock_ordered σ P θ hst j i hji y x hy hx
      (sameTruthBlock_symm σ θ x y h))

theorem sameTruthBlock_of_connected
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (i j : Fin P.size) (x y : σ.Time) (hx : x.val ∈ P.interval i) (hy : y.val ∈ P.interval j)
    (h : Connected (PieceTrue σ P θ) i j) : SameTruthBlock σ θ x y := by
  intro z hl hr
  have hzD : z.val ∈ σ.domain := z.property
  rw [← P.covers] at hzD
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hzD
  have hklo : min i.val j.val ≤ k.val := by
    by_contra hnot
    have hki : k < i := by omega
    have hkj : k < j := by omega
    have hlt := lt_min (point_lt_of_index_lt P hki hk hx) (point_lt_of_index_lt P hkj hk hy)
    exact (not_lt_of_ge hl) hlt
  have hkhi : k.val ≤ max i.val j.val := by
    by_contra hnot
    have hik : i < k := by omega
    have hjk : j < k := by omega
    have hlt := max_lt (point_lt_of_index_lt P hik hx hk) (point_lt_of_index_lt P hjk hy hk)
    exact (not_lt_of_ge hr) hlt
  exact h k hklo hkhi z hk

/-- The selected source is exactly the actual maximal uninterrupted truth
interval containing any one of its origins, not merely a set of true samples. -/
theorem source_iff_sameTruthBlock
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) θ) (b : TruthBlock σ P θ)
    (x : σ.Time) (hx : x ∈ source σ P θ b) (y : σ.Time) :
    y ∈ source σ P θ b ↔ SameTruthBlock σ θ x y := by
  obtain ⟨i,hi,hxi⟩ := hx
  constructor
  · rintro ⟨j,hj,hyj⟩
    exact sameTruthBlock_of_connected σ P θ i j x y hxi hyj
      (connected_trans hi (connected_symm hj))
  · intro hxy
    have hyD : y.val ∈ σ.domain := y.property
    rw [← P.covers] at hyD
    obtain ⟨j,hyj⟩ := Set.mem_iUnion.mp hyD
    exact ⟨j,connected_trans (connected_symm
      (connected_of_sameTruthBlock σ P θ hst i j x y hxi hyj hxy)) hi,hyj⟩

theorem source_separated
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) θ) (b c : TruthBlock σ P θ) (hne : b ≠ c)
    (x : σ.Time) (hx : x ∈ source σ P θ b) (y : σ.Time) (hy : y ∈ source σ P θ c) :
    ¬ SameTruthBlock σ θ x y := by
  obtain ⟨i,hi,hxi⟩ := hx
  obtain ⟨j,hj,hyj⟩ := hy
  intro hxy
  exact hne (end_unique b c (connected_trans (connected_symm hi)
    (connected_trans (connected_of_sameTruthBlock σ P θ hst i j x y hxi hyj hxy) hj)))

/-- Endpoints of distinct maximal runs are strictly ordered. A false singleton
separator is a genuine intervening piece, so equal geometric boundary numbers
are never silently used to merge different runs. -/
theorem endpoint_lt_of_last_lt
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (b c : TruthBlock σ P θ) (hbc : b.val < c.val) :
    endpoint σ P θ b < endpoint σ P θ c := by
  let j : Fin P.size := ⟨b.val.val+1,by have := c.val.isLt; omega⟩
  have hjc : j < c.val := by
    have hne : j ≠ c.val := by
      intro he
      exact b.property.2 j rfl (he.symm ▸ c.property.1)
    have hval : j.val ≠ c.val.val := fun he => hne (Fin.ext he)
    change b.val.val+1 ≠ c.val.val at hval
    change b.val.val+1 < c.val.val
    change b.val.val < c.val.val at hbc
    omega
  obtain ⟨x,hx⟩ := piece_point σ P j
  obtain ⟨y,hy⟩ := piece_point σ P c.val
  have hxy := point_lt_of_index_lt P hjc hx hy
  have hbx : endpoint σ P θ b ≤ x.val :=
    (P.ordered (show b.val < j by change b.val.val < b.val.val+1; omega)).trans (MarkedInterval.left_le_of_mem hx)
  exact hbx.trans_lt (hxy.trans_le (MarkedInterval.le_right_of_mem hy))

theorem endpoint_injective (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) : Function.Injective (endpoint σ P θ) := by
  intro b c he
  apply Subtype.ext
  rcases lt_trichotomy b.val c.val with hlt | heq | hgt
  · have h := endpoint_lt_of_last_lt σ P θ b c hlt
    rw [he] at h
    exact False.elim (lt_irrefl _ h)
  · exact heq
  · have h := endpoint_lt_of_last_lt σ P θ c b hgt
    rw [he] at h
    exact False.elim (lt_irrefl _ h)

noncomputable def truthBlockOf (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (i : Fin P.size) (hi : PieceTrue σ P θ i) : TruthBlock σ P θ :=
  blockOf (PieceTrue σ P θ) i hi

theorem truthBlockOf_contains (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (i : Fin P.size) (hi : PieceTrue σ P θ i)
    (x : σ.Time) (hx : x.val ∈ P.interval i) :
    x ∈ source σ P θ (truthBlockOf σ P θ i hi) :=
  ⟨i,blockOf_connected _ i hi,hx⟩

theorem truthBlockOf_adjacent (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (i j : Fin P.size) (hi : PieceTrue σ P θ i) (hj : PieceTrue σ P θ j)
    (hij : j.val=i.val+1) : truthBlockOf σ P θ i hi = truthBlockOf σ P θ j hj :=
  blockOf_adjacent _ i j hi hj hij

/-- A true origin selects an actual maximal truth interval containing its
entire partition piece. Only stability of θ on each piece is needed. -/
theorem exists_truthBlock_of_true_origin
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) θ) (i : Fin P.size)
    (x : σ.Time) (hx : x.val ∈ P.interval i) (ht : σ.Satisfies θ x) :
    ∃ b : TruthBlock σ P θ, ∀ y : σ.Time, y.val ∈ P.interval i → y ∈ source σ P θ b := by
  have hi := pieceTrue_of_mem σ P θ hst i x hx ht
  exact ⟨truthBlockOf σ P θ i hi,truthBlockOf_contains σ P θ i hi⟩

/-- A false point in an intervening piece prevents truth-block connection.
In particular this applies when that piece is just the single false endpoint;
no positive duration hypothesis on the separator is present. -/
theorem false_point_separates (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (θ : Formula Var) (i k j : Fin P.size) (hik : i < k) (hkj : k < j)
    (x z y : σ.Time) (hx : x.val ∈ P.interval i) (hz : z.val ∈ P.interval k)
    (hy : y.val ∈ P.interval j) (hf : ¬ σ.Satisfies θ z) :
    ¬ SameTruthBlock σ θ x y := by
  intro h
  have hxz := point_lt_of_index_lt P hik hx hz
  have hzy := point_lt_of_index_lt P hkj hz hy
  exact hf (h z ((min_le_left _ _).trans hxz.le) (hzy.le.trans (le_max_right _ _)))

/-- On a stable partition, bound the number of maximal truth intervals of a
bounded temporal formula ending in a window of width `I.upper`. -/
theorem ended_partition_truth_blocks_bound
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (hst : ∀ i, σ.Stable (P.interval i) (boundedTemporal kind I φ))
    (T : Finset (TruthBlock σ P (boundedTemporal kind I φ))) (u : ℝ)
    (hend : ∀ b ∈ T, u-I.upper ≤ endpoint σ P (boundedTemporal kind I φ) b ∧
      endpoint σ P (boundedTemporal kind I φ) b ≤ u) :
    T.card ≤ ⌈I.upper/(I.upper-I.lower)⌉₊ + 3 := by
  apply ended_truth_blocks_bound σ kind I φ T
    (source σ P (boundedTemporal kind I φ)) (endpoint σ P (boundedTemporal kind I φ)) u hend
  · exact (endpoint_injective σ P _).injOn
  · intro b _ x hx
    exact source_true σ P _ b hx
  · intro b _ x hx
    exact source_upper σ P _ b hx
  · intro b _ v hv
    exact source_cofinal σ P _ b v hv
  · intro b _ c _ hne x hx y hy
    exact source_separated σ P _ hst b c hne x hx y hy

end STLTableau.Section4.Finiteness.TruthPartitionIntervals
