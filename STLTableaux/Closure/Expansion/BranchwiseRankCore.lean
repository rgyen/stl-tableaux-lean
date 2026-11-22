import STLTableaux.Closure.Expansion.ExpansionRankTermination

/-! Set-valued branchwise levels and their fresh-predicate rank. The descent
argument needs only bounded initial complexities and fresh-frontier provenance;
it does not require that the levels or their sets of predicates be finite. -/
namespace STLTableau.Section3.BranchwiseExpansion

variable {State Pred : Type*}

/-- Level zero contains the initial state; each next level takes one expansion
at a selected predicate in the current state. -/
def level (Step : Pred → State → State → Prop) (current : State → Set Pred)
    (initial : State) : ℕ → Set State
  | 0 => {initial}
  | i + 1 => {t | ∃ s ∈ level Step current initial i, ∃ p ∈ current s, Step p s t}

/-- Predicates appearing in the current component anywhere in a level. -/
def labels (Step : Pred → State → State → Prop) (current : State → Set Pred)
    (initial : State) (i : ℕ) : Set Pred :=
  {p | ∃ s ∈ level Step current initial i, p ∈ current s}

/-- At level zero all predicates are fresh; otherwise compare the whole level
with the immediately preceding level. -/
def fresh (Step : Pred → State → State → Prop) (current : State → Set Pred)
    (initial : State) : ℕ → Set Pred
  | 0 => labels Step current initial 0
  | i + 1 => labels Step current initial (i + 1) \ labels Step current initial i

/-- The maximum complexity among the fresh predicates (empty maximum zero). -/
noncomputable def rank (Step : Pred → State → State → Prop) (current : State → Set Pred)
    (complexity : Pred → ℕ) (initial : State) (i : ℕ) : ℕ :=
  sSup (complexity '' fresh Step current initial i)

variable {Step : Pred → State → State → Prop} {current : State → Set Pred}
variable {complexity : Pred → ℕ} {initial : State}

@[simp] theorem mem_level_zero {s : State} :
    s ∈ level Step current initial 0 ↔ s = initial := Iff.rfl

theorem mem_level_succ {i : ℕ} {t : State} :
    t ∈ level Step current initial (i + 1) ↔
      ∃ s ∈ level Step current initial i, ∃ p ∈ current s, Step p s t := Iff.rfl

theorem mem_labels {i : ℕ} {p : Pred} :
    p ∈ labels Step current initial i ↔
      ∃ s ∈ level Step current initial i, p ∈ current s := Iff.rfl

@[simp] theorem labels_zero :
    labels Step current initial 0 = current initial := by
  ext p
  simp [labels]

@[simp] theorem fresh_zero :
    fresh Step current initial 0 = current initial := labels_zero

theorem mem_fresh_succ {i : ℕ} {p : Pred} :
    p ∈ fresh Step current initial (i + 1) ↔
      p ∈ labels Step current initial (i + 1) ∧ p ∉ labels Step current initial i :=
  Iff.rfl

theorem labels_succ_mono
    (hkeep : ∀ ⦃p s t⦄, Step p s t → current s ⊆ current t)
    (hexists : ∀ ⦃p s⦄, p ∈ current s → ∃ t, Step p s t) (i : ℕ) :
    labels Step current initial i ⊆ labels Step current initial (i + 1) := by
  rintro q ⟨s, hs, hq⟩
  obtain ⟨t, ht⟩ := hexists hq
  exact ⟨t, ⟨s, hs, q, hq, ht⟩, hkeep ht hq⟩

theorem labels_mono
    (hkeep : ∀ ⦃p s t⦄, Step p s t → current s ⊆ current t)
    (hexists : ∀ ⦃p s⦄, p ∈ current s → ∃ t, Step p s t) :
    Monotone (labels Step current initial) :=
  monotone_nat_of_le_succ (labels_succ_mono hkeep hexists)

/-- The exact local property needed for the rank argument: each next-level
novelty comes from a strictly larger predicate fresh at this level. -/
def FreshProvenance (Step : Pred → State → State → Prop) (current : State → Set Pred)
    (complexity : Pred → ℕ) (initial : State) : Prop :=
  ∀ i, ∀ q ∈ fresh Step current initial (i + 1),
    ∃ p ∈ fresh Step current initial i, complexity q < complexity p

/-- Separate the upper inclusion (every novelty is a child) from the replay
property (a child of a predicate one level earlier is already present).
This avoids requiring an exact set identity when proving the bridge. -/
theorem freshProvenance_of_children (children : Pred → Set Pred)
    (hnext : ∀ i, ∀ q ∈ fresh Step current initial (i + 1),
      ∃ p ∈ labels Step current initial i, q ∈ children p)
    (hreplay : ∀ i, ∀ p ∈ labels Step current initial i,
      children p ⊆ labels Step current initial (i + 1))
    (hcomplex : ∀ ⦃p q⦄, q ∈ children p → complexity q < complexity p) :
    FreshProvenance Step current complexity initial := by
  intro i q hq
  obtain ⟨p, hp, hchild⟩ := hnext i q hq
  refine ⟨p, ?_, hcomplex hchild⟩
  cases i with
  | zero => exact hp
  | succ i =>
    exact ⟨hp, fun hold => (mem_fresh_succ.mp hq).2 (hreplay i p hold hchild)⟩

/-- In particular, a context-independent exact child recurrence suffices. -/
theorem freshProvenance_of_recurrence (children : Pred → Set Pred)
    (hrec : ∀ i, labels Step current initial (i + 1) =
      labels Step current initial i ∪ ⋃ p ∈ labels Step current initial i, children p)
    (hcomplex : ∀ ⦃p q⦄, q ∈ children p → complexity q < complexity p) :
    FreshProvenance Step current complexity initial := by
  refine freshProvenance_of_children children ?_ ?_ hcomplex
  · intro i q hq
    obtain ⟨hnew, hold⟩ := mem_fresh_succ.mp hq
    rw [hrec] at hnew
    have hchild := hnew.resolve_left hold
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hchild
    obtain ⟨hpl, hpq⟩ := Set.mem_iUnion.mp hp
    exact ⟨p, hpl, hpq⟩
  · intro i p hp q hq
    rw [hrec]
    apply Or.inr
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hq⟩⟩

theorem fresh_bounded (hprov : FreshProvenance Step current complexity initial)
    {N : ℕ} (hinit : ∀ p ∈ current initial, complexity p ≤ N) :
    ∀ i, ∀ p ∈ fresh Step current initial i, complexity p ≤ N := by
  intro i
  induction i with
  | zero => simpa using hinit
  | succ i ih =>
    intro q hq
    obtain ⟨p, hp, hlt⟩ := hprov i q hq
    exact hlt.le.trans (ih p hp)

theorem complexity_le_rank {i : ℕ} {p : Pred} {N : ℕ}
    (hbound : ∀ q ∈ fresh Step current initial i, complexity q ≤ N)
    (hp : p ∈ fresh Step current initial i) :
    complexity p ≤ rank Step current complexity initial i :=
  le_csSup ⟨N, by rintro n ⟨q, hq, rfl⟩; exact hbound q hq⟩ ⟨p, hp, rfl⟩

theorem rank_le {i N : ℕ}
    (hbound : ∀ p ∈ fresh Step current initial i, complexity p ≤ N) :
    rank Step current complexity initial i ≤ N := by
  unfold rank
  by_cases hne : (complexity '' fresh Step current initial i).Nonempty
  · exact csSup_le hne (by rintro n ⟨p, hp, rfl⟩; exact hbound p hp)
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

theorem rank_attained {i N : ℕ}
    (hbound : ∀ p ∈ fresh Step current initial i, complexity p ≤ N)
    (hne : (fresh Step current initial i).Nonempty) :
    ∃ p ∈ fresh Step current initial i, complexity p = rank Step current complexity initial i :=
  Nat.sSup_mem (hne.image complexity) ⟨N, by rintro n ⟨p, hp, rfl⟩; exact hbound p hp⟩

theorem rank_succ_lt_of_pos (hprov : FreshProvenance Step current complexity initial)
    {N : ℕ} (hinit : ∀ p ∈ current initial, complexity p ≤ N) {i : ℕ}
    (hi : 0 < rank Step current complexity initial i) :
    rank Step current complexity initial (i + 1) < rank Step current complexity initial i := by
  have hlt : ∀ q ∈ fresh Step current initial (i + 1),
      complexity q < rank Step current complexity initial i := by
    intro q hq
    obtain ⟨p, hp, hqp⟩ := hprov i q hq
    exact hqp.trans_le (complexity_le_rank (fresh_bounded hprov hinit i) hp)
  have hb := rank_le (fun q hq => Nat.le_pred_of_lt (hlt q hq))
  exact hb.trans_lt (Nat.pred_lt (Nat.ne_of_gt hi))

theorem fresh_succ_eq_empty_of_rank_zero (hprov : FreshProvenance Step current complexity initial)
    {N : ℕ} (hinit : ∀ p ∈ current initial, complexity p ≤ N) {i : ℕ}
    (hi : rank Step current complexity initial i = 0) :
    fresh Step current initial (i + 1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨p, hp, hqp⟩ := hprov i q hq
  have hle := complexity_le_rank (fresh_bounded hprov hinit i) hp
  omega

theorem rank_succ_zero_of_zero (hprov : FreshProvenance Step current complexity initial)
    {N : ℕ} (hinit : ∀ p ∈ current initial, complexity p ≤ N) {i : ℕ}
    (hi : rank Step current complexity initial i = 0) :
    rank Step current complexity initial (i + 1) = 0 := by
  simp [rank, fresh_succ_eq_empty_of_rank_zero hprov hinit hi]

theorem rank_eventually_zero (hprov : FreshProvenance Step current complexity initial)
    {N : ℕ} (hinit : ∀ p ∈ current initial, complexity p ≤ N) :
    ∃ k : ℕ, ∀ i ≥ k, rank Step current complexity initial i = 0 :=
  eventually_zero_of_rank_decrease _
    (fun _ => rank_succ_lt_of_pos hprov hinit)
    (fun _ => rank_succ_zero_of_zero hprov hinit)

end STLTableau.Section3.BranchwiseExpansion
