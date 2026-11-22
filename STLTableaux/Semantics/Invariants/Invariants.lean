import STLTableaux.Rules.Finite.Rules
import STLTableaux.Semantics.Intervals.IntervalLemmas
import STLTableaux.Closure.Residual.SatisfiedClosure

/-! Predicate invariants on a signal and partition. The condition for no past satisfaction
uses the last preceding interval on which the formula holds throughout. -/
namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

noncomputable def pastTrue (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) (φ : Formula Var) : Finset (Fin P.size) := by
  classical
  exact Finset.univ.filter fun j => j.1 < k.1 ∧
    ∀ t : σ.Time, t.1 ∈ P.interval j → (σ, t) ⊨ φ

@[simp] theorem mem_pastTrue (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : Judgement.Position P) (φ : Formula Var) (j : Fin P.size) :
    j ∈ pastTrue σ P k φ ↔ j.1 < k.1 ∧
      ∀ t : σ.Time, t.1 ∈ P.interval j → (σ, t) ⊨ φ := by
  classical
  simp [pastTrue]

/-- The separation bound at the last preceding interval satisfying the
formula throughout. The bound is vacuous when there is no such interval. -/
def PastSeparated (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var) : Prop :=
  ∀ j ∈ pastTrue σ P k φ, (∀ l ∈ pastTrue σ P k φ, l ≤ j) →
    (α c : ℝ) <[Marker.imp b (¬ₘ (P.interval j).rightBoundary)]
      ((P.interval ⟨k.1, hk⟩).left + I.lower - (P.interval j).right)

/-- When there is a preceding true interval, separation is equivalent to
the bound at the last such interval. -/
theorem pastSeparated_iff_max (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : (pastTrue σ P k φ).Nonempty) :
    PastSeparated σ P α k hk c b I φ ↔
      (α c : ℝ) <[Marker.imp b (¬ₘ (P.interval ((pastTrue σ P k φ).max' hne)).rightBoundary)]
        ((P.interval ⟨k.1, hk⟩).left + I.lower -
          (P.interval ((pastTrue σ P k φ).max' hne)).right) := by
  classical
  constructor
  · intro h
    exact h _ (Finset.max'_mem _ _) (fun j hj => Finset.le_max' _ j hj)
  · intro h j hj hmax
    have he : j = (pastTrue σ P k φ).max' hne :=
      le_antisymm (Finset.le_max' _ j hj) (hmax _ (Finset.max'_mem _ _))
    simpa only [he] using h

/-- The five invariant cases, including past-cover exclusion. -/
def Invariant (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size) :
    IntervalPredicate Clock Var → Prop
  | .plain _ => True
  | .upper c b .always I _ =>
      (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] I.lower
  | .bounded c d b q .always I _ =>
      ((α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] I.lower) ∧
      ((α d : ℝ) <[Marker.conj b q] ((α c : ℝ) + (I.upper - I.lower)))
  | .upper c b .eventually I φ =>
      ((α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] I.upper) ∧
      ((0 : ℝ) <[Marker.conj b (P.interval ⟨k.1, hk⟩).rightBoundary]
        ((α c : ℝ) + ((P.interval ⟨k.1, hk⟩).right - (P.interval ⟨k.1, hk⟩).left))) ∧
      PastSeparated σ P α k hk c b I φ
  | .bounded c d b q .eventually I φ =>
      ((α c : ℝ) <[Marker.imp b (P.interval ⟨k.1, hk⟩).leftBoundary] I.upper) ∧
      ((α d : ℝ) <[Marker.conj b q] (α c : ℝ)) ∧
      PastSeparated σ P α k hk c b I φ

/-- Under the marked start condition, checking points already belong to the
current suffix; adding a suffix intersection would therefore change nothing. -/
theorem always_safe (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval)
    (h : (α c : ℝ) <[Marker.imp b J.leftBoundary] I.lower)
    {S : Scope} (he : S.left = J.left - α c) (hb : S.leftBoundary = b)
    {t : ℝ} (ht : t ∈ alwaysRegion S I) : InCurrentSuffix J t := by
  have hl : S.left + I.lower < t ∨
      (S.left + I.lower = t ∧ S.leftBoundary.Includes) := ht.1
  rw [he, hb] at hl
  rcases h with h | ⟨h, hm⟩
  · exact Or.inl (by rcases hl with hl | ⟨hl, _⟩ <;> linarith)
  · rcases hl with hl | ⟨hl, hb⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩

/-- Stable partitions turn the latest-past-cover bound into exclusion of every
past witness, including witnesses at shared endpoints and singleton pieces. -/
theorem witness_in_suffix (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (c : Clock) (b : Marker) (I : BoundedTimeInterval) (φ : Formula Var)
    (hstable : ∀ j, σ.Stable (P.interval j) φ)
    (hpast : PastSeparated σ P α k hk c b I φ)
    (t : ℝ) (ht : (P.interval ⟨k.1, hk⟩).left - (α c : ℝ) <[b] t)
    (w : σ.Time) (hw : w.1 ∈ (I : TimeInterval).translate t) (hwφ : (σ, w) ⊨ φ) :
    InCurrentSuffix (P.interval ⟨k.1, hk⟩) w.1 := by
  classical
  let i : Fin P.size := ⟨k.1, hk⟩
  by_contra hs
  have hwD : w.1 ∈ ⋃ j, (P.interval j).carrier := P.covers.symm ▸ w.2
  obtain ⟨j, hwj⟩ := Set.mem_iUnion.1 hwD
  have hji : j < i := by
    by_contra hn
    have hij : i ≤ j := le_of_not_gt hn
    rcases hij.eq_or_lt with he | hlt
    · subst j
      exact hs hwj.1
    · have hord := P.ordered hlt
      have hwl : (P.interval i).right ≤ w.1 :=
        hord.trans (MarkedInterval.left_le_of_mem hwj)
      rcases (MarkedInterval.nonempty_iff (P.interval i)).1 (P.nonempty i) with hlen | ⟨he, hm⟩
      · exact hs (Or.inl (hlen.trans_le hwl))
      · have hle : (P.interval i).left ≤ w.1 := he.le.trans hwl
        rcases hle.lt_or_eq with hlt | heq
        · exact hs (Or.inl hlt)
        · exact hs (Or.inr ⟨heq, ((Marker.includes_conj _ _).1 hm).1⟩)
  have hj : j ∈ pastTrue σ P k φ := (mem_pastTrue σ P k φ j).2
    ⟨hji, fun v hv => (hstable j w v hwj hv).1 hwφ⟩
  let m := (pastTrue σ P k φ).max' ⟨j, hj⟩
  have hm : m ∈ pastTrue σ P k φ := Finset.max'_mem _ _
  have hmax : ∀ l ∈ pastTrue σ P k φ, l ≤ m := fun l hl => Finset.le_max' _ l hl
  have hjm := hmax j hj
  have hwm : w.1 ≤ (P.interval m).right := by
    rcases hjm.eq_or_lt with he | hlt
    · exact he ▸ MarkedInterval.le_right_of_mem hwj
    · exact (MarkedInterval.le_right_of_mem hwj).trans
        ((P.ordered hlt).trans (P.left_le_right m))
  have hinc : w.1 = (P.interval m).right → (P.interval m).rightBoundary.Includes := by
    intro he
    rcases hjm.eq_or_lt with hjm | hjm
    · have hwm : w.1 ∈ P.interval m := hjm ▸ hwj
      rcases hwm.2 with hh | ⟨_, hm⟩
      · exact (lt_irrefl _ (he ▸ hh)).elim
      · exact hm
    · have hml : (P.interval m).right ≤ (P.interval m).left := by
        rw [← he]
        exact (MarkedInterval.le_right_of_mem hwj).trans (P.ordered hjm)
      have heq := le_antisymm (P.left_le_right m) hml
      rcases (MarkedInterval.nonempty_iff (P.interval m)).1 (P.nonempty m) with hlt | ⟨_, hm⟩
      · exact (not_lt_of_ge hml hlt).elim
      · exact ((Marker.includes_conj _ _).1 hm).2
  have hbound := hpast m hm hmax
  have hdelay : I.lower ≤ w.1 - t := hw.1
  rcases hbound with hbnd | ⟨hbnd, hmarker⟩
  · rcases ht with ht | ⟨ht, _⟩ <;> dsimp [i] at * <;> linarith
  · rcases ht with ht | ⟨ht, hb⟩
    · dsimp [i] at *; linarith
    · have heq : w.1 = (P.interval m).right := by dsimp [i] at *; linarith
      exact (Marker.includes_complement _).1
        ((Marker.includes_imp _ _).1 hmarker hb) (hinc heq)

/-- Predicate satisfaction agrees with residual satisfaction under the
predicate invariant and stability for the predicate's formula. -/
theorem predicate_iff_residual (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (hk : k.1 < P.size)
    (p : IntervalPredicate Clock Var) (hi : Invariant σ P α k hk p)
    (hst : σ.StablePartition p.formula P) :
    predicateSatisfies σ (P.interval ⟨k.1, hk⟩) α p ↔
      IntervalPredicate.Satisfies σ (P.interval ⟨k.1, hk⟩) α p := by
  cases p with
  | plain φ => rfl
  | upper c b kind I φ =>
      cases kind with
      | always =>
          constructor
          · exact fun h t ht _ => h t ht
          · exact fun h t ht => h t ht (always_safe _ α c b I hi rfl rfl ht)
      | eventually =>
          constructor
          · intro h t ht
            have hstable : ∀ j, σ.Stable (P.interval j) φ :=
              fun j => hst j φ (.until_right (.refl φ))
            let T := (scope (P.interval ⟨k.1, hk⟩) α (.upper c b .eventually I φ)).carrier
            obtain ⟨j, w, hwj, hw, htrue⟩ :=
              eventually_stable_scope_cover σ P T (.bounded I) φ hstable h t ht
            have hwφ := htrue w hwj
            exact ⟨w, hw, witness_in_suffix σ P α k hk c b I φ
              hstable hi.2.2 t ht.1 w hw hwφ, hwφ⟩
          · intro h t ht
            obtain ⟨w, hw, _, hwφ⟩ := h t ht
            exact ⟨w, hw, hwφ⟩
  | bounded c d b q kind I φ =>
      cases kind with
      | always =>
          constructor
          · exact fun h t ht _ => h t ht
          · exact fun h t ht => h t ht (always_safe _ α c b I hi.1 rfl rfl ht)
      | eventually =>
          constructor
          · intro h t ht
            have hstable : ∀ j, σ.Stable (P.interval j) φ :=
              fun j => hst j φ (.until_right (.refl φ))
            let T := (scope (P.interval ⟨k.1, hk⟩) α (.bounded c d b q .eventually I φ)).carrier
            obtain ⟨j, w, hwj, hw, htrue⟩ :=
              eventually_stable_scope_cover σ P T (.bounded I) φ hstable h t ht
            have hwφ := htrue w hwj
            exact ⟨w, hw, witness_in_suffix σ P α k hk c b I φ
              hstable hi.2.2 t ht.1 w hw hwφ, hwφ⟩
          · intro h t ht
            obtain ⟨w, hw, _, hwφ⟩ := h t ht
            exact ⟨w, hw, hwφ⟩

end STLTableau
