import STLTableaux.Finiteness.Bounds.AlwaysTruthBlocks

/-! Bounds the number of temporal truth intervals by counting their distinct
endpoints. Used in the proof of Lemma 4.36. -/
namespace STLTableau.Section4.Finiteness
open Finiteness.Alternation
variable {Var : Type*}

 def boundedTemporal (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) : Formula Var :=
  match kind with
  | .always => .always (.bounded I) φ
  | .eventually => .eventually (.bounded I) φ

/-- Uninterrupted truth on the whole closed interval between two origins. -/
 def SameTruthBlock (σ : FiniteSignal Var) (θ : Formula Var) (x y : σ.Time) : Prop :=
  ∀ z : σ.Time, min x.val y.val ≤ z.val → z.val ≤ max x.val y.val → σ.Satisfies θ z

 theorem false_between_truth_blocks (σ : FiniteSignal Var) (θ : Formula Var)
    (x y : σ.Time) (hxy : x.val < y.val) (hx : σ.Satisfies θ x) (hy : σ.Satisfies θ y)
    (hne : ¬ SameTruthBlock σ θ x y) :
    ∃ z : σ.Time, x.val < z.val ∧ z.val < y.val ∧ ¬ σ.Satisfies θ z := by
  classical
  unfold SameTruthBlock at hne
  push Not at hne
  obtain ⟨z, hl, hr, hz⟩ := hne
  rw [min_eq_left hxy.le] at hl
  rw [max_eq_right hxy.le] at hr
  have hxz : x.val ≠ z.val := by
    intro he
    exact hz ((Subtype.ext he : x = z) ▸ hx)
  have hzy : z.val ≠ y.val := by
    intro he
    exact hz ((Subtype.ext he : z = y).symm ▸ hy)
  exact ⟨z, lt_of_le_of_ne hl hxz, lt_of_le_of_ne hr hzy, hz⟩

 theorem finite_temporal_truth_blocks_bound (σ : FiniteSignal Var)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var) (u v : ℝ)
    (T : Finset σ.Time) (hw : ∀ x ∈ T, u ≤ x.val ∧ x.val ≤ v)
    (ht : ∀ x ∈ T, σ.Satisfies (boundedTemporal kind I φ) x)
    (hb : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      ¬ SameTruthBlock σ (boundedTemporal kind I φ) x y) :
    T.card ≤ ⌈(v-u)/(I.upper-I.lower)⌉₊ + 2 := by
  classical
  by_cases hz : T.card = 0
  · rw [hz]; omega
  have hp : 0 < T.card := Nat.pos_of_ne_zero hz
  let e := T.orderIsoOfFin rfl
  let index (i : Nat) : Fin T.card := ⟨i % T.card, Nat.mod_lt _ hp⟩
  let t (i : Nat) : σ.Time := (e (index i)).val
  let n := T.card - 1
  have hm : ∀ i, t i ∈ T := fun i => (e (index i)).property
  have ho : ∀ i < n, (t i).val < (t (i+1)).val := by
    intro i hi
    apply e.strictMono
    change i % T.card < (i+1) % T.card
    rw [Nat.mod_eq_of_lt (by dsimp [n] at hi; omega),
      Nat.mod_eq_of_lt (by dsimp [n] at hi; omega)]
    omega
  have sep (i : Nat) (hi : i < n) :
      ∃ z : σ.Time, (t i).val < z.val ∧ z.val < (t (i+1)).val ∧
        ¬ σ.Satisfies (boundedTemporal kind I φ) z := by
    apply false_between_truth_blocks σ _ _ _ (ho i hi) (ht _ (hm i)) (ht _ (hm (i+1)))
    apply hb _ (hm i) _ (hm (i+1))
    intro he
    have hh := ho i hi
    rw [he] at hh
    exact (lt_irrefl _ hh)
  let z : Nat → σ.Time := fun i => if hi : i < n then Classical.choose (sep i hi) else t 0
  have hs (i : Nat) (hi : i < n) := Classical.choose_spec (sep i hi)
  have hzdef (i : Nat) (hi : i < n) : z i = Classical.choose (sep i hi) := dif_pos hi
  have hbetween : ∀ i < n, (t i).val < (z i).val ∧ (z i).val < (t (i+1)).val := by
    intro i hi
    rw [hzdef i hi]
    exact ⟨(hs i hi).1, (hs i hi).2.1⟩
  have hfalse : ∀ i < n, ¬ σ.Satisfies (boundedTemporal kind I φ) (z i) := by
    intro i hi
    rw [hzdef i hi]
    exact (hs i hi).2.2
  have hcount : n+1 ≤ ⌈(v-u)/(I.upper-I.lower)⌉₊ + 2 := by
    cases kind with
    | always =>
      have h := always_separated_true_samples_bound σ I φ u v n t z
        (fun i _ => hw _ (hm i)) (fun i _ => ht _ (hm i)) hbetween hfalse
      exact h.trans (by omega)
    | eventually =>
      exact eventually_separated_samples_bound σ I φ u v n t z
        (fun i _ => hw _ (hm i)) (fun i _ => ht _ (hm i)) hbetween hfalse
  dsimp [n] at hcount
  omega

/-- A finite family contains at most one representative of each actual maximal
truth block. Cofinality and upper bounds describe its right endpoint, allowing
open endpoints. There is no cardinality assumption in these hypotheses. -/
 theorem ended_truth_blocks_bound {Block : Type*} (σ : FiniteSignal Var)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (T : Finset Block) (source : Block → Set σ.Time) (endpoint : Block → ℝ)
    (u : ℝ) (hend : ∀ p ∈ T, u-I.upper ≤ endpoint p ∧ endpoint p ≤ u)
    (hinj : Set.InjOn endpoint (T : Set Block))
    (htrue : ∀ p ∈ T, ∀ x ∈ source p, σ.Satisfies (boundedTemporal kind I φ) x)
    (hupper : ∀ p ∈ T, ∀ x ∈ source p, x.val ≤ endpoint p)
    (hcofinal : ∀ p ∈ T, ∀ v < endpoint p, ∃ x ∈ source p, v < x.val)
    (hblocks : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ x ∈ source p, ∀ y ∈ source q,
      ¬ SameTruthBlock σ (boundedTemporal kind I φ) x y) :
    T.card ≤ ⌈I.upper/(I.upper-I.lower)⌉₊ + 3 := by
  classical
  let A := T.filter (fun p => u-I.upper < endpoint p)
  have pick_exists : ∀ p : A, ∃ x ∈ source p.val, u-I.upper < x.val := by
    intro p
    exact hcofinal p.val (Finset.mem_filter.mp p.property).1 _
      (Finset.mem_filter.mp p.property).2
  choose pick hp hw using pick_exists
  have hi : Function.Injective pick := by
    intro p q he
    apply Subtype.ext
    by_contra hne
    apply hblocks p.val (Finset.mem_filter.mp p.property).1 q.val
      (Finset.mem_filter.mp q.property).1 hne (pick p) (hp p) (pick q) (hp q)
    intro z hl hr
    simp only [← he, min_self, max_self] at hl hr
    have hz : z = pick p := Subtype.ext (le_antisymm hr hl)
    rw [hz]
    exact htrue p.val (Finset.mem_filter.mp p.property).1 _ (hp p)
  let samples := A.attach.image pick
  have hcard : samples.card = A.card := by
    rw [Finset.card_image_of_injective _ hi, Finset.card_attach]
  have hb := finite_temporal_truth_blocks_bound σ kind I φ (u-I.upper) u samples
    (by
      intro x hx
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨(hw p).le, (hupper p.val (Finset.mem_filter.mp p.property).1 _ (hp p)).trans
        (hend p.val (Finset.mem_filter.mp p.property).1).2⟩)
    (by
      intro x hx
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      exact htrue p.val (Finset.mem_filter.mp p.property).1 _ (hp p))
    (by
      intro x hx y hy hne
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
      apply hblocks p.val (Finset.mem_filter.mp p.property).1 q.val
        (Finset.mem_filter.mp q.property).1
      · intro he
        exact hne (congrArg pick (Subtype.ext he))
      · exact hp p
      · exact hp q)
  rw [hcard, show u-(u-I.upper) = I.upper by ring] at hb
  have hrest : (T \ A).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have pT := (Finset.mem_sdiff.mp hp).1
    have qT := (Finset.mem_sdiff.mp hq).1
    apply hinj pT qT
    have hp' : endpoint p ≤ u-I.upper := by
      by_contra h
      exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨pT, by linarith⟩)
    have hq' : endpoint q ≤ u-I.upper := by
      by_contra h
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨qT, by linarith⟩)
    linarith [(hend p pT).1, (hend q qT).1]
  have hsub : A ⊆ T := Finset.filter_subset _ _
  have he := Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- The stronger ceiling bound fits the conservative endpoint budget. -/
theorem endpoint_bound_le_conservative_budget (I : BoundedTimeInterval) :
    ⌈I.upper/(I.upper-I.lower)⌉₊ + 3 ≤
      2 * ⌊I.upper/(I.upper-I.lower)⌋₊ + 7 := by
  have h := Nat.ceil_le_floor_add_one (I.upper/(I.upper-I.lower))
  omega

end STLTableau.Section4.Finiteness
