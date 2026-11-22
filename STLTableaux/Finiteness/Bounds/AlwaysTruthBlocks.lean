import STLTableaux.Finiteness.Bounds.BoundedAlternation
import Mathlib.Data.Finset.Sort

/-! Original G truth blocks: adjacent true pieces belong to the same block.
This counts distinct blocks of origin times, not current post-check scopes.
No tableau state or next component is constructed or changed. -/
namespace STLTableau.Section4.Finiteness.Alternation
variable {Var : Type*}

/-- Two origins belong to one uninterrupted G-true block precisely when
all intermediate origins are true, including the two origins themselves. -/
def SameAlwaysTruthBlock (σ : FiniteSignal Var) (I : BoundedTimeInterval)
    (φ : Formula Var) (x y : σ.Time) : Prop :=
  ∀ z : σ.Time, min x.1 y.1 ≤ z.1 → z.1 ≤ max x.1 y.1 →
    σ.Satisfies (Formula.always (.bounded I) φ) z

/-- Distinct true blocks have a genuine false origin strictly between them. -/
theorem false_between_distinct_truth_blocks (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (x y : σ.Time)
    (hxy : x.1 < y.1)
    (hx : σ.Satisfies (Formula.always (.bounded I) φ) x)
    (hy : σ.Satisfies (Formula.always (.bounded I) φ) y)
    (hne : ¬ SameAlwaysTruthBlock σ I φ x y) :
    ∃ z : σ.Time, x.1 < z.1 ∧ z.1 < y.1 ∧
      ¬ σ.Satisfies (Formula.always (.bounded I) φ) z := by
  classical
  unfold SameAlwaysTruthBlock at hne
  push Not at hne
  obtain ⟨z, hl, hr, hz⟩ := hne
  rw [min_eq_left hxy.le] at hl
  rw [max_eq_right hxy.le] at hr
  have hxl : x.1 ≠ z.1 := by
    intro he
    have he : x = z := Subtype.ext he
    exact hz (he ▸ hx)
  have hyr : z.1 ≠ y.1 := by
    intro he
    have he : z = y := Subtype.ext he
    exact hz (he.symm ▸ hy)
  exact ⟨z, lt_of_le_of_ne hl hxl, lt_of_le_of_ne hr hyr, hz⟩

/-- A finite family containing at most one origin from each original true
block has at most ceil(window length / timing width)+1 members. Block
separation, not separation of checking regions, is the premise. -/
theorem finite_always_truth_blocks_bound (σ : FiniteSignal Var)
    (I : BoundedTimeInterval) (φ : Formula Var) (u v : ℝ)
    (T : Finset σ.Time)
    (hwindow : ∀ x ∈ T, u ≤ x.1 ∧ x.1 ≤ v)
    (htrue : ∀ x ∈ T, σ.Satisfies (Formula.always (.bounded I) φ) x)
    (hblocks : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ SameAlwaysTruthBlock σ I φ x y) :
    T.card ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ + 1 := by
  classical
  by_cases hz : T.card = 0
  · rw [hz]
    exact Nat.zero_le _
  have hp : 0 < T.card := Nat.pos_of_ne_zero hz
  let e := T.orderIsoOfFin rfl
  let index (i : ℕ) : Fin T.card := ⟨i % T.card, Nat.mod_lt _ hp⟩
  let t (i : ℕ) : σ.Time := (e (index i)).val
  let n := T.card - 1
  have hmem : ∀ i, t i ∈ T := fun i => (e (index i)).property
  have ho : ∀ i < n, (t i).1 < (t (i + 1)).1 := by
    intro i hi
    have hi0 : i < T.card := by dsimp [n] at hi; omega
    have hi1 : i + 1 < T.card := by dsimp [n] at hi; omega
    have hidx : index i < index (i + 1) := by
      change i % T.card < (i + 1) % T.card
      rw [Nat.mod_eq_of_lt hi0, Nat.mod_eq_of_lt hi1]
      omega
    exact e.strictMono hidx
  have hg : ∀ i < n, I.upper - I.lower ≤ (t (i + 1)).1 - (t i).1 := by
    intro i hi
    have hne : t i ≠ t (i + 1) := by
      intro he
      have hh := ho i hi
      rw [he] at hh
      exact (lt_irrefl _ hh)
    obtain ⟨z, hl, hr, hf⟩ := false_between_distinct_truth_blocks σ I φ _ _
      (ho i hi) (htrue _ (hmem i)) (htrue _ (hmem (i + 1)))
      (hblocks _ (hmem i) _ (hmem (i + 1)) hne)
    exact (always_true_gap σ I φ _ z _ hl hr
      (htrue _ (hmem i)) hf (htrue _ (hmem (i + 1)))).le
  have hspan := span_of_gaps (fun i => (t i).1) (I.upper - I.lower) n hg
  have hw : 0 < I.upper - I.lower := sub_pos.mpr I.nonSingular
  have hn : (n : ℝ) ≤ (v - u) / (I.upper - I.lower) := by
    apply (le_div_iff₀ hw).mpr
    linarith [(hwindow _ (hmem 0)).1, (hwindow _ (hmem n)).2]
  have hceil := Nat.le_ceil ((v - u) / (I.upper - I.lower))
  have hnat : n ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ := by
    exact_mod_cast (le_trans hn hceil)
  dsimp [n] at hnat
  omega

/-- A family already represents original true scopes: every represented
origin is G-true, and two labels whose source scopes meet the same uninterrupted
true block are the same label. These are source scopes before checks, not
current clock-evaluated scopes. No cardinal bound or state-existence field
is part of the condition. -/
structure OriginalScopeRepresentative {Label : Type*}
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (T : Finset Label) (source : Label → Set σ.Time) : Prop where
  truth : ∀ p ∈ T, ∀ x ∈ source p,
    σ.Satisfies (Formula.always (.bounded I) φ) x
  unique : ∀ p ∈ T, ∀ q ∈ T, ∀ x ∈ source p, ∀ y ∈ source q,
    SameAlwaysTruthBlock σ I φ x y → p = q

/-- Existing labels, including checked residuals, can be counted through
original source scopes once each such scope has a true origin in the active
window. This theorem does not assert that a given path supplies those scopes. -/
theorem original_scope_labels_bound {Label : Type*}
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (T : Finset Label) (source : Label → Set σ.Time)
    (hrep : OriginalScopeRepresentative σ I φ T source)
    (u v : ℝ)
    (hwindow : ∀ p ∈ T, ∃ x ∈ source p, u ≤ x.1 ∧ x.1 ≤ v) :
    T.card ≤ ⌈(v - u) / (I.upper - I.lower)⌉₊ + 1 := by
  classical
  have hex : ∀ p : {p // p ∈ T}, ∃ x ∈ source p.val, u ≤ x.1 ∧ x.1 ≤ v := by
    intro p
    exact hwindow p.val p.property
  choose pick hsource hwin using hex
  have hinj : Function.Injective pick := by
    intro p q he
    apply Subtype.ext
    apply hrep.unique p.val p.property q.val q.property (pick p) (hsource p)
      (pick q) (hsource q)
    intro z hl hr
    simp only [← he, min_self, max_self] at hl hr
    have hez : z = pick p := Subtype.ext (le_antisymm hr hl)
    rw [hez]
    exact hrep.truth p.val p.property _ (hsource p)
  let samples := T.attach.image pick
  have hcard : samples.card = T.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hcount := finite_always_truth_blocks_bound σ I φ u v samples
    (by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact hwin p)
    (by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact hrep.truth p.val p.property _ (hsource p))
    (by
      intro x hx y hy hne hsame
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
      have he : p = q := Subtype.ext
        (hrep.unique p.val p.property q.val q.property _ (hsource p) _ (hsource q) hsame)
      exact hne (congrArg pick he))
  rw [hcard] at hcount
  exact hcount

/-- The observation window of length I.upper gives exactly r(I)+1. -/
theorem original_scope_labels_resolution_bound {Label : Type*}
    (σ : FiniteSignal Var) (I : BoundedTimeInterval) (φ : Formula Var)
    (T : Finset Label) (source : Label → Set σ.Time)
    (hrep : OriginalScopeRepresentative σ I φ T source) (now : ℝ)
    (hwindow : ∀ p ∈ T, ∃ x ∈ source p,
      now - I.upper ≤ x.1 ∧ x.1 ≤ now) :
    T.card ≤ ⌈I.upper / (I.upper - I.lower)⌉₊ + 1 := by
  have h := original_scope_labels_bound σ I φ T source hrep (now - I.upper) now hwindow
  have he : now - (now - I.upper) = I.upper := by ring
  rw [he] at h
  exact h

end STLTableau.Section4.Finiteness.Alternation
