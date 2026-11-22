import STLTableaux.Syntax.InputSyntax
import STLTableaux.Semantics.Stability.FiniteFamilyRefinement
import STLTableaux.Semantics.Partitions.PointOpenPartition

/-! Finite variability of normalized formulas from their atomic observations. -/
namespace STLTableau.FiniteSignal

open scoped STL
variable {Var : Type*} {σ : FiniteSignal Var}

private def cutBoundary (x : ℝ) : Fin 3 → ℝ := ![0, x, σ.horizon]

private theorem cutBoundary_strict {x : ℝ} (hx : 0 < x) (hτ : x < σ.horizon) :
    StrictMono (cutBoundary (σ := σ) x) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [cutBoundary, σ.horizon_pos]

private def baseBoundary (σ : FiniteSignal Var) : Fin 2 → ℝ := ![0, σ.horizon]

private theorem baseBoundary_strict (σ : FiniteSignal Var) : StrictMono (baseBoundary σ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [baseBoundary, σ.horizon_pos]

private def basePartition (σ : FiniteSignal Var) : IntervalPartition σ.domain :=
  IntervalPartition.pointOpenPartition (baseBoundary σ) (baseBoundary_strict σ)

private def cutPartition (x : ℝ) (hx : 0 < x) (hτ : x < σ.horizon) :
    IntervalPartition σ.domain :=
  IntervalPartition.pointOpenPartition (cutBoundary x) (cutBoundary_strict hx hτ)

private def ConstOn (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (p : ℝ → Prop) : Prop :=
  ∀ i u v, u ∈ (P.interval i).carrier → v ∈ (P.interval i).carrier → (p u ↔ p v)

private theorem ConstOn.refine {p : ℝ → Prop} {P Q : IntervalPartition σ.domain}
    (h : ConstOn σ P p) (r : Q ⊑ P) : ConstOn σ Q p := by
  intro i u v hu hv
  obtain ⟨j, hj⟩ := r i
  exact h j u v (hj hu) (hj hv)

/-- A cut separates the points strictly below it, at it, and strictly above it. -/
private theorem exists_cut (x : ℝ) : ∃ P : IntervalPartition σ.domain,
    ConstOn σ P (· < x) ∧ ConstOn σ P (· = x) := by
  by_cases h₀ : x ≤ 0
  · refine ⟨basePartition σ, ?_, ?_⟩
    · intro i u v hu hv
      change u ∈ (IntervalPartition.pointOpenPiece (baseBoundary σ) i).carrier at hu
      change v ∈ (IntervalPartition.pointOpenPiece (baseBoundary σ) i).carrier at hv
      fin_cases i <;> simp [IntervalPartition.pointOpenPiece_carrier, baseBoundary] at hu hv
      · simp [hu, hv]
      · constructor <;> intro h <;> linarith [hu.1, hv.1]
    · intro i u v hu hv
      change u ∈ (IntervalPartition.pointOpenPiece (baseBoundary σ) i).carrier at hu
      change v ∈ (IntervalPartition.pointOpenPiece (baseBoundary σ) i).carrier at hv
      fin_cases i <;> simp [IntervalPartition.pointOpenPiece_carrier, baseBoundary] at hu hv
      · simp [hu, hv]
      · constructor <;> intro h <;> linarith [hu.1, hv.1]
  · by_cases hτ : x < σ.horizon
    · refine ⟨cutPartition x (lt_of_not_ge h₀) hτ, ?_, ?_⟩
      all_goals
        intro i u v hu hv
        change u ∈ (IntervalPartition.pointOpenPiece (cutBoundary x) i).carrier at hu
        change v ∈ (IntervalPartition.pointOpenPiece (cutBoundary x) i).carrier at hv
        fin_cases i <;> simp [IntervalPartition.pointOpenPiece_carrier, cutBoundary] at hu hv
        all_goals first
          | (simp [hu, hv]; done)
          | constructor <;> intro h <;> linarith [hu.1, hu.2, hv.1, hv.2]
    · refine ⟨basePartition σ, ?_, ?_⟩
      all_goals
        intro i u v hu hv
        have hd (z : ℝ) (hz : z ∈ ((basePartition σ).interval i).carrier) : z < σ.horizon := by
          have hz' : z ∈ σ.domain := by
            rw [← (basePartition σ).covers]
            exact Set.mem_iUnion.mpr ⟨i, hz⟩
          exact hz'.2
        constructor <;> intro h <;> linarith [hd u hu, hd v hv]

private theorem exists_common_constOn {ι : Type*} [Fintype ι]
    (p : ι → ℝ → Prop) (hp : ∀ i, ∃ P : IntervalPartition σ.domain, ConstOn σ P (p i))
    (P₀ : IntervalPartition σ.domain) :
    ∃ R : IntervalPartition σ.domain, R.FinerThan P₀ ∧ ∀ i, ConstOn σ R (p i) := by
  classical
  choose Ps hs using hp
  obtain ⟨R, hR, hRs, _⟩ := P₀.exists_common_refinement_finset (Finset.univ.image Ps)
  exact ⟨R, hR, fun i => (hs i).refine (hRs (Ps i) (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))⟩

/-- A convex truth set requires at most two cuts, retaining each endpoint as a
singleton so its truth need not agree with either adjacent interval. -/
private theorem exists_constOn_of_convex (p : ℝ → Prop)
    (hc : ∀ ⦃x y z⦄, x ≤ z → z ≤ y → p x → p y → p z) :
    ∃ P : IntervalPartition σ.domain, ConstOn σ P p := by
  let S := {u | u ∈ σ.domain ∧ p u}
  by_cases hS : S.Nonempty
  · have hLo : BddBelow S := ⟨0, fun _ h => h.1.1⟩
    have hHi : BddAbove S := ⟨σ.horizon, fun _ h => h.1.2.le⟩
    let a := sInf S
    let b := sSup S
    have hInside (z : ℝ) (haz : a < z) (hzb : z < b) : p z := by
      obtain ⟨x, hx, hxz⟩ := exists_lt_of_csInf_lt hS haz
      obtain ⟨y, hy, hzy⟩ := exists_lt_of_lt_csSup hS hzb
      exact hc hxz.le hzy.le hx.2 hy.2
    obtain ⟨P, hPa, hPa'⟩ := exists_cut (σ := σ) a
    obtain ⟨Q, hQb, hQb'⟩ := exists_cut (σ := σ) b
    obtain ⟨R, hRP, hRQ, _⟩ := P.exists_common_refinement Q
    refine ⟨R, ?_⟩
    intro i u v hu hv
    have inDomain (w : ℝ) (hw : w ∈ (R.interval i).carrier) : w ∈ σ.domain := by
      rw [← R.covers]
      exact Set.mem_iUnion.mpr ⟨i, hw⟩
    have step (x y : ℝ) (hx : x ∈ (R.interval i).carrier) (hy : y ∈ (R.interval i).carrier)
        (hpx : p x) : p y := by
      have hxS : x ∈ S := ⟨inDomain x hx, hpx⟩
      have hax : a ≤ x := csInf_le hLo hxS
      have hxb : x ≤ b := le_csSup hHi hxS
      by_cases he : x = a
      · exact (he.trans ((hPa'.refine hRP i x y hx hy).mp he).symm) ▸ hpx
      by_cases he' : x = b
      · exact (he'.trans ((hQb'.refine hRQ i x y hx hy).mp he').symm) ▸ hpx
      apply hInside
      · have hn := (hPa.refine hRP i x y hx hy).not.mp (not_lt_of_ge hax)
        have hne := (hPa'.refine hRP i x y hx hy).not.mp he
        exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
      · exact (hQb.refine hRQ i x y hx hy).mp (lt_of_le_of_ne hxb he')
    exact ⟨step u v hu hv, step v u hv hu⟩
  · refine ⟨basePartition σ, ?_⟩
    intro i u v hu hv
    have hd (z : ℝ) (hz : z ∈ ((basePartition σ).interval i).carrier) : z ∈ σ.domain := by
      rw [← (basePartition σ).covers]
      exact Set.mem_iUnion.mpr ⟨i, hz⟩
    exact ⟨fun h => (hS ⟨u, hd u hu, h⟩).elim, fun h => (hS ⟨v, hd v hv, h⟩).elim⟩

private theorem interval_between (J : MarkedInterval) {x z y : ℝ}
    (hx : x ∈ J.carrier) (hy : y ∈ J.carrier) (hxz : x ≤ z) (hzy : z ≤ y) :
    z ∈ J.carrier := by
  rcases eq_or_lt_of_le hxz with rfl | hleft
  · exact hx
  rcases eq_or_lt_of_le hzy with rfl | hright
  · exact hy
  exact ⟨Or.inl ((MarkedInterval.left_le_of_mem hx).trans_lt hleft),
    Or.inl (hright.trans_le (MarkedInterval.le_right_of_mem hy))⟩

private def origin (I : TimeInterval) (J : MarkedInterval) (t : ℝ) : Prop :=
  ∃ w ∈ J.carrier, w ∈ I.translate t

private theorem origin_convex (I : TimeInterval) (J : MarkedInterval) {x y z : ℝ}
    (hxz : x ≤ z) (hzy : z ≤ y) (hx : origin I J x) (hy : origin I J y) :
    origin I J z := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvy⟩ := hy
  cases I with
  | unbounded a =>
      change (a : ℝ) ≤ v - y at hvy
      exact ⟨v, hv, show (a : ℝ) ≤ v - z by linarith⟩
  | bounded I =>
      change I.lower ≤ u - x ∧ u - x ≤ I.upper at hux
      change I.lower ≤ v - y ∧ v - y ≤ I.upper at hvy
      by_cases h : z + I.lower ≤ u
      · exact ⟨u, hu, show I.lower ≤ u - z ∧ u - z ≤ I.upper by constructor <;> linarith [hux.2]⟩
      · refine ⟨z + I.lower, interval_between J hu hv (by linarith) (by linarith [hvy.1]), ?_⟩
        change I.lower ≤ z + I.lower - z ∧ z + I.lower - z ≤ I.upper
        constructor <;> linarith [I.nonSingular]

private theorem fv_truth (σ : FiniteSignal Var) : σ.HasFiniteVariability .truth := by
  refine ⟨basePartition σ, fun i χ hχ => ?_⟩
  cases hχ
  exact fun _ _ _ _ => Iff.rfl

private theorem fv_neg {φ : Formula Var} (h : σ.HasFiniteVariability φ) :
    σ.HasFiniteVariability (.neg φ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, fun i χ hχ => ?_⟩
  cases hχ with
  | refl => exact fun u v hu hv => not_congr ((hP i).stable u v hu hv)
  | neg hχ => exact hP i _ hχ

/-- The true origins are the union of the origin intervals of all true operand
cells. Refining for those origin intervals also preserves the operand partition. -/
private theorem fv_eventually (I : TimeInterval) {φ : Formula Var}
    (h : σ.HasFiniteVariability φ) : σ.HasFiniteVariability (φ.eventually I) := by
  classical
  obtain ⟨P, hP⟩ := h
  have hOrigin (i : Fin P.size) :
      ∃ Q : IntervalPartition σ.domain, ConstOn σ Q (origin I (P.interval i)) :=
    exists_constOn_of_convex _ (fun _ _ _ => origin_convex I (P.interval i))
  obtain ⟨Q, hQP, hQ⟩ := exists_common_constOn _ hOrigin P
  have witnessEq (t : σ.Time) : σ.Satisfies (φ.eventually I) t ↔
      ∃ i : Fin P.size, origin I (P.interval i) t.1 ∧
        ∀ w : σ.Time, w.1 ∈ (P.interval i).carrier → σ.Satisfies φ w := by
    rw [σ.satisfies_eventually_iff I φ t]
    constructor
    · rintro ⟨w, htime, hw⟩
      have hd : w.1 ∈ ⋃ i, (P.interval i).carrier := P.covers.symm ▸ w.property
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hd
      exact ⟨i, ⟨w.1, hi, htime⟩, fun v hv => ((hP i).stable w v hi hv).mp hw⟩
    · rintro ⟨i, ⟨w, hw, htime⟩, ht⟩
      have hd : w ∈ σ.domain := P.covers ▸ Set.mem_iUnion.mpr ⟨i, hw⟩
      exact ⟨⟨w, hd⟩, htime, ht ⟨w, hd⟩ hw⟩
  refine ⟨Q, fun i χ hχ => ?_⟩
  change Formula.IsSubformula χ (.until I .truth φ) at hχ
  cases hχ with
  | until_right hχ => exact hP.of_finer hQP i _ hχ
  | until_left hχ =>
    cases hχ
    exact fun _ _ _ _ => Iff.rfl
  | refl =>
    intro u v hu hv
    change σ.Satisfies (φ.eventually I) u ↔ σ.Satisfies (φ.eventually I) v
    rw [witnessEq u, witnessEq v]
    exact exists_congr fun j => and_congr (hQ j i u.1 v.1 hu hv) Iff.rfl

private theorem stable_untimedUntil {J : MarkedInterval} {φ ψ : Formula Var}
    (hφ : σ.Stable J φ) (hψ : σ.Stable J ψ) : σ.Stable J (φ.untimedUntil ψ) := by
  suffices ordered : ∀ (x y : σ.Time), x.1 ∈ J → y.1 ∈ J → x.1 ≤ y.1 →
      (σ.Satisfies (φ.untimedUntil ψ) x ↔ σ.Satisfies (φ.untimedUntil ψ) y) by
    intro x y hx hy
    rcases le_total x.1 y.1 with h | h
    · exact ordered x y hx hy h
    · exact (ordered y x hy hx h).symm
  intro x y hx hy hxy
  constructor
  · rintro ⟨w, hw, hψw, hp⟩
    have hxw : x.1 ≤ w.1 := TimeInterval.le_of_mem_translate hw
    by_cases hyw : y.1 ≤ w.1
    · refine ⟨w, ?_, hψw, fun t hyt htw => hp t (hxy.trans hyt) htw⟩
      change (0 : ℝ) ≤ w.1 - y.1
      linarith
    · have hφy := (hφ x y hx hy).mp (hp x le_rfl hxw)
      have hwJ := interval_between J hx hy hxw (le_of_not_ge hyw)
      exact σ.satisfies_untimedUntil_of_and φ ψ y hφy ((hψ w y hwJ hy).mp hψw)
  · rintro ⟨w, hw, hψw, hp⟩
    have hyw : y.1 ≤ w.1 := TimeInterval.le_of_mem_translate hw
    refine ⟨w, ?_, hψw, ?_⟩
    · change (0 : ℝ) ≤ w.1 - x.1
      linarith
    · intro t hxt htw
      by_cases hyt : y.1 ≤ t.1
      · exact hp t hyt htw
      · exact (hφ y t hy (interval_between J hx hy hxt (le_of_not_ge hyt))).mp (hp y le_rfl hyw)

private theorem fv_untimedUntil {φ ψ : Formula Var}
    (hφ : σ.HasFiniteVariability φ) (hψ : σ.HasFiniteVariability ψ) :
    σ.HasFiniteVariability (φ.untimedUntil ψ) := by
  obtain ⟨P, hP⟩ := hφ
  obtain ⟨Q, hQ⟩ := hψ
  obtain ⟨R, _, _, hRφ, hRψ⟩ := exists_common_stable_refinement hP hQ
  refine ⟨R, fun i χ hχ => ?_⟩
  change Formula.IsSubformula χ (.until (.unbounded 0) φ ψ) at hχ
  cases hχ with
  | refl => exact stable_untimedUntil (hRφ i).stable (hRψ i).stable
  | until_left hχ => exact hRφ i _ hχ
  | until_right hχ => exact hRψ i _ hχ

end STLTableau.FiniteSignal

namespace STLTableau.Formula

open STLTableau.FiniteSignal

variable {Var : Type*}

/-- Fully stable partitions for the atomic subformulas suffice for every
formula in the normalized input grammar. -/
theorem NormalizedReady.hasFiniteVariability_of_atoms {φ : Formula Var} (ready : φ.NormalizedReady)
    {σ : FiniteSignal Var}
    (atoms : ∀ a, IsSubformula (.atom a) φ → σ.HasFiniteVariability (.atom a)) :
    σ.HasFiniteVariability φ := by
  induction ready with
  | truth => exact fv_truth σ
  | atom a => exact atoms a (.refl _)
  | and _ _ ihφ ihψ =>
    exact (ihφ fun a ha => atoms a (.and_left ha)).and (ihψ fun a ha => atoms a (.and_right ha))
  | or _ _ ihφ ihψ =>
    exact fv_neg ((fv_neg (ihφ fun a ha => atoms a (.neg (.and_left (.neg ha))))).and
      (fv_neg (ihψ fun a ha => atoms a (.neg (.and_right (.neg ha))))))
  | «until» _ _ ihφ ihψ =>
    exact fv_untimedUntil (ihφ fun a ha => atoms a (.until_left ha))
      (ihψ fun a ha => atoms a (.until_right ha))
  | release _ _ ihφ ihψ =>
    exact fv_neg (fv_untimedUntil (fv_neg (ihφ fun a ha => atoms a (.neg (.until_left (.neg ha)))))
      (fv_neg (ihψ fun a ha => atoms a (.neg (.until_right (.neg ha))))))
  | eventually I _ ih => exact fv_eventually I (ih fun a ha => atoms a (.until_right ha))
  | always I _ ih =>
    exact fv_neg (fv_eventually I (fv_neg (ih fun a ha => atoms a (.neg (.until_right (.neg ha))))))

end STLTableau.Formula
