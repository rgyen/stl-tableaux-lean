import STLTableaux.Semantics.IntervalSemantics
import STLTableaux.Semantics.Stability.Stability

/-! The checking interval lemmas C.8–C.10 for bounded and unbounded timing
intervals. Satisfaction is evaluated within the finite signal domain. -/
namespace STLTableau
open scoped STL
variable {Var : Type*}

/-- The finite lower endpoint, also for `[a,∞)`. -/
def timingLower : TimeInterval → ℝ
  | .bounded I => I.lower
  | .unbounded a => a

theorem timingLower_le_of_mem (I : TimeInterval) {d : ℝ} (hd : d ∈ I) :
    timingLower I ≤ d := by
  cases I with
  | bounded I => exact hd.1
  | unbounded a => exact hd

/-- The Minkowski difference `K-I`, expressed by its witnesses. -/
def timingDifference (K : Set ℝ) (I : TimeInterval) : Set ℝ :=
  {t | ∃ u ∈ K, u ∈ I.translate t}

/-- Agreement with the set-theoretic Minkowski subtraction in the manuscript. -/
theorem mem_timingDifference_iff {K : Set ℝ} {I : TimeInterval} {t : ℝ} :
    t ∈ timingDifference K I ↔ ∃ u ∈ K, ∃ d ∈ I, t = u - d := by
  constructor
  · rintro ⟨u, hu, hd⟩
    exact ⟨u, hu, u - t, hd, by ring⟩
  · rintro ⟨u, hu, d, hd, rfl⟩
    exact ⟨u, hu, by simpa only [TimeInterval.mem_translate, sub_sub_cancel] using hd⟩

/-- Lemma C.8, including unbounded timing. -/
theorem always_interval_vacuous (σ : FiniteSignal Var) (K : MarkedInterval)
    (I : TimeInterval) (φ : Formula Var)
    (hr : K.right = σ.horizon) (_hopen : K.rightBoundary = ○)
    (hlen : K.right - K.left ≤ timingLower I) :
    ∀ t : σ.Time, t.1 ∈ K → (σ, t) ⊨ □[I] φ := by
  intro t ht
  apply (FiniteSignal.satisfies_always_iff σ I φ t).2
  intro u hu
  have hl := MarkedInterval.left_le_of_mem ht
  have hd := timingLower_le_of_mem I hu
  have huτ := u.2.2
  rw [hr] at hlen
  exfalso
  linarith

/-- Lemma C.9. The shifted set is intersected with
the signal domain through the type of the evaluation time. -/
theorem interval_eventually (σ : FiniteSignal Var) (K : Set ℝ)
    (I : TimeInterval) (φ : Formula Var) (hK : K ⊆ σ.domain)
    (hφ : ∀ t : σ.Time, t.1 ∈ K → (σ, t) ⊨ φ) :
    ∀ t : σ.Time, t.1 ∈ timingDifference K I → (σ, t) ⊨ ◇[I] φ := by
  intro t ht
  obtain ⟨u, huK, huI⟩ := ht
  exact (FiniteSignal.satisfies_eventually_iff σ I φ t).2
    ⟨⟨u, hK huK⟩, huI, hφ ⟨u, hK huK⟩ huK⟩

/-- Use C.9 at signal times. The general rule API also permits arbitrary
valuations, so a real origin outside the signal domain uses only the interval
shift, without evaluating an STL formula at that origin. -/
theorem eventually_witness_of_timingDifference (σ : FiniteSignal Var) (K : Set ℝ)
    (I : TimeInterval) (φ : Formula Var) (hK : K ⊆ σ.domain)
    (hφ : ∀ t : σ.Time, t.1 ∈ K → (σ, t) ⊨ φ)
    (t : ℝ) (ht : t ∈ timingDifference K I) :
    ∃ u : σ.Time, u.1 ∈ I.translate t ∧ (σ, u) ⊨ φ := by
  by_cases htD : t ∈ σ.domain
  · let origin : σ.Time := ⟨t, htD⟩
    exact (FiniteSignal.satisfies_eventually_iff σ I φ origin).1
      (interval_eventually σ K I φ hK hφ origin ht)
  · obtain ⟨u, huK, huI⟩ := ht
    let w : σ.Time := ⟨u, hK huK⟩
    exact ⟨w, huI, hφ w huK⟩

/-- Lemma C.10. A finite family of true
partition pieces covers exactly the required eventuality region. Only
operand stability, rather than full subformula stability, is assumed. -/
theorem interval_eventually_stable (σ : FiniteSignal Var) (K : Set ℝ)
    (I : TimeInterval) (φ : Formula Var) (P : IntervalPartition σ.domain)
    (hK : K ⊆ σ.domain) (hst : ∀ j, σ.Stable (P.interval j) φ) :
    (∀ t : σ.Time, t.1 ∈ K → (σ, t) ⊨ ◇[I] φ) ↔
      ∃ S : Finset (Fin P.size),
        (∀ t ∈ K, ∃ j ∈ S, t ∈ timingDifference (P.interval j).carrier I) ∧
        (∀ j ∈ S, ∀ t : σ.Time, t.1 ∈ P.interval j → (σ, t) ⊨ φ) := by
  classical
  constructor
  · intro h
    let S := Finset.univ.filter fun j =>
      ∀ t : σ.Time, t.1 ∈ P.interval j → (σ, t) ⊨ φ
    refine ⟨S, ?_, ?_⟩
    · intro t htK
      obtain ⟨u, huI, huφ⟩ :=
        (FiniteSignal.satisfies_eventually_iff σ I φ ⟨t, hK htK⟩).1
          (h ⟨t, hK htK⟩ htK)
      have huD : u.1 ∈ ⋃ j, (P.interval j).carrier := P.covers.symm ▸ u.2
      obtain ⟨j, huj⟩ := Set.mem_iUnion.1 huD
      refine ⟨j, ?_, u.1, huj, huI⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro v hv
      exact (hst j u v huj hv).1 huφ
    · intro j hj
      exact (Finset.mem_filter.1 hj).2
  · rintro ⟨S, hcover, htrue⟩ t htK
    obtain ⟨j, hj, u, huj, huI⟩ := hcover t.1 htK
    have huD : u ∈ σ.domain := by
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨j, huj⟩
    exact (FiniteSignal.satisfies_eventually_iff σ I φ t).2
      ⟨⟨u, huD⟩, huI, htrue j hj ⟨u, huD⟩ huj⟩

/-- The cover from C.10 provides a true partition piece for each origin in the
signal domain. Raw scopes at arbitrary valuations may also contain other
origins; there the interval-shift argument uses the original witness. -/
theorem eventually_stable_scope_cover (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (T : Set ℝ) (I : TimeInterval) (φ : Formula Var)
    (hst : ∀ j, σ.Stable (P.interval j) φ)
    (hs : ∀ t ∈ T, ∃ u : σ.Time, u.1 ∈ I.translate t ∧ (σ,u)⊨φ) :
    ∀ t ∈ T, ∃ (j : Fin P.size) (u : σ.Time), u.1 ∈ P.interval j ∧ u.1 ∈ I.translate t ∧
      ∀ v : σ.Time, v.1 ∈ P.interval j → (σ, v) ⊨ φ := by
  let K := T ∩ σ.domain
  obtain ⟨S, hcover, htrue⟩ :=
    (interval_eventually_stable σ K I φ P Set.inter_subset_right hst).1
      (fun t ht => (FiniteSignal.satisfies_eventually_iff σ I φ t).2 (hs t.1 ht.1))
  intro t ht
  by_cases htD : t ∈ σ.domain
  · obtain ⟨j, hj, u, huJ, huI⟩ := hcover t ⟨ht, htD⟩
    let w : σ.Time := ⟨u, P.covers.subset (Set.mem_iUnion.2 ⟨j, huJ⟩)⟩
    exact ⟨j, w, huJ, huI, htrue j hj⟩
  · obtain ⟨u, huI, huφ⟩ := hs t ht
    have huD : u.1 ∈ ⋃ j, (P.interval j).carrier := P.covers.symm ▸ u.2
    obtain ⟨j, huJ⟩ := Set.mem_iUnion.1 huD
    exact ⟨j, u, huJ, huI, fun v hv => (hst j u v huJ hv).1 huφ⟩

end STLTableau
