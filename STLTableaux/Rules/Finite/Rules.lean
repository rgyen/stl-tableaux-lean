import STLTableaux.Semantics.Predicates.Predicates
import STLTableaux.Rules.Catalogue.ClockedExpansion

/-! Satisfaction of rule branches with bounded timing intervals, using the
judgement semantics from `STLTableaux.Semantics.IntervalSemantics`. -/
namespace STLTableau
open scoped STL
open STLTableau.ExpansionRule
variable {Clock Var : Type*}

def branchSatisfied (R : ExpansionRule Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  ∃ Ψ ∈ R.branches, satisfies σ P α k Ψ

/-- Conjunction expansion is correct without stability or extra invariants,
including at the terminal position. -/
theorem plainAnd_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ, P, α, k)⊨ₚ((plainAnd (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      branchSatisfied (plainAnd φ ψ) σ P α k := by
  by_cases hk : k.1 < P.size
  · simp [branchSatisfied, plainAnd, satisfies, hk,
      predicateSatisfies, FiniteSignal.Satisfies, forall_and]
  · simp [branchSatisfied, plainAnd, satisfies, hk]

/-- Disjunction expansion is sound without stability. -/
theorem plainOr_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (h : branchSatisfied (plainOr φ ψ) σ P α k) :
    (σ, P, α, k)⊨ₚ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ, P, α, k)⊨ₚ Judgement.predicate (.plain φ)) ∨
      ((σ, P, α, k)⊨ₚ Judgement.predicate (.plain ψ)) := by
    simpa [branchSatisfied, plainOr] using h
  by_cases hk : k.1 < P.size
  · simp only [plainOr, satisfies, dif_pos hk, predicateSatisfies] at hb ⊢
    intro t ht
    apply (FiniteSignal.satisfies_or σ φ ψ t).2
    exact hb.elim (fun hφ => Or.inl (hφ t ht)) (fun hψ => Or.inr (hψ t ht))
  · simp [satisfies, hk] at hb

/-- Full stability lets pointwise disjunction choose one branch for the
entire interval. In fact, stability of the first disjunct already suffices. -/
theorem plainOr_complete_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hstable : σ.StablePartition (Formula.or φ ψ) P)
    (h : (σ, P, α, k)⊨ₚ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    branchSatisfied (plainOr φ ψ) σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · have hs : σ.Stable (P.interval ⟨k.1, hk⟩) φ :=
      hstable ⟨k.1, hk⟩ φ (.neg (.and_left (.neg (.refl φ))))
    simp only [plainOr, satisfies, dif_pos hk, predicateSatisfies] at h
    have hb : ((∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ, t)⊨φ) ∨
        (∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ, t)⊨ψ)) := by
      by_cases hφ : ∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ, t)⊨φ
      · exact Or.inl hφ
      · push Not at hφ
        obtain ⟨u, hu, hnu⟩ := hφ
        right
        intro t ht
        rcases (FiniteSignal.satisfies_or σ φ ψ t).1 (h t ht) with htφ | htψ
        · exact (hnu ((hs t u ht hu).1 htφ)).elim
        · exact htψ
    simpa [branchSatisfied, plainOr, satisfies, hk,
      predicateSatisfies] using hb
  · simp [satisfies, hk] at h

/-- Soundness and completeness of disjunction under the stability
assumption, including the terminal position. -/
theorem plainOr_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hstable : σ.StablePartition (Formula.or φ ψ) P) :
    ((σ, P, α, k)⊨ₚ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      branchSatisfied (plainOr φ ψ) σ P α k :=
  ⟨plainOr_complete_at φ ψ σ P α k hstable, plainOr_sound_at φ ψ σ P α k⟩

/-- The immediate-witness branch of until is sound without stability. -/
theorem plainUntil_now_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ)) ⇒ₚ
      (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk, predicateSatisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_untimedUntil_of_and σ φ ψ t (h.1 t ht) (h.2 t ht)
  · simp [satisfies, hk] at h

/-- Every until expansion branch needs the current unclocked predicate for the left operand;
this follows from the inclusive until semantics, without stability. -/
theorem plainUntil_implies_left (φ ψ : Formula Var) :
    (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) ⇒ₚ
      Judgement.predicate (.plain φ) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk, predicateSatisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_left_of_until σ (.unbounded 0) φ ψ t (h t ht)
  · simp only [satisfies, dif_neg hk] at h

/-- The first release branch in the figure is sound: under the
dual semantics it requires only the left operand, not both operands. -/
theorem plainRelease_now_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) : Judgement Clock Var) ⇒ₚ
      Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk, predicateSatisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_release_of_left σ (.unbounded 0) φ ψ t (h t ht)
  · simp only [satisfies, dif_neg hk] at h

/-- Soundness of the next-interval until branch. No stability is needed:
until itself supplies the left operand throughout the next interval. -/
theorem plainUntil_next_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)))) ⇒ₚ
      (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
      simp only [satisfies, dif_pos hk, dif_pos hn,
        predicateSatisfies] at h ⊢
      obtain ⟨u, hu⟩ := P.nonempty j
      have huD : u ∈ σ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨j, hu⟩
      let v : σ.Time := ⟨u, huD⟩
      obtain ⟨w, hvw, hwψ, hprefix⟩ := h.2 v hu
      have hvwle : v.1 ≤ w.1 := TimeInterval.le_of_mem_translate hvw
      intro t ht
      have htv : t.1 ≤ v.1 :=
        (MarkedInterval.le_right_of_mem ht).trans
          (hadj ▸ MarkedInterval.left_le_of_mem hu)
      refine ⟨w, ?_, hwψ, ?_⟩
      · change (0 : ℝ) ≤ w.1 - t.1
        exact sub_nonneg.mpr (htv.trans hvwle)
      · intro z htz hzw
        by_cases hzv : z.1 ≤ v.1
        · have hzUnion := MarkedInterval.mem_union_of_between_adjacent
            (P.interval i) (P.interval j) (P.nonempty i) (P.nonempty j)
            hadj hm ht hu htz hzv
          rcases hzUnion with hzi | hzj
          · exact h.1 z hzi
          · exact FiniteSignal.satisfies_left_of_until σ (.unbounded 0) φ ψ z
              (h.2 z hzj)
        · exact hprefix z (le_of_not_ge hzv) hzw
    · simp [satisfies, hk, hn] at h
  · simp [satisfies, hk] at h

/-- Both until branches are sound at every position. -/
theorem plainUntil_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (h : branchSatisfied (plainUntil φ ψ) σ P α k) :
    (σ, P, α, k)⊨ₚ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ, P, α, k)⊨ₚ
      (Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ))) ∨
      ((σ, P, α, k)⊨ₚ (Judgement.predicate (.plain φ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ))))) := by
    simpa [branchSatisfied, plainUntil] using h
  exact hb.elim (plainUntil_now_sound φ ψ σ P α k)
    (plainUntil_next_sound φ ψ σ P α k)

/-- The next release branch is sound without stability. A counterexample
witness outside the current piece would also refute release in the next piece. -/
theorem plainRelease_next_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain ψ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)))) ⇒ₚ
      (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)) :
        Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
      simp only [satisfies, dif_pos hk, dif_pos hn,
        predicateSatisfies] at h ⊢
      intro t ht hcounter
      obtain ⟨w, htw, hnψ, hprefix⟩ := hcounter
      have htwle : t.1 ≤ w.1 := TimeInterval.le_of_mem_translate htw
      have hwNot : w.1 ∉ P.interval i := by
        intro hw
        exact hnψ (h.1 w hw)
      obtain ⟨u, hu, huw⟩ := MarkedInterval.exists_mem_next_le_of_not_mem
        (P.interval i) (P.interval j) (P.nonempty i) (P.nonempty j)
        hadj hm ht htwle hwNot
      have huD : u ∈ σ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨j, hu⟩
      let v : σ.Time := ⟨u, huD⟩
      have htv : t.1 ≤ v.1 :=
        (MarkedInterval.le_right_of_mem ht).trans
          (hadj ▸ MarkedInterval.left_le_of_mem hu)
      apply h.2 v hu
      refine ⟨w, ?_, hnψ, ?_⟩
      · change (0 : ℝ) ≤ w.1 - u
        exact sub_nonneg.mpr huw
      · intro z hvz hzw
        exact hprefix z (htv.trans hvz) hzw
    · simp [satisfies, hk, hn] at h
  · simp [satisfies, hk] at h

/-- The terminal release branch is sound because every remaining signal
time lies in the current last partition piece. -/
theorem plainRelease_terminal_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var)) ⇒ₚ
      Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [satisfies, dif_pos hk, predicateSatisfies] at h ⊢
    intro t ht hcounter
    obtain ⟨w, htw, hnψ, _⟩ := hcounter
    have hw : w.1 ∈ P.interval ⟨k.1, hk⟩ :=
      P.mem_last_of_le ⟨k.1, hk⟩ h.2 ht w.2 (TimeInterval.le_of_mem_translate htw)
    exact hnψ (h.1 w hw)
  · simp [satisfies, hk] at h

/-- All three release branches are sound without stability. -/
theorem plainRelease_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (h : branchSatisfied (plainRelease φ ψ) σ P α k) :
    (σ, P, α, k)⊨ₚ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ, P, α, k)⊨ₚ Judgement.predicate (.plain φ)) ∨
      ((σ, P, α, k)⊨ₚ (Judgement.predicate (.plain ψ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ))))) ∨
      ((σ, P, α, k)⊨ₚ (Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var))) := by
    simpa [branchSatisfied, plainRelease] using h
  rcases hb with hnow | hnext | hlast
  · exact plainRelease_now_sound φ ψ σ P α k hnow
  · exact plainRelease_next_sound φ ψ σ P α k hnext
  · exact plainRelease_terminal_sound φ ψ σ P α k hlast

/-- Until completeness on a fully stable partition. A witness outside the
current piece provides one next-interval until point, then stability lifts it
to that entire piece. -/
theorem plainUntil_complete_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.untimedUntil φ ψ) P)
    (h : (σ, P, α, k)⊨ₚ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    branchSatisfied (plainUntil φ ψ) σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hU : ∀ t : σ.Time, t.1 ∈ P.interval i →
        (σ, t)⊨(Formula.untimedUntil φ ψ) := by
      simpa only [plainUntil, satisfies, dif_pos hk,
        predicateSatisfies] using h
    have hφ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ, t)⊨φ :=
      fun t ht => FiniteSignal.satisfies_left_of_until σ (.unbounded 0) φ ψ t (hU t ht)
    by_cases hψ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ, t)⊨ψ
    · refine ⟨Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ),
        by simp [plainUntil], ?_⟩
      simp only [satisfies, dif_pos hk, predicateSatisfies]
      exact ⟨hφ, hψ⟩
    · have hnone : ∀ t : σ.Time, t.1 ∈ P.interval i → ¬((σ, t)⊨ψ) := by
        intro t ht htψ
        apply hψ
        intro v hv
        exact (hs i ψ (.until_right (.refl ψ)) t v ht hv).1 htψ
      obtain ⟨a, ha⟩ := P.nonempty i
      have haD : a ∈ σ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i, ha⟩
      let t : σ.Time := ⟨a, haD⟩
      obtain ⟨w, htw, hwψ, hprefix⟩ := hU t ha
      have htwle : t.1 ≤ w.1 := TimeInterval.le_of_mem_translate htw
      have hwNot : w.1 ∉ P.interval i := fun hw => hnone w hw hwψ
      have hn : k.1 + 1 < P.size := by
        by_contra hnot
        have hlast : i.1 + 1 = P.size := by dsimp [i]; omega
        exact hwNot (P.mem_last_of_le i hlast ha w.2 htwle)
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      obtain ⟨u, hu, huw⟩ := MarkedInterval.exists_mem_next_le_of_not_mem
        (P.interval i) (P.interval j) (P.nonempty i) (P.nonempty j) hadj
        (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn) ha htwle hwNot
      have huD : u ∈ σ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨j, hu⟩
      let v : σ.Time := ⟨u, huD⟩
      have htv : t.1 ≤ v.1 := (MarkedInterval.le_right_of_mem ha).trans
        (hadj ▸ MarkedInterval.left_le_of_mem hu)
      have hvU : (σ, v)⊨(Formula.untimedUntil φ ψ) := by
        refine ⟨w, ?_, hwψ, ?_⟩
        · change (0 : ℝ) ≤ w.1 - u
          exact sub_nonneg.mpr huw
        · intro z hvz hzw
          exact hprefix z (htv.trans hvz) hzw
      have hnext : ∀ z : σ.Time, z.1 ∈ P.interval j →
          (σ, z)⊨(Formula.untimedUntil φ ψ) := by
        intro z hz
        exact (hs j (Formula.untimedUntil φ ψ) (.refl _) v z hu hz).1 hvU
      refine ⟨Judgement.predicate (.plain φ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ))),
        by simp [plainUntil], ?_⟩
      simp only [satisfies, dif_pos hk, dif_pos hn, predicateSatisfies]
      exact ⟨hφ, hnext⟩
  · simp [satisfies, hk] at h

/-- Full correctness of the unclocked until rule under full stability. -/
theorem plainUntil_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.untimedUntil φ ψ) P) :
    ((σ, P, α, k)⊨ₚ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      branchSatisfied (plainUntil φ ψ) σ P α k :=
  ⟨plainUntil_complete_at φ ψ σ P α k hs, plainUntil_sound_at φ ψ σ P α k⟩

/-- Release completeness under full stability. If the left operand is
not uniformly true, it is uniformly false; the right operand must then hold.
A next-interval counterexample propagates backward by until soundness. -/
theorem plainRelease_complete_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.release (.unbounded 0) φ ψ) P)
    (h : (σ, P, α, k)⊨ₚ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    branchSatisfied (plainRelease φ ψ) σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hR : ∀ t : σ.Time, t.1 ∈ P.interval i →
        (σ, t)⊨(Formula.release (.unbounded 0) φ ψ) := by
      simpa only [plainRelease, satisfies, dif_pos hk,
        predicateSatisfies] using h
    by_cases hφ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ, t)⊨φ
    · refine ⟨Judgement.predicate (.plain φ), by simp [plainRelease], ?_⟩
      simp only [satisfies, dif_pos hk, predicateSatisfies]
      exact hφ
    · have hnφ : ∀ t : σ.Time, t.1 ∈ P.interval i → ¬((σ, t)⊨φ) := by
        intro t ht htφ
        apply hφ
        intro v hv
        exact (hs i φ (.neg (.until_left (.neg (.refl φ)))) t v ht hv).1 htφ
      have hψ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ, t)⊨ψ := by
        intro t ht
        by_contra hnot
        exact hR t ht (FiniteSignal.satisfies_untimedUntil_of_and
          σ (.neg φ) (.neg ψ) t (hnφ t ht) hnot)
      by_cases hn : k.1 + 1 < P.size
      · let j : Fin P.size := ⟨k.1 + 1, hn⟩
        have hnext : ∀ u : σ.Time, u.1 ∈ P.interval j →
            (σ, u)⊨(Formula.release (.unbounded 0) φ ψ) := by
          intro u hu hcounter
          have hcounterNext : ∀ v : σ.Time, v.1 ∈ P.interval j →
              (σ, v)⊨(Formula.untimedUntil (.neg φ) (.neg ψ)) := by
            intro v hv
            exact (hs j (Formula.untimedUntil (.neg φ) (.neg ψ))
              (.neg (.refl _)) u v hu hv).1 hcounter
          have hbranch : (σ, P, α, k)⊨ₚ
              (Judgement.predicate (.plain (.neg φ)) ∧ⱼ
                Xⱼ (Judgement.predicate (.plain
                  (Formula.untimedUntil (.neg φ) (.neg ψ))))) := by
            simp only [satisfies, dif_pos hk, dif_pos hn,
              predicateSatisfies]
            exact ⟨hnφ, hcounterNext⟩
          have hbad := plainUntil_next_sound (.neg φ) (.neg ψ) σ P α k hbranch
          simp only [satisfies, dif_pos hk, predicateSatisfies] at hbad
          obtain ⟨t, ht⟩ := P.nonempty i
          have htD : t ∈ σ.domain := by
            rw [← P.covers]
            exact Set.mem_iUnion.2 ⟨i, ht⟩
          exact hR ⟨t, htD⟩ ht (hbad ⟨t, htD⟩ ht)
        refine ⟨Judgement.predicate (.plain ψ) ∧ⱼ
          Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ))),
          by simp [plainRelease], ?_⟩
        simp only [satisfies, dif_pos hk, dif_pos hn, predicateSatisfies]
        exact ⟨hψ, hnext⟩
      · refine ⟨Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var),
          by simp [plainRelease], ?_⟩
        simp only [satisfies, dif_pos hk, predicateSatisfies]
        exact ⟨hψ, by omega⟩
  · simp [satisfies, hk] at h

/-- Full correctness of the unclocked release rule under full stability. -/
theorem plainRelease_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.release (.unbounded 0) φ ψ) P) :
    ((σ, P, α, k)⊨ₚ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      branchSatisfied (plainRelease φ ψ) σ P α k :=
  ⟨plainRelease_complete_at φ ψ σ P α k hs, plainRelease_sound_at φ ψ σ P α k⟩


end STLTableau
