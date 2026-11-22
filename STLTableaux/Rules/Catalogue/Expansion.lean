/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Syntax.Judgements
import STLTableaux.Semantics.Residual.Invariant

/-! # Expansion rules

Branch syntax and expansion rules for conjunction, disjunction, untimed
until, and untimed release (Section 3.3 and Figure 10).
-/

namespace STLTableau

open scoped STL

namespace Judgement

/-- The invariant for a set of judgements: check exactly the interval
predicates that are members of the set, not predicates beneath resets or next.
Those are evaluated separately at their respective valuations and positions. -/
def SetInvariant {Clock Var : Type*} (J : MarkedInterval) (α : ClockValuation Clock)
    (L : Set (Judgement Clock Var)) : Prop :=
  ∀ p, Judgement.predicate p ∈ L → IntervalPredicate.Invariant J α p

@[simp] theorem setInvariant_empty {Clock Var : Type*} (J : MarkedInterval)
    (α : ClockValuation Clock) : SetInvariant J α (∅ : Set (Judgement Clock Var)) := by
  simp [SetInvariant]

theorem setInvariant_union {Clock Var : Type*} (J : MarkedInterval)
    (α : ClockValuation Clock) (L M : Set (Judgement Clock Var)) :
    SetInvariant J α (L ∪ M) ↔ SetInvariant J α L ∧ SetInvariant J α M := by
  simp only [SetInvariant, Set.mem_union, or_imp, forall_and]

/-- Satisfaction of the non-interval-predicate part of a judgement.
Reset and next scopes are retained; interval predicates contribute no tests.
This is the `T` part in Proposition 4.16. -/
def NonPredicateSatisfies {Clock Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) :
    (k : Position P) → Judgement Clock Var → Prop
  | k, .terminal => k.1 = P.size
  | _, .clock c r a => r.Holds (α c) a
  | k, .leftMarker m =>
      if h : k.1 < P.size then (P.interval ⟨k.1, h⟩).leftBoundary = m else m = ●
  | _, .predicate _ => True
  | k, .next Ψ =>
      if h : k.1 < P.size then
        NonPredicateSatisfies σ P (ClockResetSet.elapse α (duration P ⟨k.1, h⟩))
          ⟨k.1 + 1, by omega⟩ Ψ
      else False
  | k, .reset Λ Ψ => NonPredicateSatisfies σ P (Λ.apply α) k Ψ
  | k, .conj Ψ₁ Ψ₂ => NonPredicateSatisfies σ P α k Ψ₁ ∧
      NonPredicateSatisfies σ P α k Ψ₂

theorem nonPredicateSatisfies_congr_of_agree {Clock Var : Type*} {Ψ : Judgement Clock Var}
    {α β : ClockValuation Clock} (h : ∀ c ∈ freeClocks Ψ, α c = β c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (k : Position P) :
    NonPredicateSatisfies σ P α k Ψ ↔ NonPredicateSatisfies σ P β k Ψ := by
  induction Ψ generalizing α β k with
  | terminal => rfl
  | clock c r a =>
      have hc := h c (by simp [freeClocks])
      simp [NonPredicateSatisfies, hc]
  | leftMarker m => rfl
  | predicate p => rfl
  | next Ψ ih =>
      simp only [NonPredicateSatisfies]
      split
      · apply ih
        intro c hc
        simp [ClockResetSet.elapse, h c (by simpa [freeClocks] using hc)]
      · rfl
  | reset Λ Ψ ih =>
      apply ih
      intro c hc
      cases hΛ : Λ.value c with
      | some a => simp [ClockResetSet.apply, hΛ]
      | none =>
          have hcnot : c ∉ Λ.clocks := by
            rintro ⟨a, ha⟩
            rw [hΛ] at ha
            cases ha
          have hcfree : c ∈ freeClocks (.reset Λ Ψ) := ⟨hc, hcnot⟩
          have hα : Λ.apply α c = α c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          have hβ : Λ.apply β c = β c := by
            unfold ClockResetSet.apply
            rw [hΛ]
          rw [hα, hβ]
          exact h c hcfree
  | conj Φ Ψ ihΦ ihΨ =>
      constructor
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).1 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).1 hΨ
      · rintro ⟨hΦ, hΨ⟩
        constructor
        · exact (ihΦ (fun c hc => h c (Or.inl hc)) k).2 hΦ
        · exact (ihΨ (fun c hc => h c (Or.inr hc)) k).2 hΨ


/-- Auxiliary invariant traversal, not the direct-member
`SetInvariant`. Follow elapsed clocks and reset scope. A predicate is checked only when
its declaring interval exists; the terminal position adds no predicate
invariant. Guards add no invariant obligations. -/
def EvaluatedInvariant {Clock Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) :
    (k : Position P) → Judgement Clock Var → Prop
  | _, .terminal => True
  | _, .clock _ _ _ => True
  | _, .leftMarker _ => True
  | k, .predicate p =>
      if h : k.1 < P.size then IntervalPredicate.Invariant (P.interval ⟨k.1, h⟩) α p
      else True
  | k, .next Ψ =>
      if h : k.1 < P.size then
        EvaluatedInvariant σ P (ClockResetSet.elapse α (duration P ⟨k.1, h⟩))
          ⟨k.1 + 1, by omega⟩ Ψ
      else False
  | k, .reset Λ Ψ => EvaluatedInvariant σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => EvaluatedInvariant σ P α k Φ ∧ EvaluatedInvariant σ P α k Ψ

@[simp] theorem evaluatedInvariant_conj {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (Φ Ψ : Judgement Clock Var) :
    EvaluatedInvariant σ P α k (Φ ∧ⱼ Ψ) ↔
      EvaluatedInvariant σ P α k Φ ∧ EvaluatedInvariant σ P α k Ψ := Iff.rfl

@[simp] theorem evaluatedInvariant_reset {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (Λ : ClockResetSet Clock)
    (Ψ : Judgement Clock Var) :
    EvaluatedInvariant σ P α k (Λ ·ⱼ Ψ) ↔
      EvaluatedInvariant σ P (Λ.apply α) k Ψ := Iff.rfl

/-- Recursive checking of every set member implies the invariant
for direct predicate members at a valid declaring interval. -/
theorem setInvariant_of_evaluated {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (hk : k.1 < P.size)
    (L : Set (Judgement Clock Var))
    (h : ∀ Ψ ∈ L, EvaluatedInvariant σ P α k Ψ) :
    SetInvariant (P.interval ⟨k.1, hk⟩) α L := by
  intro p hp
  simpa only [EvaluatedInvariant, dif_pos hk] using h (.predicate p) hp

/-- A recursively checked branch can replace one judgement in a set while
preserving the direct-member invariant. No reset is applied to the
other members; the branch retains its own evaluation context. -/
theorem setInvariant_replace_of_evaluated {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (hk : k.1 < P.size)
    (L : Set (Judgement Clock Var)) (source B : Judgement Clock Var)
    (hL : SetInvariant (P.interval ⟨k.1, hk⟩) α L)
    (hB : EvaluatedInvariant σ P α k B) :
    SetInvariant (P.interval ⟨k.1, hk⟩) α (insert B (L \ {source})) := by
  intro p hp
  rcases Set.mem_insert_iff.1 hp with heq | hp
  · subst B
    simpa only [EvaluatedInvariant, dif_pos hk] using hB
  · exact hL p hp.1

/-- Flatten only the outer conjunctions of a branch. Next/reset bodies
remain intact so their time and clock evaluation contexts are preserved.
The result is a set of judgement conjuncts. -/
def conjuncts {Clock Var : Type*} : Judgement Clock Var → Set (Judgement Clock Var)
  | .conj Φ Ψ => conjuncts Φ ∪ conjuncts Ψ
  | Ψ => {Ψ}

/-- Replacing outer conjunctions by a set preserves satisfaction. -/
theorem satisfies_conjuncts_iff {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (B : Judgement Clock Var) :
    (∀ Ψ ∈ conjuncts B, (σ,P,α,k)⊨ⱼΨ) ↔ (σ,P,α,k)⊨ⱼB := by
  induction B with
  | conj Φ Ψ ihΦ ihΨ =>
      simpa only [conjuncts, Set.mem_union, or_imp, forall_and, Satisfies] using
        and_congr ihΦ ihΨ
  | _ => simp only [conjuncts, Set.mem_singleton_iff, forall_eq]

/-- Flattening preserves recursive invariant obligations as well. -/
theorem evaluatedInvariant_conjuncts_iff {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (B : Judgement Clock Var) :
    (∀ Ψ ∈ conjuncts B, EvaluatedInvariant σ P α k Ψ) ↔
      EvaluatedInvariant σ P α k B := by
  induction B with
  | conj Φ Ψ ihΦ ihΨ =>
      simpa only [conjuncts, Set.mem_union, or_imp, forall_and, EvaluatedInvariant] using
        and_congr ihΦ ihΨ
  | _ => simp only [conjuncts, Set.mem_singleton_iff, forall_eq]

/-- Replace one set member with all outer conjuncts of a checked branch.
The unchanged context retains its clocks and direct-member invariant. -/
theorem setInvariant_replace_conjuncts_of_evaluated {Clock Var : Type*}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Position P) (hk : k.1 < P.size)
    (L : Set (Judgement Clock Var)) (source B : Judgement Clock Var)
    (hL : SetInvariant (P.interval ⟨k.1, hk⟩) α L)
    (hB : EvaluatedInvariant σ P α k B) :
    SetInvariant (P.interval ⟨k.1, hk⟩) α ((L \ {source}) ∪ conjuncts B) := by
  apply (setInvariant_union _ _ _ _).2
  constructor
  · intro p hp
    exact hL p hp.1
  · exact setInvariant_of_evaluated σ P α k hk (conjuncts B)
      ((evaluatedInvariant_conjuncts_iff σ P α k B).2 hB)

end Judgement

/-- A source predicate and a nonempty finite list of possible branches. -/
structure ExpansionRule (Clock Var : Type*) where
  source : IntervalPredicate Clock Var
  branches : List (Judgement Clock Var)
  branches_nonempty : branches ≠ []

namespace ExpansionRule

variable {Clock Var : Type*}

/-- Conjunction has one branch containing both unclocked predicates. -/
def plainAnd (φ ψ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (φ ∧ₛ ψ)
  branches := [Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ)]
  branches_nonempty := by simp

/-- Disjunction has one alternative for each disjunct. -/
def plainOr (φ ψ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (Formula.or φ ψ)
  branches := [Judgement.predicate (.plain φ), Judgement.predicate (.plain ψ)]
  branches_nonempty := by simp

/-- The two untimed-until branches in the rule catalogue. -/
def plainUntil (φ ψ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (Formula.untimedUntil φ ψ)
  branches := [
    Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ),
    Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)))]
  branches_nonempty := by simp

/-- The three untimed-release branches in the rule catalogue. -/
def plainRelease (φ ψ : Formula Var) : ExpansionRule Clock Var where
  source := .plain (Formula.release (.unbounded 0) φ ψ)
  branches := [
    Judgement.predicate (.plain φ),
    Judgement.predicate (.plain ψ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ))),
    Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var)]
  branches_nonempty := by simp

/-- Some expansion branch holds in the specified semantic context. -/
def BranchSatisfied (R : ExpansionRule Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) : Prop :=
  ∃ Ψ ∈ R.branches, (σ,P,α,k)⊨ⱼ Ψ

/-- Conjunction expansion is correct without stability or extra invariants,
including at the terminal position. -/
theorem plainAnd_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) :
    ((σ,P,α,k)⊨ⱼ((plainAnd (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      (plainAnd φ ψ).BranchSatisfied σ P α k := by
  by_cases hk : k.1 < P.size
  · simp [BranchSatisfied, plainAnd, Judgement.Satisfies, hk,
      IntervalPredicate.Satisfies, FiniteSignal.Satisfies, forall_and]
  · simp [BranchSatisfied, plainAnd, Judgement.Satisfies, hk]

/-- Disjunction expansion is sound without stability. -/
theorem plainOr_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (h : (plainOr φ ψ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ,P,α,k)⊨ⱼ Judgement.predicate (.plain φ)) ∨
      ((σ,P,α,k)⊨ⱼ Judgement.predicate (.plain ψ)) := by
    simpa [BranchSatisfied, plainOr] using h
  by_cases hk : k.1 < P.size
  · simp only [plainOr, Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at hb ⊢
    intro t ht
    apply (FiniteSignal.satisfies_or σ φ ψ t).2
    exact hb.elim (fun hφ => Or.inl (hφ t ht)) (fun hψ => Or.inr (hψ t ht))
  · simp [Judgement.Satisfies, hk] at hb

/-- Full stability lets pointwise disjunction choose one branch for the
entire interval. In fact, stability of the first disjunct already suffices. -/
theorem plainOr_complete_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hstable : σ.StablePartition (Formula.or φ ψ) P)
    (h : (σ,P,α,k)⊨ⱼ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    (plainOr φ ψ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · have hs : σ.Stable (P.interval ⟨k.1, hk⟩) φ :=
      hstable ⟨k.1, hk⟩ φ (.neg (.and_left (.neg (.refl φ))))
    simp only [plainOr, Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h
    have hb : ((∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ,t)⊨φ) ∨
        (∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ,t)⊨ψ)) := by
      by_cases hφ : ∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1, hk⟩ → (σ,t)⊨φ
      · exact Or.inl hφ
      · push Not at hφ
        obtain ⟨u, hu, hnu⟩ := hφ
        right
        intro t ht
        rcases (FiniteSignal.satisfies_or σ φ ψ t).1 (h t ht) with htφ | htψ
        · exact (hnu ((hs t u ht hu).1 htφ)).elim
        · exact htψ
    simpa [BranchSatisfied, plainOr, Judgement.Satisfies, hk,
      IntervalPredicate.Satisfies] using hb
  · simp [Judgement.Satisfies, hk] at h

/-- Soundness and completeness of disjunction under the stability
assumption, including the terminal position. -/
theorem plainOr_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hstable : σ.StablePartition (Formula.or φ ψ) P) :
    ((σ,P,α,k)⊨ⱼ((plainOr (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      (plainOr φ ψ).BranchSatisfied σ P α k :=
  ⟨plainOr_complete_at φ ψ σ P α k hstable, plainOr_sound_at φ ψ σ P α k⟩

/-- The immediate-witness branch of until is sound without stability. -/
theorem plainUntil_now_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ)) ⇒ⱼ
      (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_untimedUntil_of_and σ φ ψ t (h.1 t ht) (h.2 t ht)
  · simp [Judgement.Satisfies, hk] at h

/-- Every until expansion branch needs the current unclocked predicate for the left operand;
this follows from the inclusive until semantics, without stability. -/
theorem plainUntil_implies_left (φ ψ : Formula Var) :
    (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) ⇒ⱼ
      Judgement.predicate (.plain φ) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_left_of_until σ (.unbounded 0) φ ψ t (h t ht)
  · simp only [Judgement.Satisfies, dif_neg hk] at h

/-- The first release branch in the figure is sound: under the
dual semantics it requires only the left operand, not both operands. -/
theorem plainRelease_now_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) : Judgement Clock Var) ⇒ⱼ
      Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h ⊢
    intro t ht
    exact FiniteSignal.satisfies_release_of_left σ (.unbounded 0) φ ψ t (h t ht)
  · simp only [Judgement.Satisfies, dif_neg hk] at h

/-- Soundness of the next-interval until branch. No stability is needed:
until itself supplies the left operand throughout the next interval. -/
theorem plainUntil_next_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain φ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)))) ⇒ⱼ
      (Judgement.predicate (.plain (Formula.untimedUntil φ ψ)) : Judgement Clock Var) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1, hk⟩
      let j : Fin P.size := ⟨k.1 + 1, hn⟩
      have hadj : (P.interval i).right = (P.interval j).left :=
        P.adjacent_right_eq_left i hn
      have hm := P.adjacent_rightBoundary_eq_complement_leftBoundary i hn
      simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn,
        IntervalPredicate.Satisfies] at h ⊢
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
    · simp [Judgement.Satisfies, hk, hn] at h
  · simp [Judgement.Satisfies, hk] at h

/-- Both until branches are sound at every position. -/
theorem plainUntil_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (h : (plainUntil φ ψ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ,P,α,k)⊨ⱼ
      (Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ))) ∨
      ((σ,P,α,k)⊨ⱼ (Judgement.predicate (.plain φ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ))))) := by
    simpa [BranchSatisfied, plainUntil] using h
  exact hb.elim (plainUntil_now_sound φ ψ σ P α k)
    (plainUntil_next_sound φ ψ σ P α k)

/-- The next release branch is sound without stability. A counterexample
witness outside the current piece would also refute release in the next piece. -/
theorem plainRelease_next_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain ψ) ∧ⱼ
      Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)))) ⇒ⱼ
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
      simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn,
        IntervalPredicate.Satisfies] at h ⊢
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
    · simp [Judgement.Satisfies, hk, hn] at h
  · simp [Judgement.Satisfies, hk] at h

/-- The terminal release branch is sound because every remaining signal
time lies in the current last partition piece. -/
theorem plainRelease_terminal_sound (φ ψ : Formula Var) :
    (Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var)) ⇒ⱼ
      Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ)) := by
  intro σ P α k h
  by_cases hk : k.1 < P.size
  · simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at h ⊢
    intro t ht hcounter
    obtain ⟨w, htw, hnψ, _⟩ := hcounter
    have hw : w.1 ∈ P.interval ⟨k.1, hk⟩ :=
      P.mem_last_of_le ⟨k.1, hk⟩ h.2 ht w.2 (TimeInterval.le_of_mem_translate htw)
    exact hnψ (h.1 w hw)
  · simp [Judgement.Satisfies, hk] at h

/-- All three release branches are sound without stability. -/
theorem plainRelease_sound_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (h : (plainRelease φ ψ).BranchSatisfied σ P α k) :
    (σ,P,α,k)⊨ⱼ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var) := by
  have hb : ((σ,P,α,k)⊨ⱼ Judgement.predicate (.plain φ)) ∨
      ((σ,P,α,k)⊨ⱼ (Judgement.predicate (.plain ψ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ))))) ∨
      ((σ,P,α,k)⊨ⱼ (Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var))) := by
    simpa [BranchSatisfied, plainRelease] using h
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
    (h : (σ,P,α,k)⊨ⱼ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    (plainUntil φ ψ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hU : ∀ t : σ.Time, t.1 ∈ P.interval i →
        (σ,t)⊨(Formula.untimedUntil φ ψ) := by
      simpa only [plainUntil, Judgement.Satisfies, dif_pos hk,
        IntervalPredicate.Satisfies] using h
    have hφ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ,t)⊨φ :=
      fun t ht => FiniteSignal.satisfies_left_of_until σ (.unbounded 0) φ ψ t (hU t ht)
    by_cases hψ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ,t)⊨ψ
    · refine ⟨Judgement.predicate (.plain φ) ∧ⱼ Judgement.predicate (.plain ψ),
        by simp [plainUntil], ?_⟩
      simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies]
      exact ⟨hφ, hψ⟩
    · have hnone : ∀ t : σ.Time, t.1 ∈ P.interval i → ¬((σ,t)⊨ψ) := by
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
      have hvU : (σ,v)⊨(Formula.untimedUntil φ ψ) := by
        refine ⟨w, ?_, hwψ, ?_⟩
        · change (0 : ℝ) ≤ w.1 - u
          exact sub_nonneg.mpr huw
        · intro z hvz hzw
          exact hprefix z (htv.trans hvz) hzw
      have hnext : ∀ z : σ.Time, z.1 ∈ P.interval j →
          (σ,z)⊨(Formula.untimedUntil φ ψ) := by
        intro z hz
        exact (hs j (Formula.untimedUntil φ ψ) (.refl _) v z hu hz).1 hvU
      refine ⟨Judgement.predicate (.plain φ) ∧ⱼ
        Xⱼ (Judgement.predicate (.plain (Formula.untimedUntil φ ψ))),
        by simp [plainUntil], ?_⟩
      simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn, IntervalPredicate.Satisfies]
      exact ⟨hφ, hnext⟩
  · simp [Judgement.Satisfies, hk] at h

/-- Full correctness of the unclocked until rule under full stability. -/
theorem plainUntil_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.untimedUntil φ ψ) P) :
    ((σ,P,α,k)⊨ⱼ((plainUntil (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      (plainUntil φ ψ).BranchSatisfied σ P α k :=
  ⟨plainUntil_complete_at φ ψ σ P α k hs, plainUntil_sound_at φ ψ σ P α k⟩

/-- Release completeness under full stability. If the left operand is
not uniformly true, it is uniformly false; the right operand must then hold.
A next-interval counterexample propagates backward by until soundness. -/
theorem plainRelease_complete_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.release (.unbounded 0) φ ψ) P)
    (h : (σ,P,α,k)⊨ⱼ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var)) :
    (plainRelease φ ψ).BranchSatisfied σ P α k := by
  classical
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1, hk⟩
    have hR : ∀ t : σ.Time, t.1 ∈ P.interval i →
        (σ,t)⊨(Formula.release (.unbounded 0) φ ψ) := by
      simpa only [plainRelease, Judgement.Satisfies, dif_pos hk,
        IntervalPredicate.Satisfies] using h
    by_cases hφ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ,t)⊨φ
    · refine ⟨Judgement.predicate (.plain φ), by simp [plainRelease], ?_⟩
      simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies]
      exact hφ
    · have hnφ : ∀ t : σ.Time, t.1 ∈ P.interval i → ¬((σ,t)⊨φ) := by
        intro t ht htφ
        apply hφ
        intro v hv
        exact (hs i φ (.neg (.until_left (.neg (.refl φ)))) t v ht hv).1 htφ
      have hψ : ∀ t : σ.Time, t.1 ∈ P.interval i → (σ,t)⊨ψ := by
        intro t ht
        by_contra hnot
        exact hR t ht (FiniteSignal.satisfies_untimedUntil_of_and
          σ (.neg φ) (.neg ψ) t (hnφ t ht) hnot)
      by_cases hn : k.1 + 1 < P.size
      · let j : Fin P.size := ⟨k.1 + 1, hn⟩
        have hnext : ∀ u : σ.Time, u.1 ∈ P.interval j →
            (σ,u)⊨(Formula.release (.unbounded 0) φ ψ) := by
          intro u hu hcounter
          have hcounterNext : ∀ v : σ.Time, v.1 ∈ P.interval j →
              (σ,v)⊨(Formula.untimedUntil (.neg φ) (.neg ψ)) := by
            intro v hv
            exact (hs j (Formula.untimedUntil (.neg φ) (.neg ψ))
              (.neg (.refl _)) u v hu hv).1 hcounter
          have hbranch : (σ,P,α,k)⊨ⱼ
              (Judgement.predicate (.plain (.neg φ)) ∧ⱼ
                Xⱼ (Judgement.predicate (.plain
                  (Formula.untimedUntil (.neg φ) (.neg ψ))))) := by
            simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn,
              IntervalPredicate.Satisfies]
            exact ⟨hnφ, hcounterNext⟩
          have hbad := plainUntil_next_sound (.neg φ) (.neg ψ) σ P α k hbranch
          simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies] at hbad
          obtain ⟨t, ht⟩ := P.nonempty i
          have htD : t ∈ σ.domain := by
            rw [← P.covers]
            exact Set.mem_iUnion.2 ⟨i, ht⟩
          exact hR ⟨t, htD⟩ ht (hbad ⟨t, htD⟩ ht)
        refine ⟨Judgement.predicate (.plain ψ) ∧ⱼ
          Xⱼ (Judgement.predicate (.plain (Formula.release (.unbounded 0) φ ψ))),
          by simp [plainRelease], ?_⟩
        simp only [Judgement.Satisfies, dif_pos hk, dif_pos hn, IntervalPredicate.Satisfies]
        exact ⟨hψ, hnext⟩
      · refine ⟨Judgement.predicate (.plain ψ) ∧ⱼ Xⱼ (∗ : Judgement Clock Var),
          by simp [plainRelease], ?_⟩
        simp only [Judgement.Satisfies, dif_pos hk, IntervalPredicate.Satisfies]
        exact ⟨hψ, by omega⟩
  · simp [Judgement.Satisfies, hk] at h

/-- Full correctness of the unclocked release rule under full stability. -/
theorem plainRelease_correct_at (φ ψ : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P)
    (hs : σ.StablePartition (Formula.release (.unbounded 0) φ ψ) P) :
    ((σ,P,α,k)⊨ⱼ((plainRelease (Clock := Clock) φ ψ).source : Judgement Clock Var)) ↔
      (plainRelease φ ψ).BranchSatisfied σ P α k :=
  ⟨plainRelease_complete_at φ ψ σ P α k hs, plainRelease_sound_at φ ψ σ P α k⟩

/-- Unclocked conjunction only produces unclocked predicates with trivial invariants. -/
theorem plainAnd_preserves_evaluatedInvariant (φ ψ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (plainAnd φ ψ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [plainAnd, List.mem_cons, List.not_mem_nil, or_false] at hB
  subst B
  by_cases hk : k.1 < P.size <;>
    simp_all [Judgement.EvaluatedInvariant, Judgement.NonPredicateSatisfies,
        IntervalPredicate.Invariant]

/-- Either disjunction branch preserves the recursively evaluated invariant. -/
theorem plainOr_preserves_evaluatedInvariant (φ ψ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (plainOr φ ψ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [plainOr, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl <;> by_cases hk : k.1 < P.size <;>
    simp_all [Judgement.EvaluatedInvariant, Judgement.NonPredicateSatisfies,
        IntervalPredicate.Invariant]

/-- Until preservation includes the validity of the next declaring position. -/
theorem plainUntil_preserves_evaluatedInvariant (φ ψ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (plainUntil φ ψ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [plainUntil, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl <;> by_cases hk : k.1 < P.size <;>
    by_cases hn : k.1 + 1 < P.size <;>
    simp_all [Judgement.EvaluatedInvariant, Judgement.NonPredicateSatisfies,
        IntervalPredicate.Invariant]

/-- Release preservation includes the next and terminal alternatives. -/
theorem plainRelease_preserves_evaluatedInvariant (φ ψ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (B : Judgement Clock Var) (hB : B ∈ (plainRelease φ ψ).branches)
    (h : Judgement.NonPredicateSatisfies σ P α k B) : Judgement.EvaluatedInvariant σ P α k B := by
  simp only [plainRelease, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl <;> by_cases hk : k.1 < P.size <;>
    by_cases hn : k.1 + 1 < P.size <;>
    simp_all [Judgement.EvaluatedInvariant, Judgement.NonPredicateSatisfies,
        IntervalPredicate.Invariant]

end ExpansionRule

end STLTableau
