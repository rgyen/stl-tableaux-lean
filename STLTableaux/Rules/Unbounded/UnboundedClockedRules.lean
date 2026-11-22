import STLTableaux.Semantics.Predicates.UnboundedClocked
import STLTableaux.Rules.Catalogue.ClockedExpansion

/-! Expansion rules for unbounded clocked predicates. Upper-endpoint guards
that hold at infinity are omitted, and branches with impossible guards are
discarded. `Node.holds` defines satisfaction by recursion on the judgement. -/
namespace STLTableau.UnboundedClocked
open scoped STL
variable {Clock Var : Type*}

inductive Node (Clock Var : Type*) where
  | terminal
  | plain (φ : Formula Var)
  | predicate (p : Predicate Clock Var)
  | clock (c : Clock) (r : ClockRelation) (a : NNReal)
  | marker (m : Marker)
  | next (body : Node Clock Var)
  | reset (resets : ClockResetSet Clock) (body : Node Clock Var)
  | conj (left right : Node Clock Var)

namespace Node

def holds (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) : (k : Judgement.Position P) → Node Clock Var → Prop
  | k, .terminal => k.1 = P.size
  | k, .plain φ => if h : k.1 < P.size then
      ∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1,h⟩ → (σ,t)⊨φ else False
  | k, .predicate p => if h : k.1 < P.size then
      satisfies σ (P.interval ⟨k.1,h⟩) α p else False
  | _, .clock c r a => r.Holds (α c) a
  | k, .marker m => if h : k.1 < P.size then
      (P.interval ⟨k.1,h⟩).leftBoundary = m else m = ●
  | k, .next Ψ => if h : k.1 < P.size then
      holds σ P (ClockResetSet.elapse α (Judgement.duration P ⟨k.1,h⟩))
        ⟨k.1 + 1,by omega⟩ Ψ else False
  | k, .reset Λ Ψ => holds σ P (Λ.apply α) k Ψ
  | k, .conj Φ Ψ => holds σ P α k Φ ∧ holds σ P α k Ψ

def lt (c : Clock) (m : Marker) (a : NNReal) : Node Clock Var :=
  .clock c (match m with | ○ => .lt | ● => .le) a

def gt (c : Clock) (m : Marker) (a : NNReal) : Node Clock Var :=
  .clock c (match m with | ○ => .gt | ● => .ge) a

@[simp] theorem holds_lt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    holds σ P α k (lt c m a) ↔ (α c : ℝ) <[m] (a : ℝ) := by
  cases m <;> simp [lt, holds, ClockRelation.Holds]

@[simp] theorem holds_gt (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) (c : Clock) (m : Marker) (a : NNReal) :
    holds σ P α k (gt c m a) ↔ (a : ℝ) <[m] (α c : ℝ) := by
  cases m <;> simp [gt, holds, ClockRelation.Holds]

end Node

private abbrev C := Node.conj (Clock := Clock) (Var := Var)
private abbrev X := Node.next (Clock := Clock) (Var := Var)
private abbrev A := Node.predicate (Clock := Clock) (Var := Var)
private abbrev T := Node.plain (Clock := Clock) (Var := Var)
private abbrev M := Node.marker (Clock := Clock) (Var := Var)

/-- Main figure's `↑` `□` defer, retaining the endpoint-freezing reset. -/
def upperAlwaysDefer [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  X (C (Node.lt c (Marker.imp b m) a)
    (.reset (ClockResetSet.singleton d 0)
      (C (A (.bounded c d b (¬ₘ m) .always a φ)) (M m))))

def upperAlwaysCheck [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (Node.gt c (Marker.conj b (¬ₘ m)) a)
    (.reset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0))
      (C (A (.bounded c d m (¬ₘ m) .always a φ)) (M m)))))

def alwaysWait (c : Clock) (a : NNReal) : Node Clock Var :=
  X (C (.clock c .le a) .terminal)

def alwaysLast (c : Clock) (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (.clock c .gt a) .terminal))

def upperAlwaysBranches [DecidableEq Clock] (c d : Clock) (b : Marker)
    (a : NNReal) (φ : Formula Var) : List (Node Clock Var) :=
  [upperAlwaysDefer c d b ○ a φ, upperAlwaysDefer c d b ● a φ,
   alwaysWait c a, alwaysLast c a φ,
   upperAlwaysCheck c d b ○ a φ, upperAlwaysCheck c d b ● a φ]

def boundedAlwaysDefer (c d : Clock) (b q m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  X (C (M m) (C (Node.lt c (Marker.imp b m) a)
    (A (.bounded c d b q .always a φ))))

def boundedAlwaysCheck [DecidableEq Clock] (c d : Clock) (b q m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (Node.gt c (Marker.conj b (¬ₘ m)) a)
    (.reset (ClockResetSet.singleton c a)
      (C (A (.bounded c d m q .always a φ)) (M m)))))

/-- `d < ∞` is true; the finite-rule finish branch requiring `d > ∞` is impossible. -/
def boundedAlwaysBranches [DecidableEq Clock] (c d : Clock) (b q : Marker)
    (a : NNReal) (φ : Formula Var) : List (Node Clock Var) :=
  [boundedAlwaysDefer c d b q ○ a φ, boundedAlwaysDefer c d b q ● a φ,
   alwaysWait c a, alwaysLast c a φ,
   boundedAlwaysCheck c d b q ○ a φ, boundedAlwaysCheck c d b q ● a φ]

def upperEventuallyDefer [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  X (.reset (ClockResetSet.singleton d 0)
    (C (A (.bounded c d b (¬ₘ m) .eventually a φ)) (M m)))

def upperEventuallyCheck [DecidableEq Clock] (c d : Clock) (b m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (Node.gt c (Marker.conj b (¬ₘ m)) a)
    (.reset ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0))
      (C (A (.bounded c d m (¬ₘ m) .eventually a φ)) (M m)))))

noncomputable def upperEventuallyBranches [DecidableEq Clock] (c d : Clock) (b : Marker)
    (a : NNReal) (φ : Formula Var) : List (Node Clock Var) := by
  classical
  exact [upperEventuallyDefer c d b ○ a φ, upperEventuallyDefer c d b ● a φ] ++
    if a = 0 then [T φ] else
      [upperEventuallyCheck c d b ○ a φ, upperEventuallyCheck c d b ● a φ]

def boundedEventuallyDefer (c d : Clock) (b q m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  X (C (M m) (A (.bounded c d b q .eventually a φ)))

def boundedEventuallyFinish (d : Clock) (q m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (Node.gt d (Marker.notConj q m) a) (M m)))

def boundedEventuallyCheck [DecidableEq Clock] (c d : Clock) (b q m : Marker)
    (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  C (T φ) (X (C (Node.gt c (Marker.conj b (¬ₘ m)) a)
    (C (Node.lt d (Marker.conj q m) a)
      (.reset (ClockResetSet.singleton c a)
        (C (A (.bounded c d m q .eventually a φ)) (M m))))))

def boundedEventuallyBranches [DecidableEq Clock] (c d : Clock) (b q : Marker)
    (a : NNReal) (φ : Formula Var) : List (Node Clock Var) :=
  [boundedEventuallyDefer c d b q ○ a φ, boundedEventuallyDefer c d b q ● a φ,
   boundedEventuallyFinish d q ○ a φ, boundedEventuallyFinish d q ● a φ,
   boundedEventuallyCheck c d b q ○ a φ, boundedEventuallyCheck c d b q ● a φ]

/-- Equal tracked endpoints have identical unbounded meanings at any positions. -/
theorem bounded_transport (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α β : ClockValuation Clock) (c d : Clock) (b q : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hc : J.left - (α c : ℝ) = K.left - (β c : ℝ))
    (hd : J.left - (α d : ℝ) = K.left - (β d : ℝ)) :
    satisfies σ J α (.bounded c d b q kind a φ) ↔
      satisfies σ K β (.bounded c d b q kind a φ) := by
  cases kind <;> simp only [satisfies, temporalSatisfies, scope, hc, hd]

/-- Freezing the old right endpoint on the next interval gives exactly the
old `↑` scope, and thus exact semantics, not only a sound implication. -/
theorem upper_frozen_transport [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : Judgement.Position P) (hn : k.1 + 1 < P.size)
    (c d : Clock) (b m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    (hcd : c ≠ d) (hm : (P.interval ⟨k.1 + 1, hn⟩).leftBoundary = m) :
    let i : Fin P.size := ⟨k.1,by omega⟩
    let j : Fin P.size := ⟨k.1 + 1, hn⟩
    let β := (ClockResetSet.singleton d 0).apply
      (ClockResetSet.elapse α (Judgement.duration P i))
    satisfies σ (P.interval i) α (.upper c b kind a φ) ↔
      satisfies σ (P.interval j) β (.bounded c d b (¬ₘ m) kind a φ) := by
  intro i j β
  have hc : (P.interval i).left - (α c : ℝ) =
      (P.interval j).left - (β c : ℝ) := by
    dsimp [β]
    rw [ClockResetSet.apply_singleton_of_ne 0 _ hcd]
    exact (Judgement.next_left_sub_elapse_eq P α i hn c).symm
  have hd : (P.interval i).right = (P.interval j).left - (β d : ℝ) := by
    dsimp [β]
    rw [ClockResetSet.apply_singleton_self, NNReal.coe_zero, sub_zero]
    exact P.adjacent_right_eq_left i hn
  have hq : (P.interval i).rightBoundary = ¬ₘ m := by
    exact (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
      (congrArg Marker.complement hm)
  cases kind <;> simp only [satisfies, temporalSatisfies, scope, hc, hd, hq]

/-- Both eventuality and always freezing/defer branches are sound; the
always lower guard is unnecessary in this direction. -/
theorem upper_defer_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b m : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
    (Node.holds σ P α k (upperAlwaysDefer c d b m a φ) →
      Node.holds σ P α k (A (.upper c b .always a φ))) ∧
    (Node.holds σ P α k (upperEventuallyDefer c d b m a φ) →
      Node.holds σ P α k (A (.upper c b .eventually a φ))) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · constructor
      · intro h
        simp only [upperAlwaysDefer, C, X, A, M, Node.holds, dif_pos hk, dif_pos hn] at h ⊢
        exact (upper_frozen_transport σ P α k hn c d b m .always a φ hcd h.2.2).2 h.2.1
      · intro h
        simp only [upperEventuallyDefer, C, X, A, M, Node.holds, dif_pos hk, dif_pos hn] at h ⊢
        exact (upper_frozen_transport σ P α k hn c d b m .eventually a φ hcd h.2).2 h.1
    · simp [upperAlwaysDefer, upperEventuallyDefer, C, X, A, M, Node.holds, hk, hn]
  · simp [upperAlwaysDefer, upperEventuallyDefer, C, X, A, M, Node.holds, hk]

/-- Unchanged clocks preserve a `↑↓` scope exactly across the next step. -/
theorem bounded_defer_sound (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var) :
    (Node.holds σ P α k (boundedAlwaysDefer c d b q m a φ) →
      Node.holds σ P α k (A (.bounded c d b q .always a φ))) ∧
    (Node.holds σ P α k (boundedEventuallyDefer c d b q m a φ) →
      Node.holds σ P α k (A (.bounded c d b q .eventually a φ))) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · have hc := (Judgement.next_left_sub_elapse_eq P α ⟨k.1,hk⟩ hn c).symm
      have hd := (Judgement.next_left_sub_elapse_eq P α ⟨k.1,hk⟩ hn d).symm
      constructor
      · intro h
        simp only [boundedAlwaysDefer, C, X, A, M, Node.holds, dif_pos hk, dif_pos hn] at h ⊢
        exact (bounded_transport σ _ _ α _ c d b q .always a φ hc hd).2 h.2.2
      · intro h
        simp only [boundedEventuallyDefer, C, X, A, M, Node.holds, dif_pos hk, dif_pos hn] at h ⊢
        exact (bounded_transport σ _ _ α _ c d b q .eventually a φ hc hd).2 h.2
    · simp [boundedAlwaysDefer, boundedEventuallyDefer, C, X, A, M, Node.holds, hk, hn]
  · simp [boundedAlwaysDefer, boundedEventuallyDefer, C, X, A, M, Node.holds, hk]

/-- TemporalOpen for the unbounded extension. -/
def opening [DecidableEq Clock] (c : Clock) (m : Marker)
    (kind : TemporalKind) (a : NNReal) (φ : Formula Var) : Node Clock Var :=
  .reset (ClockResetSet.singleton c 0) (C (A (.upper c m kind a φ)) (M m))

theorem opening_correct [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    Node.holds σ P α k (T (formula kind a φ)) ↔
      ∃ m, Node.holds σ P α k (opening c m kind a φ) := by
  by_cases hk : k.1 < P.size
  · let J := P.interval ⟨k.1,hk⟩
    have hD : J.carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1,hk⟩,ht⟩
    constructor
    · intro h
      have hh : ∀ t : σ.Time, t.1 ∈ J → (σ,t)⊨formula kind a φ := by
        simpa [T, Node.holds, hk, J] using h
      refine ⟨J.leftBoundary, ?_⟩
      simp only [opening, C, A, M, Node.holds, dif_pos hk]
      exact ⟨(plain_iff_upper_zero σ J ((ClockResetSet.singleton c 0).apply α) c
        J.leftBoundary kind a φ
        (P.nonempty _) hD (by simp) rfl).1 hh, rfl⟩
    · rintro ⟨m,h⟩
      simp only [opening, C, A, M, Node.holds, dif_pos hk] at h
      have hh := (plain_iff_upper_zero σ J ((ClockResetSet.singleton c 0).apply α) c m kind a φ
        (P.nonempty _) hD (by simp) h.2.symm).2 h.1
      simpa [T, Node.holds, hk, J] using hh
  · simp [opening, C, A, M, Node.holds, hk]

private theorem lower_suffix (J : MarkedInterval) (α : ClockValuation Clock)
    (c : Clock) (b : Marker) (a : NNReal)
    (hi : (α c : ℝ) <[Marker.imp b J.leftBoundary] (a : ℝ))
    (t : ℝ) (ht : J.left - (α c : ℝ) + (a : ℝ) <[b] t) :
    IntervalPredicate.InCurrentSuffix J t := by
  rcases hi with hi | ⟨hi,hm⟩
  · left; rcases ht with ht | ⟨ht,_⟩ <;> linarith
  · rcases ht with ht | ⟨ht,hb⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, (Marker.includes_imp _ _).1 hm hb⟩

/-- Both terminal-always branches are sound under the original positional
invariant, without any stability or hypothesis for no past satisfaction. -/
theorem always_terminal_sound (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size,
      (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1,hk⟩).leftBoundary] (a : ℝ)) :
    (Node.holds σ P α k (alwaysWait c a) ∨ Node.holds σ P α k (alwaysLast c a φ)) →
      Node.holds σ P α k (A (.upper c b .always a φ)) := by
  intro h
  by_cases hk : k.1 < P.size
  · simp only [Node.holds, dif_pos hk, satisfies, temporalSatisfies, scope]
    intro t ht
    have hs := lower_suffix (P.interval ⟨k.1,hk⟩) α c b a (hi hk) t.1 ht
    rcases h with h | h
    · simp only [alwaysWait, C, X, Node.holds, dif_pos hk] at h
      have hlast : k.1 + 1 = P.size := h.2
      have htJ := P.mem_last_of_left_condition ⟨k.1,hk⟩ hlast t.2 hs
      have hr := P.lt_right_of_mem_last ⟨k.1,hk⟩ hlast htJ
      have hg : (α c : ℝ) + ((P.interval ⟨k.1,hk⟩).right -
          (P.interval ⟨k.1,hk⟩).left) ≤ (a : ℝ) := h.1
      have htl : (P.interval ⟨k.1,hk⟩).left - (α c : ℝ) + (a : ℝ) ≤ t.1 :=
        ht.elim le_of_lt (fun h => h.1.le)
      exact (by linarith : False).elim
    · simp only [alwaysLast, C, X, T, Node.holds, dif_pos hk] at h
      exact h.1 t (P.mem_last_of_left_condition ⟨k.1,hk⟩ h.2.2 t.2 hs)
  · simp [alwaysWait, alwaysLast, C, X, T, Node.holds, hk] at h

/-- Once a ray reaches the current piece, the unclocked predicate checks this interval
and resetting c to a starts the next ray exactly at the next boundary. -/
theorem always_check_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size,
      (α c : ℝ) <[Marker.imp b (P.interval ⟨k.1,hk⟩).leftBoundary] (a : ℝ)) :
    (Node.holds σ P α k (upperAlwaysCheck c d b m a φ) →
      Node.holds σ P α k (A (.upper c b .always a φ))) ∧
    (Node.holds σ P α k (boundedAlwaysCheck c d b q m a φ) →
      Node.holds σ P α k (A (.bounded c d b q .always a φ))) := by
  have ray : ∀ (β : ClockValuation Clock),
      (β c : ℝ) = (a : ℝ) →
      ∀ hk : k.1 < P.size, ∀ hn : k.1 + 1 < P.size,
      (P.interval ⟨k.1 + 1,hn⟩).leftBoundary = m →
      (∀ t : σ.Time, t.1 ∈ P.interval ⟨k.1,hk⟩ → (σ,t)⊨φ) →
      (∀ t : σ.Time,
        (P.interval ⟨k.1 + 1,hn⟩).left - (β c : ℝ) + (a : ℝ) <[m] t.1 →
          (σ,t)⊨φ) →
      ∀ t : σ.Time, (P.interval ⟨k.1,hk⟩).left - (α c : ℝ) +
        (a : ℝ) <[b] t.1 → (σ,t)⊨φ := by
    intro β hc hk hn hm hφ hnext t ht
    have hs := lower_suffix (P.interval ⟨k.1,hk⟩) α c b a (hi hk) t.1 ht
    by_cases htJ : t.1 ∈ P.interval ⟨k.1,hk⟩
    · exact hφ t htJ
    · apply hnext t
      rw [hc, sub_add_cancel]
      have hadj := P.adjacent_right_eq_left ⟨k.1,hk⟩ hn
      have hmarker : (P.interval ⟨k.1,hk⟩).rightBoundary = ¬ₘ m := by
        exact (P.adjacent_rightBoundary_eq_complement_leftBoundary ⟨k.1,hk⟩ hn).trans
          (congrArg Marker.complement hm)
      have hnright : ¬ t.1 <[(P.interval ⟨k.1,hk⟩).rightBoundary]
          (P.interval ⟨k.1,hk⟩).right := fun hr => htJ ⟨hs,hr⟩
      rw [← hadj]
      simpa only [sub_zero] using
        (Judgement.not_markedLT_add_complement_iff t.1 0 _ m).1
          (by simpa only [add_zero, hmarker] using hnright)
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · constructor
      · intro h
        simp only [upperAlwaysCheck, C, X, T, M, A, Node.holds,
          dif_pos hk, dif_pos hn, satisfies, temporalSatisfies, scope] at h ⊢
        exact ray _ (by simp [ClockResetSet.apply, ClockResetSet.union,
          ClockResetSet.singleton]) hk hn h.2.2.2 h.1 h.2.2.1
      · intro h
        simp only [boundedAlwaysCheck, C, X, T, M, A, Node.holds,
          dif_pos hk, dif_pos hn, satisfies, temporalSatisfies, scope] at h ⊢
        exact ray _ (by simp) hk hn h.2.2.2 h.1 h.2.2.1
    · simp [upperAlwaysCheck, boundedAlwaysCheck, C, X, T, Node.holds, hk, hn]
  · simp [upperAlwaysCheck, boundedAlwaysCheck, C, X, T, Node.holds, hk]

private theorem eventually_cut (σ : FiniteSignal Var) (J K : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var)
    (r : ℝ) (hne : J.carrier.Nonempty) (hD : J.carrier ⊆ σ.domain)
    (hadj : J.right = K.left) (hm : J.rightBoundary = ¬ₘ m)
    (hφ : ∀ u : σ.Time, u.1 ∈ J → (σ,u)⊨φ)
    (hnext : ∀ t : ℝ, K.left - (a : ℝ) <[m] t → t <[q] r →
      ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ,u)⊨φ) :
    ∀ t : ℝ, J.left - (α c : ℝ) <[b] t → t <[q] r →
      ∃ u : σ.Time, (a : ℝ) ≤ u.1 - t ∧ (σ,u)⊨φ := by
  intro t ht hr
  by_cases hcut : t + (a : ℝ) <[J.rightBoundary] J.right
  · exact current_witness σ J α c b a φ hne hD hφ t ht hcut
  · apply hnext t ?_ hr
    rw [← hadj]
    exact (Judgement.not_markedLT_add_complement_iff t (a : ℝ) J.right m).1
      (by simpa only [hm] using hcut)

/-- Check/reset soundness for both eventuality forms. With no finite upper
bound there is no reach constraint on current witnesses. -/
theorem eventually_check_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d) :
    (Node.holds σ P α k (upperEventuallyCheck c d b m a φ) →
      Node.holds σ P α k (A (.upper c b .eventually a φ))) ∧
    (Node.holds σ P α k (boundedEventuallyCheck c d b q m a φ) →
      Node.holds σ P α k (A (.bounded c d b q .eventually a φ))) := by
  by_cases hk : k.1 < P.size
  · by_cases hn : k.1 + 1 < P.size
    · let i : Fin P.size := ⟨k.1,hk⟩
      let j : Fin P.size := ⟨k.1 + 1,hn⟩
      let γ := ClockResetSet.elapse α (Judgement.duration P i)
      have hadj : (P.interval i).right = (P.interval j).left := P.adjacent_right_eq_left i hn
      have hD : (P.interval i).carrier ⊆ σ.domain := by
        intro t ht
        rw [← P.covers]
        exact Set.mem_iUnion.2 ⟨i,ht⟩
      have hm : (P.interval j).leftBoundary = m → (P.interval i).rightBoundary = ¬ₘ m := by
        intro hh
        exact (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hh)
      constructor
      · intro h
        let β := ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ
        have hβc : β c = a := by
          simp [β, ClockResetSet.apply, ClockResetSet.union, ClockResetSet.singleton]
        have hβd : β d = 0 := by
          change ((ClockResetSet.singleton c a).union (ClockResetSet.singleton d 0)).apply γ d = 0
          rw [ClockResetSet.apply_union_eq_right_of_not_mem _ _ γ (by simp [hcd.symm])]
          exact ClockResetSet.apply_singleton_self d 0 γ
        simp only [upperEventuallyCheck, C, X, T, M, A, Node.holds,
          dif_pos hk, dif_pos hn, satisfies, temporalSatisfies] at h ⊢
        have hnext := h.2.2.1
        change ∀ t : ℝ, t ∈ scope (P.interval j) β
          (.bounded c d m (¬ₘ m) .eventually a φ) → _ at hnext
        intro t ht
        apply eventually_cut σ (P.interval i) (P.interval j) α c b
          (P.interval i).rightBoundary m a φ (P.interval i).right
          (P.nonempty i) hD hadj (hm h.2.2.2) h.1 ?_ t ht.1 ht.2
        intro v hl hr
        apply hnext v
        change ((P.interval j).left - (β c : ℝ) <[m] v) ∧
          (v <[¬ₘ m] ((P.interval j).left - (β d : ℝ)))
        rw [hβc, hβd, NNReal.coe_zero, sub_zero, ← hadj, ← hm h.2.2.2]
        exact ⟨by simpa only [hadj] using hl, hr⟩
      · intro h
        let β := (ClockResetSet.singleton c a).apply γ
        have hβc : β c = a := ClockResetSet.apply_singleton_self c a γ
        have hβd : β d = γ d := ClockResetSet.apply_singleton_of_ne a γ hcd.symm
        have hd : (P.interval j).left - (β d : ℝ) = (P.interval i).left - (α d : ℝ) := by
          rw [hβd]
          exact Judgement.next_left_sub_elapse_eq P α i hn d
        simp only [boundedEventuallyCheck, C, X, T, M, A, Node.holds,
          dif_pos hk, dif_pos hn, satisfies, temporalSatisfies] at h ⊢
        have hnext := h.2.2.2.1
        change ∀ t : ℝ, t ∈ scope (P.interval j) β
          (.bounded c d m q .eventually a φ) → _ at hnext
        intro t ht
        apply eventually_cut σ (P.interval i) (P.interval j) α c b q m a φ
          ((P.interval i).left - (α d : ℝ)) (P.nonempty i) hD hadj
          (hm h.2.2.2.2) h.1 ?_ t ht.1 ht.2
        intro v hl hr
        apply hnext v
        change ((P.interval j).left - (β c : ℝ) <[m] v) ∧
          (v <[q] ((P.interval j).left - (β d : ℝ)))
        rw [hβc, hd]
        exact ⟨hl,hr⟩
    · simp [upperEventuallyCheck, boundedEventuallyCheck, C, X, T, Node.holds, hk, hn]
  · simp [upperEventuallyCheck, boundedEventuallyCheck, C, X, T, Node.holds, hk]

/-- The branch `[φ]` at zero lower bound is sound even without source invariants. -/
theorem upperEventually_zero_sound (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (ha : a = 0)
    (h : Node.holds σ P α k (T φ)) :
    Node.holds σ P α k (A (.upper c b .eventually a φ)) := by
  by_cases hk : k.1 < P.size
  · simp only [Node.holds, dif_pos hk, satisfies, temporalSatisfies] at h ⊢
    have hD : (P.interval ⟨k.1,hk⟩).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1,hk⟩,ht⟩
    intro t ht
    apply current_witness σ _ α c b a φ (P.nonempty _) hD h t ht.1
    rw [ha, NNReal.coe_zero, add_zero]
    exact ht.2
  · simp [Node.holds, hk] at h

theorem boundedEventually_finish_sound (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q m : Marker) (a : NNReal) (φ : Formula Var)
    (h : Node.holds σ P α k (boundedEventuallyFinish d q m a φ)) :
    Node.holds σ P α k (A (.bounded c d b q .eventually a φ)) := by
  by_cases hk : k.1 < P.size
  · let i : Fin P.size := ⟨k.1,hk⟩
    let γ := ClockResetSet.elapse α (Judgement.duration P i)
    simp only [boundedEventuallyFinish, C, T, X, M, Node.holds, dif_pos hk] at h ⊢
    have hright : (P.interval i).rightBoundary = ¬ₘ m := by
      by_cases hn : k.1 + 1 < P.size
      · have hm : (P.interval ⟨k.1 + 1,hn⟩).leftBoundary = m := by
          simpa only [Node.holds, dif_pos hn] using h.2.2
        exact (P.adjacent_rightBoundary_eq_complement_leftBoundary i hn).trans
          (congrArg Marker.complement hm)
      · have hm : m = ● := by simpa only [Node.holds, dif_neg hn] using h.2.2
        have hlast : i.1 + 1 = P.size := by dsimp [i]; omega
        rw [P.rightBoundary_last i hlast, hm]
        rfl
    have hg : (a : ℝ) <[Marker.notConj q m] (γ d : ℝ) :=
      (Node.holds_gt σ P γ ⟨k.1 + 1,by omega⟩ d (Marker.notConj q m) a).1 h.2.1
    have hguard : (a : ℝ) <[Marker.imp q (P.interval i).rightBoundary]
        ((α d : ℝ) + ((P.interval i).right - (P.interval i).left)) := by
      rw [hright]
      have he : Marker.imp q (¬ₘ m) = Marker.notConj q m := by cases q <;> cases m <;> rfl
      rw [he]
      exact hg
    have hD : (P.interval i).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨i,ht⟩
    exact bounded_finish σ (P.interval i) α c d b q a φ (P.nonempty i) hD h.1 hguard
  · simp [boundedEventuallyFinish, C, T, Node.holds, hk] at h

/-- Branch satisfaction is an ordinary existential over the encoded branch list. -/
def BranchSatisfied (branches : List (Node Clock Var)) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P) : Prop :=
  ∃ B ∈ branches, Node.holds σ P α k B

/-- Soundness of the full literal unbounded `↑` `□` rule. -/
theorem upperAlways_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.upper c b .always a φ))
    (h : BranchSatisfied (upperAlwaysBranches c d b a φ) σ P α k) :
    Node.holds σ P α k (A (.upper c b .always a φ)) := by
  obtain ⟨B,hB,h⟩ := h
  simp only [upperAlwaysBranches, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (upper_defer_sound σ P α k c d b ○ a φ hcd).1 h
  · exact (upper_defer_sound σ P α k c d b ● a φ hcd).1 h
  · exact always_terminal_sound σ P α k c b a φ hi (Or.inl h)
  · exact always_terminal_sound σ P α k c b a φ hi (Or.inr h)
  · exact (always_check_sound σ P α k c d b ○ ○ a φ hi).1 h
  · exact (always_check_sound σ P α k c d b ○ ● a φ hi).1 h

/-- Soundness of the full literal unbounded `↑↓` `□` rule. -/
theorem boundedAlways_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var)
    (hi : ∀ hk : k.1 < P.size, Invariant σ P α k hk (.bounded c d b q .always a φ))
    (h : BranchSatisfied (boundedAlwaysBranches c d b q a φ) σ P α k) :
    Node.holds σ P α k (A (.bounded c d b q .always a φ)) := by
  obtain ⟨B,hB,h⟩ := h
  simp only [boundedAlwaysBranches, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (bounded_defer_sound σ P α k c d b q ○ a φ).1 h
  · exact (bounded_defer_sound σ P α k c d b q ● a φ).1 h
  · exact always_terminal_sound σ P α k c b a φ hi (Or.inl h)
  · exact always_terminal_sound σ P α k c b a φ hi (Or.inr h)
  · exact (always_check_sound σ P α k c d b q ○ a φ hi).2 h
  · exact (always_check_sound σ P α k c d b q ● a φ hi).2 h

/-- Soundness of all unbounded `↑` `◇` branches; no invariant is needed. -/
theorem upperEventually_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : BranchSatisfied (upperEventuallyBranches c d b a φ) σ P α k) :
    Node.holds σ P α k (A (.upper c b .eventually a φ)) := by
  classical
  obtain ⟨B,hB,h⟩ := h
  by_cases ha : a = 0
  · simp only [upperEventuallyBranches, if_pos ha, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl
    · exact (upper_defer_sound σ P α k c d b ○ a φ hcd).2 h
    · exact (upper_defer_sound σ P α k c d b ● a φ hcd).2 h
    · exact upperEventually_zero_sound σ P α k c b a φ ha h
  · simp only [upperEventuallyBranches, if_neg ha, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB
    rcases hB with rfl | rfl | rfl | rfl
    · exact (upper_defer_sound σ P α k c d b ○ a φ hcd).2 h
    · exact (upper_defer_sound σ P α k c d b ● a φ hcd).2 h
    · exact (eventually_check_sound σ P α k c d b ○ ○ a φ hcd).1 h
    · exact (eventually_check_sound σ P α k c d b ○ ● a φ hcd).1 h

/-- Soundness of all unbounded `↑↓` `◇` branches. -/
theorem boundedEventually_sound [DecidableEq Clock] (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock) (k : Judgement.Position P)
    (c d : Clock) (b q : Marker) (a : NNReal) (φ : Formula Var) (hcd : c ≠ d)
    (h : BranchSatisfied (boundedEventuallyBranches c d b q a φ) σ P α k) :
    Node.holds σ P α k (A (.bounded c d b q .eventually a φ)) := by
  obtain ⟨B,hB,h⟩ := h
  simp only [boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (bounded_defer_sound σ P α k c d b q ○ a φ).2 h
  · exact (bounded_defer_sound σ P α k c d b q ● a φ).2 h
  · exact boundedEventually_finish_sound σ P α k c d b q ○ a φ h
  · exact boundedEventually_finish_sound σ P α k c d b q ● a φ h
  · exact (eventually_check_sound σ P α k c d b q ○ a φ hcd).2 h
  · exact (eventually_check_sound σ P α k c d b q ● a φ hcd).2 h

end STLTableau.UnboundedClocked
