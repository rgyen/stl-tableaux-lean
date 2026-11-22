import STLTableaux.Syntax.Section3Judgements

/-! Concrete reset-aware boundary extension for both temporal operators and
finite or unbounded timing. This is a local semantic result, not a construction
of bounded paths or a new closure correctness assumption. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- The actual STL formula of a clocked predicate. -/
def timedFormula (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) : Formula Var :=
  match kind with
  | .always => □[I] φ
  | .eventually => ◇[I] φ

/-- An unclocked temporal predicate agrees with its `↑` form when the clock is zero
and the marker is the current interval's left marker. -/
theorem plain_iff_upper_zero (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (d : Clock) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (hne : J.carrier.Nonempty)
    (hD : J.carrier ⊆ σ.domain) (hd : (α d : ℝ) = 0) :
    Predicate.holds σ J α (.plain (timedFormula kind I φ)) ↔
      Predicate.holds σ J α (.upper d J.leftBoundary kind I φ) := by
  cases I with
  | bounded I =>
      cases kind with
      | always => exact STLTableau.plain_always_iff_upper_zero σ J α d I φ hd hne hD
      | eventually => exact STLTableau.plain_eventually_iff_upper_zero σ J α d I φ hd hD
  | unbounded a =>
      exact UnboundedClocked.plain_iff_upper_zero σ J α d J.leftBoundary kind a φ
        hne hD hd rfl

/-- The boundary union uses complementary markers, so the joining comparison
is the true comparison 0 ≤ 0. The other comparison remains an explicit unary
numeric side condition, evaluated after inherited resets. -/
theorem boundary_merge_at (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hd : (α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (α c : ℝ)) :
    Judgement.holds σ P α k
      (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) ↔
      Judgement.holds σ P α k (.predicate (.upper c m kind I φ)) := by
  have hj : (α d : ℝ) <[Marker.disj (¬ₘ ℓ) ℓ] (α d : ℝ) := by
    rw [hd]
    cases ℓ <;> simp [Marker.complement, Marker.disj, MarkedLT, Marker.Includes]
  have he := Judgement.predicate_merge_connected σ P α k c d d m (¬ₘ ℓ) ℓ kind I φ
    hj (by simpa only [hd] using hc)
  apply Iff.trans _ he
  by_cases hk : k.1 < P.size
  · have hD : (P.interval ⟨k.1,hk⟩).carrier ⊆ σ.domain := by
      intro t ht
      rw [← P.covers]
      exact Set.mem_iUnion.2 ⟨⟨k.1,hk⟩,ht⟩
    simp only [Judgement.holds, dif_pos hk]
    exact and_congr Iff.rfl (by
      rw [hm hk]
      exact plain_iff_upper_zero σ _ α d kind I φ (P.nonempty _) hD hd)
  · simp [Judgement.holds, hk]

/-- Required boundary merger inside the actual inherited reset context.
The right clock need only be zero after these resets; arbitrary additional
bindings are allowed and remain in their scope. -/
theorem boundary_merge_under_reset (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hd : (R.apply α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ)) :
    Judgement.holds σ P α k (.reset R
      (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ))))) ↔
    Judgement.holds σ P α k (.reset R (.predicate (.upper c m kind I φ))) :=
  boundary_merge_at σ P (R.apply α) k c d m ℓ kind I φ hd hm hc

/-- Optional extension is always sound: its upper output implies the old
input in the `↑↓` form. Satisfaction of the added unclocked predicate is a consequence, not
a hypothesis. -/
theorem boundary_extension_sound (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hd : (R.apply α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ)) :
    Judgement.holds σ P α k (.reset R (.predicate (.upper c m kind I φ))) →
    Judgement.holds σ P α k
      (.reset R (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))) := by
  intro h
  exact ((boundary_merge_under_reset σ P α k R c d m ℓ kind I φ hd hm hc).2 h).1

/-- On the fixed signal where the current unclocked predicate is true, optional
extension preserves satisfaction in both directions. No path equivalence on
all signals is asserted. -/
theorem boundary_extension_iff_of_plain (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (hd : (R.apply α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ))
    (hplain : Judgement.holds σ P α k (.predicate (.plain (timedFormula kind I φ)))) :
    Judgement.holds σ P α k
      (.reset R (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))) ↔
    Judgement.holds σ P α k (.reset R (.predicate (.upper c m kind I φ))) := by
  have hp : Judgement.holds σ P (R.apply α) k
      (.predicate (.plain (timedFormula kind I φ))) := by
    exact (Judgement.holds_congr_of_agree (Ψ := .predicate (.plain (timedFormula kind I φ)))
      (by intro c hc; exact False.elim hc) σ P k).1 hplain
  exact (and_iff_left hp).symm.trans
    (boundary_merge_under_reset σ P α k R c d m ℓ kind I φ hd hm hc)

/-- The required merger preserves an arbitrary remaining body in its original
reset scope. In particular this body may contain next judgements, guards and
additional resets; none is moved or discarded. -/
theorem boundary_merge_with_body (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Ξ : Section3.Judgement Clock Var) (hd : (R.apply α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ)) :
    Judgement.holds σ P α k (.reset R
      (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) Ξ)) ↔
    Judgement.holds σ P α k
      (.reset R (.conj (.predicate (.upper c m kind I φ)) Ξ)) := by
  exact and_congr
    (boundary_merge_under_reset σ P α k R c d m ℓ kind I φ hd hm hc) Iff.rfl

/-- Fixed-signal optional extension also leaves the whole remaining body in
place, including every future use of an inherited reset binding. -/
theorem boundary_extension_with_body_iff_of_plain (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (R : ClockResetSet Clock)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Ξ : Section3.Judgement Clock Var) (hd : (R.apply α d : ℝ) = 0)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ))
    (hplain : Judgement.holds σ P α k (.predicate (.plain (timedFormula kind I φ)))) :
    Judgement.holds σ P α k (.reset R
      (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) Ξ)) ↔
    Judgement.holds σ P α k
      (.reset R (.conj (.predicate (.upper c m kind I φ)) Ξ)) := by
  exact and_congr
    (boundary_extension_iff_of_plain σ P α k R c d m ℓ kind I φ hd hm hc hplain) Iff.rfl

/-- Delete only an unused binding: the free-clock condition covers the whole
body recursively, including future guards under next. Other resets stay put. -/
theorem unused_singleton_reset [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (d : Clock) (v : NNReal) (Ξ : Section3.Judgement Clock Var)
    (hd : d ∉ Ξ.freeClocks) :
    Judgement.holds σ P α k (.reset (ClockResetSet.singleton d v) Ξ) ↔
      Judgement.holds σ P α k Ξ := by
  change Judgement.holds σ P ((ClockResetSet.singleton d v).apply α) k Ξ ↔
    Judgement.holds σ P α k Ξ
  apply Judgement.holds_congr_of_agree
  intro x hx
  have hxd : x ≠ d := by
    intro h
    subst x
    exact hd hx
  exact ClockResetSet.apply_singleton_of_ne v α hxd

/-- The complete required boundary replacement drops its now-unused right
zero binding. The surrounding inherited reset and arbitrary remaining body
(including next parts) retain their original scope. -/
theorem boundary_merge_remove_right_reset [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (R : ClockResetSet Clock) (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Ξ : Section3.Judgement Clock Var) (hcd : c ≠ d) (hdΞ : d ∉ Ξ.freeClocks)
    (hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (R.apply α c : ℝ)) :
    Judgement.holds σ P α k (.reset R (.reset (ClockResetSet.singleton d 0)
      (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) Ξ))) ↔
    Judgement.holds σ P α k
      (.reset R (.conj (.predicate (.upper c m kind I φ)) Ξ)) := by
  have he := boundary_merge_with_body σ P (R.apply α) k
    (ClockResetSet.singleton d 0) c d m ℓ kind I φ Ξ (by simp) hm
    (by simpa only [ClockResetSet.apply_singleton_of_ne 0 (R.apply α) hcd] using hc)
  exact he.trans (unused_singleton_reset σ P (R.apply α) k d 0 _ (by
    simp only [Section3.Judgement.freeClocks, Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hcd, hdΞ⟩))

end STLTableau.Section4.Finiteness
