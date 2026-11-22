import STLTableaux.Automata.Execution.WellBehaved
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace STLTableau
variable {Var : Type*}

/-- The real number f(σ_f(t)) before testing the atomic relation. -/
def atomValue (σ : FiniteSignal Var) (a : AtomicProposition Var) (t : σ.Time) : ℝ :=
  a.function (fun i => σ.value t (a.arguments i))

/-- A boundary condition on the observed signal `[0,τ)`.
The existing forward construction uses this at `σ(left)`, including zero.
FlowSignalContinuity derives it from the flow-local `WellBehaved`
on a full execution. -/
def SignalAtomRightContinuous (σ : FiniteSignal Var) (φ : Formula Var) : Prop :=
  ∀ a : AtomicProposition Var, Formula.IsSubformula (.atom a) φ →
    ∀ t : σ.Time, ContinuousWithinAt (atomValue σ a) (Set.Ici t) t

/-- A non-strict atom true just to the right is true at the entry time.
No left limit, continuity of every coordinate, or evaluation at τ. -/
theorem atom_at_left_of_right_continuous (σ : FiniteSignal Var) (a : AtomicProposition Var)
    (ha : a.relation = .ge) (t : σ.Time) (r : ℝ) (hr : t.val < r)
    (hc : ContinuousWithinAt (atomValue σ a) (Set.Ici t) t)
    (hbody : ∀ u : σ.Time, t.val < u.val → u.val < r → a.Holds (σ.value u)) :
    a.Holds (σ.value t) := by
  suffices hg : 0 ≤ atomValue σ a t by simpa [AtomicProposition.Holds,ha,
    RealRelation.Holds,atomValue] using hg
  by_contra! hneg
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousWithinAt_iff.mp hc
    (-(atomValue σ a t)) (by linarith)
  obtain ⟨x,htx,hx⟩ := exists_between
    (lt_min hr (lt_min t.property.2 (show t.val < t.val+δ by linarith)))
  have hx' := lt_min_iff.mp hx
  have hxr := lt_min_iff.mp hx'.2
  let u : σ.Time := ⟨x,t.property.1.trans htx.le,hxr.1⟩
  have hpos := hbody u htx hx'.1
  have hv : 0 ≤ atomValue σ a u := by simpa [AtomicProposition.Holds,ha,
    RealRelation.Holds,atomValue] using hpos
  have hdist : dist u t < δ := by
    change |x - t.val| < δ
    rw [abs_of_nonneg (sub_nonneg.mpr htx.le)]
    linarith [hxr.2]
  have hclose := hd (show u ∈ Set.Ici t from htx.le) hdist
  rw [Real.dist_eq,abs_lt] at hclose
  linarith [hclose.2]

/-- Only pointwise right continuity at this entry is needed for an open
left endpoint; a closed endpoint is handled directly by interval truth. -/
theorem atom_at_partition_entry (σ : FiniteSignal Var)
    (a : AtomicProposition Var) (ha : a.relation = .ge) (J : MarkedInterval)
    (hn : J.carrier.Nonempty) (t : σ.Time) (ht : t.val = J.left)
    (hc : ContinuousWithinAt (atomValue σ a) (Set.Ici t) t)
    (hbody : ∀ u : σ.Time, u.val ∈ J → a.Holds (σ.value u)) :
    a.Holds (σ.value t) := by
  by_cases hleft : J.leftBoundary.Includes
  · apply hbody
    rw [ht]
    exact J.left_mem hn hleft
  · obtain ⟨x,hx⟩ := hn
    have hxleft : J.left < x := hx.1.resolve_right (fun eq => hleft eq.2)
    apply atom_at_left_of_right_continuous σ a ha t J.right
      (ht ▸ hxleft.trans_le (MarkedInterval.le_right_of_mem hx)) hc
    intro u hlu hur
    exact hbody u ⟨Or.inl (ht ▸ hlu),Or.inl hur⟩

/-- Right continuity of the root atoms gives the atom condition at the partition entry. -/
theorem signalAtomRightContinuous_partition_entry (σ : FiniteSignal Var) (φ : Formula Var)
    (hw : SignalAtomRightContinuous σ φ) (a : AtomicProposition Var) (ha : a.relation = .ge)
    (sub : Formula.IsSubformula (.atom a) φ) (J : MarkedInterval)
    (hn : J.carrier.Nonempty) (t : σ.Time) (ht : t.val = J.left)
    (hbody : ∀ u : σ.Time, u.val ∈ J → a.Holds (σ.value u)) :
    a.Holds (σ.value t) :=
  atom_at_partition_entry σ a ha J hn t ht (hw a sub t) hbody

end STLTableau
