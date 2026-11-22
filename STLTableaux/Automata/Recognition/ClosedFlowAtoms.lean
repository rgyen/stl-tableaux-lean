import STLTableaux.Automata.Execution.WellBehaved
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.DenselyOrdered

namespace STLTableau
variable {Var : Type*}

/-- Continuous non-strict atoms true on a positive flow's interior hold
on its entire closed domain, including both endpoints. -/
theorem atom_on_closed_curve_of_interior {r : NNReal}
    (γ : HybridFlow.Curve Var r) (hr : 0 < (r : ℝ)) (hγ : Continuous γ)
    (a : AtomicProposition Var) (ha : a.relation = .ge)
    (hf : Continuous a.function)
    (body : ∀ u, 0 < u.val → u.val < (r : ℝ) → a.Holds (γ u)) :
    ∀ u, a.Holds (γ u) := by
  let f : ℝ → ℝ := fun t =>
    a.function (fun i => γ (Set.projIcc (0 : ℝ) (r : ℝ) hr.le t) (a.arguments i))
  have hc : Continuous f := hf.comp (continuous_pi fun i =>
    (continuous_apply (a.arguments i)).comp (hγ.comp continuous_projIcc))
  have closed : IsClosed {t : ℝ | 0 ≤ f t} := isClosed_le continuous_const hc
  have interior : Set.Ioo (0 : ℝ) r ⊆ {t : ℝ | 0 ≤ f t} := by
    intro t ht
    have hp := Set.projIcc_of_mem (h := hr.le) (show t ∈ Set.Icc (0 : ℝ) r from
      ⟨ht.1.le, ht.2.le⟩)
    have h := body (Set.projIcc (0 : ℝ) (r : ℝ) hr.le t)
      (by rw [hp]; exact ht.1) (by rw [hp]; exact ht.2)
    simpa [AtomicProposition.Holds, ha, RealRelation.Holds, f] using h
  have entire : Set.Icc (0 : ℝ) r ⊆ {t : ℝ | 0 ≤ f t} := by
    rw [← closure_Ioo hr.ne]
    exact closed.closure_subset_iff.mpr interior
  intro u
  have h := entire u.property
  simpa [f, AtomicProposition.Holds, ha, RealRelation.Holds] using h

run_elab do
  for ax in ← Lean.collectAxioms ``atom_on_closed_curve_of_interior do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"

end STLTableau
