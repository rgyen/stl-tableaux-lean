import STLTableaux.Semantics.Robustness.Robustness

namespace STLTableau
namespace RobustnessClip

theorem min_upper {a b x y c : EReal}
    (hx : x ≤ max a c) (hy : y ≤ max b c) :
    min x y ≤ max (min a b) c := by
  calc
    min x y ≤ min (max a c) (max b c) := min_le_min hx hy
    _ = max (min a b) c := (sup_inf_right a b c).symm

theorem max_upper {a b x y c : EReal}
    (hx : x ≤ max a c) (hy : y ≤ max b c) :
    max x y ≤ max (max a b) c := by
  exact max_le (hx.trans (max_le_max (le_max_left _ _) le_rfl))
    (hy.trans (max_le_max (le_max_right _ _) le_rfl))

theorem iSup_upper {ι : Sort*} {f g : ι → EReal} {c : EReal}
    (h : ∀ i, g i ≤ max (f i) c) :
    (⨆ i, g i) ≤ max (⨆ i, f i) c := by
  exact iSup_le fun i => (h i).trans (max_le_max (le_iSup f i) le_rfl)

theorem iInf_upper {ι : Sort*} {f g : ι → EReal} {c : EReal}
    (h : ∀ i, g i ≤ max (f i) c) :
    (⨅ i, g i) ≤ max (⨅ i, f i) c := by
  rw [iInf_sup_eq]
  exact iInf_mono h

theorem neg_iSup {ι : Sort*} (f : ι → EReal) :
    -(⨆ i, f i) = ⨅ i, -f i := EReal.negOrderIso.map_iSup f

theorem neg_iInf {ι : Sort*} (f : ι → EReal) :
    -(⨅ i, f i) = ⨆ i, -f i := EReal.negOrderIso.map_iInf f

end RobustnessClip
namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

theorem robustness_or (φ ψ : Formula Var) (t : σ.Time) :
    σ.Robustness (Formula.or φ ψ) t = max (σ.Robustness φ t) (σ.Robustness ψ t) := by
  simp only [Formula.or, Robustness]
  rw [show ∀ a b : EReal, -min a b = max (-a) (-b) from
    fun a b => EReal.negOrderIso.map_inf a b]
  simp

theorem robustness_eventually (I : TimeInterval) (φ : Formula Var) (t : σ.Time) :
    σ.Robustness (Formula.eventually I φ) t =
      ⨆ (u : σ.Time) (_ : u.val ∈ I.translate t.val), σ.Robustness φ u := by
  simp [Formula.eventually, Robustness]

theorem robustness_always (I : TimeInterval) (φ : Formula Var) (t : σ.Time) :
    σ.Robustness (Formula.always I φ) t =
      ⨅ (u : σ.Time) (_ : u.val ∈ I.translate t.val), σ.Robustness φ u := by
  simp only [Formula.always, Robustness, robustness_eventually,
    RobustnessClip.neg_iSup]
  simp

theorem robustness_release (I : TimeInterval) (φ ψ : Formula Var) (t : σ.Time) :
    σ.Robustness (Formula.release I φ ψ) t =
      ⨅ (u : σ.Time) (_ : u.val ∈ I.translate t.val),
        max (σ.Robustness ψ u)
          (⨆ (s : σ.Time) (_ : t.val ≤ s.val) (_ : s.val ≤ u.val), σ.Robustness φ s) := by
  simp only [Formula.release, Robustness, RobustnessClip.neg_iSup]
  congr 1
  funext u
  congr 1
  funext _
  rw [show ∀ a b : EReal, -min a b = max (-a) (-b) from
    fun a b => EReal.negOrderIso.map_inf a b]
  simp only [neg_neg, RobustnessClip.neg_iInf]

end FiniteSignal

run_elab do
  for name in #[``RobustnessClip.min_upper, ``RobustnessClip.max_upper,
      ``RobustnessClip.iSup_upper, ``RobustnessClip.iInf_upper,
      ``RobustnessClip.neg_iSup, ``RobustnessClip.neg_iInf,
      ``FiniteSignal.robustness_or, ``FiniteSignal.robustness_eventually,
      ``FiniteSignal.robustness_always, ``FiniteSignal.robustness_release] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau
