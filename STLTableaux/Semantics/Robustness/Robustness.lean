import STLTableaux.Semantics.Signals
import Mathlib.Data.EReal.Operations

/-! The appendix robustness semantics on the original half-open signal
domain. Until uses the inclusive left-operand interval [t,u]. The manuscript's
ge atomic clause is literal evaluation; other relation margins below are
supplementary extensions, not changes to that clause. -/
namespace STLTableau
namespace AtomicProposition
variable {Var : Type*}

def robustness (a : AtomicProposition Var) (v : Var → ℝ) : ℝ :=
  let f := a.function (fun i => v (a.arguments i))
  match a.relation with
  | .ge | .gt => f
  | .le | .lt => -f
  | .eq => -|f|

/-- Literal atomic margin in the appendix's ge case. -/
@[simp] theorem robustness_ge (a : AtomicProposition Var) (v : Var → ℝ) :
    ({a with relation := .ge} : AtomicProposition Var).robustness v =
      a.function (fun i => v (a.arguments i)) := rfl

theorem robustness_pos_implies_holds (a : AtomicProposition Var) (v : Var → ℝ)
    (h : 0 < a.robustness v) : a.Holds v := by
  cases hr : a.relation <;>
    simp only [robustness, hr, Holds, RealRelation.Holds] at h ⊢
  · exact h.le
  · exact h
  · have := abs_nonneg (a.function (fun i => v (a.arguments i))); linarith
  · linarith
  · linarith

theorem holds_implies_robustness_nonneg (a : AtomicProposition Var) (v : Var → ℝ)
    (h : a.Holds v) : 0 ≤ a.robustness v := by
  cases hr : a.relation <;>
    simp only [robustness, hr, Holds, RealRelation.Holds] at h ⊢
  · exact h
  · exact h.le
  · rw [h]; norm_num
  · linarith
  · linarith
end AtomicProposition

namespace FiniteSignal
variable {Var : Type*} (σ : FiniteSignal Var)

noncomputable def Robustness (σ : FiniteSignal Var) : Formula Var → σ.Time → EReal
  | .truth, _ => ⊤
  | .atom a, t => (a.robustness (σ.value t) : EReal)
  | .neg φ, t => -σ.Robustness φ t
  | .and φ ψ, t => min (σ.Robustness φ t) (σ.Robustness ψ t)
  | .until I φ ψ, t =>
      ⨆ (u : σ.Time) (_ : u.val ∈ I.translate t.val),
        min (σ.Robustness ψ u)
          (⨅ (s : σ.Time) (_ : t.val ≤ s.val) (_ : s.val ≤ u.val), σ.Robustness φ s)

theorem robustness_boolean_bridges (φ : Formula Var) (t : σ.Time) :
    (0 < σ.Robustness φ t → σ.Satisfies φ t) ∧
      (σ.Satisfies φ t → 0 ≤ σ.Robustness φ t) := by
  induction φ generalizing t with
  | truth => exact ⟨fun _ => trivial, fun _ => le_top⟩
  | atom a =>
    exact ⟨fun h => a.robustness_pos_implies_holds _ (EReal.coe_pos.mp h),
      fun h => EReal.coe_nonneg.mpr (a.holds_implies_robustness_nonneg _ h)⟩
  | neg φ ih =>
    constructor
    · intro positive truth
      exact (not_le_of_gt (EReal.neg_pos.mp positive)) ((ih t).2 truth)
    · intro truth
      apply EReal.neg_nonneg.mpr
      exact le_of_not_gt (fun positive => truth ((ih t).1 positive))
  | and φ ψ ihφ ihψ =>
    exact ⟨fun h => ⟨(ihφ t).1 (lt_min_iff.mp h).1,
      (ihψ t).1 (lt_min_iff.mp h).2⟩,
      fun h => le_min ((ihφ t).2 h.1) ((ihψ t).2 h.2)⟩
  | «until» I φ ψ ihφ ihψ =>
    constructor
    · intro positive
      obtain ⟨u, hu⟩ := lt_iSup_iff.mp positive
      obtain ⟨inside, positive⟩ := lt_iSup_iff.mp hu
      obtain ⟨right, left⟩ := lt_min_iff.mp positive
      refine ⟨u, inside, (ihψ u).1 right, ?_⟩
      intro s lower upper
      apply (ihφ s).1
      exact left.trans_le (iInf_le_of_le s
        (iInf_le_of_le lower (iInf_le_of_le upper le_rfl)))
    · rintro ⟨u, inside, right, left⟩
      apply le_iSup_of_le u
      apply le_iSup_of_le inside
      apply le_min ((ihψ u).2 right)
      exact le_iInf (fun s => le_iInf (fun lower => le_iInf
        (fun upper => (ihφ s).2 (left s lower upper))))

theorem satisfies_of_robustness_pos (φ : Formula Var) (t : σ.Time)
    (positive : 0 < σ.Robustness φ t) : σ.Satisfies φ t :=
  (σ.robustness_boolean_bridges φ t).1 positive

theorem robustness_nonneg_of_satisfies (φ : Formula Var) (t : σ.Time)
    (truth : σ.Satisfies φ t) : 0 ≤ σ.Robustness φ t :=
  (σ.robustness_boolean_bridges φ t).2 truth
end FiniteSignal

run_elab do
  for name in #[``AtomicProposition.robustness_pos_implies_holds,
      ``AtomicProposition.holds_implies_robustness_nonneg,
      ``FiniteSignal.robustness_boolean_bridges,
      ``FiniteSignal.satisfies_of_robustness_pos,
      ``FiniteSignal.robustness_nonneg_of_satisfies] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end STLTableau
