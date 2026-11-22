import STLTableaux.Automata.Translation.PrelimStateGoal
import STLTableaux.Automata.Execution.PrelimFlowComposition

/-! Closed-curve concatenation from standard automaton well-formedness.
`FlowAdd` records an optional stronger pointwise property of concrete clock
relations; execution projection does not require it as an extra premise. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*}

def FlowAdd (H : HybridAutomaton Mode Label Var) : Prop :=
  ∀ (q : Mode) (v v₁ v₂ : Var → ℝ) (r s : NNReal),
    H.flow (q, v) r v₁ → H.flow (q, v₁) s v₂ → H.flow (q, v) (r + s) v₂

namespace ContinuousStep

noncomputable abbrev concatCurve (r s : NNReal)
    (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (δ : Set.Icc (0 : ℝ) s → Var → ℝ)
    (t : Set.Icc (0 : ℝ) (r + s : NNReal)) : Var → ℝ :=
  HybridFlow.concatCurve r s γ δ t

theorem concatCurve_left (r s : NNReal)
    (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (δ : Set.Icc (0 : ℝ) s → Var → ℝ)
    (t : Set.Icc (0 : ℝ) r) :
    concatCurve r s γ δ ⟨t.val, t.property.1, by
      have := t.property.2; have := s.coe_nonneg; push_cast; linarith⟩ = γ t := by
  simp only [concatCurve, HybridFlow.concatCurve, dif_pos t.property.2]

theorem concatCurve_right (r s : NNReal)
    (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (δ : Set.Icc (0 : ℝ) s → Var → ℝ)
    (join : γ ⟨r, by simp⟩ = δ ⟨0, by simp⟩) (t : Set.Icc (0 : ℝ) s) :
    concatCurve r s γ δ ⟨r + t.val, by
      have := r.coe_nonneg; have := t.property.1; have := t.property.2; constructor <;>
        push_cast <;> linarith⟩ = δ t := by
  unfold concatCurve HybridFlow.concatCurve
  split_ifs with ht
  · have zero : t.val = 0 := by have := t.property.1; linarith
    have he : (⟨(r : ℝ) + t.val, by positivity, ht⟩ : Set.Icc (0 : ℝ) r) =
        ⟨r, by simp⟩ := Subtype.ext (by simp [zero])
    rw [he, join]
    exact congrArg δ (Subtype.ext zero.symm)
  · exact congrArg δ (Subtype.ext (by dsimp; ring))

variable {H : HybridAutomaton Mode Label Var} {a b c : H.State} {r s : NNReal}
variable {γ : Set.Icc (0 : ℝ) r → Var → ℝ} {δ : Set.Icc (0 : ℝ) s → Var → ℝ}

theorem concat (first : H.ContinuousStep a b r γ)
    (second : H.ContinuousStep b c s δ) :
    H.ContinuousStep a c (r + s) (concatCurve r s γ δ) := by
  have join : γ ⟨r, by simp⟩ = δ ⟨0, by simp⟩ := first.2.2.1.trans second.2.1.symm
  have next : HybridFlow.Evolves H.flow H.invariant a.val.1 δ := by
    simpa only [first.1] using second.evolves
  have evolution := H.trajectory_closed.concat first.evolves next join
  change HybridFlow.Evolves H.flow H.invariant a.val.1
    (concatCurve r s γ δ) at evolution
  refine ⟨first.1.trans second.1, ?_, ?_, ?_⟩
  · exact (concatCurve_left r s γ δ ⟨0, by simp⟩).trans first.2.1
  · simpa using (concatCurve_right r s γ δ join ⟨s, by simp⟩).trans second.2.2.1
  · intro t
    have current := evolution t
    have initial := (concatCurve_left r s γ δ ⟨0, by simp⟩).trans first.2.1
    rw [initial] at current
    exact current

theorem concat_visits_left (r s : NNReal)
    (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (δ : Set.Icc (0 : ℝ) s → Var → ℝ)
    (t : Set.Icc (0 : ℝ) r) :
    ∃ u, concatCurve r s γ δ u = γ t :=
  ⟨_, concatCurve_left r s γ δ t⟩

theorem concat_visits_right (r s : NNReal)
    (γ : Set.Icc (0 : ℝ) r → Var → ℝ) (δ : Set.Icc (0 : ℝ) s → Var → ℝ)
    (join : γ ⟨r, by simp⟩ = δ ⟨0, by simp⟩) (t : Set.Icc (0 : ℝ) s) :
    ∃ u, concatCurve r s γ δ u = δ t :=
  ⟨_, concatCurve_right r s γ δ join t⟩

end ContinuousStep

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ContinuousStep.concat, ``ContinuousStep.concatCurve_left,
      ``ContinuousStep.concatCurve_right, ``ContinuousStep.concat_visits_left,
      ``ContinuousStep.concat_visits_right] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.HybridAutomaton

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

theorem prelim_flowAdd (h : T.TranslationReady) (τ : ℝ) :
    (T.prelimAutomaton h τ).FlowAdd := T.prelim_flow_add h τ

end STLTableau.Section4.Tableau
