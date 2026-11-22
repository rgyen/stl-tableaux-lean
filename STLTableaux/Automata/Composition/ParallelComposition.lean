import STLTableaux.Automata.Execution.PrelimExecution

/-! Disjoint-variable special case of parallel composition, represented
by a sum type. None is a fresh idle label; (None,None) is excluded.
This module proves local state/flow/jump projection, not synchronization of
arbitrary trajectory witnesses or the model-checking reduction. -/
namespace STLTableau.HybridAutomaton
variable {Mode₁ Label₁ Var₁ Mode₂ Label₂ Var₂ : Type*}

def IdleEdge (H : HybridAutomaton Mode₁ Label₁ Var₁)
    (q : Mode₁) (l : Option Label₁) (q' : Mode₁) : Prop :=
  match l with
  | none => q = q'
  | some l => (q, l, q') ∈ H.edge

def IdleJump (H : HybridAutomaton Mode₁ Label₁ Var₁) (l : Option Label₁)
    (s s' : Mode₁ × (Var₁ → ℝ)) : Prop :=
  match l with
  | none => s = s'
  | some l => ∃ e : {e // e ∈ H.edge}, e.val = (s.1, l, s'.1) ∧ H.jump e s s'

def parallel (H₁ : HybridAutomaton Mode₁ Label₁ Var₁)
    (H₂ : HybridAutomaton Mode₂ Label₂ Var₂) :
    HybridAutomaton (Mode₁ × Mode₂) (Option Label₁ × Option Label₂) (Sum Var₁ Var₂) where
  modes_finite := by
    letI := H₁.modes_finite
    letI := H₂.modes_finite
    infer_instance
  variables_finite := by
    letI := H₁.variables_finite
    letI := H₂.variables_finite
    infer_instance
  edge := {e | e.2.1 ≠ (none, none) ∧
    H₁.IdleEdge e.1.1 e.2.1.1 e.2.2.1 ∧ H₂.IdleEdge e.1.2 e.2.1.2 e.2.2.2}
  initial := {s | (s.1.1, s.2 ∘ Sum.inl) ∈ H₁.initial ∧
    (s.1.2, s.2 ∘ Sum.inr) ∈ H₂.initial}
  invariant := {s | (s.1.1, s.2 ∘ Sum.inl) ∈ H₁.invariant ∧
    (s.1.2, s.2 ∘ Sum.inr) ∈ H₂.invariant}
  flow := fun s t v => H₁.flow (s.1.1, s.2 ∘ Sum.inl) t (v ∘ Sum.inl) ∧
    H₂.flow (s.1.2, s.2 ∘ Sum.inr) t (v ∘ Sum.inr)
  trajectory_closed := H₁.trajectory_closed.parallel H₂.trajectory_closed Sum.inl Sum.inr
  jump := fun e s s' =>
    H₁.IdleJump e.val.2.1.1 (s.1.1, s.2 ∘ Sum.inl) (s'.1.1, s'.2 ∘ Sum.inl) ∧
    H₂.IdleJump e.val.2.1.2 (s.1.2, s.2 ∘ Sum.inr) (s'.1.2, s'.2 ∘ Sum.inr)

variable (H₁ : HybridAutomaton Mode₁ Label₁ Var₁) (H₂ : HybridAutomaton Mode₂ Label₂ Var₂)

def leftState (s : (H₁.parallel H₂).State) : H₁.State :=
  ⟨(s.val.1.1, s.val.2 ∘ Sum.inl), s.property.1⟩

def rightState (s : (H₁.parallel H₂).State) : H₂.State :=
  ⟨(s.val.1.2, s.val.2 ∘ Sum.inr), s.property.2⟩

theorem parallel_initial_left (s : (H₁.parallel H₂).State)
    (hi : s.val ∈ (H₁.parallel H₂).initial) : (H₁.leftState H₂ s).val ∈ H₁.initial := hi.1

theorem parallel_initial_right (s : (H₁.parallel H₂).State)
    (hi : s.val ∈ (H₁.parallel H₂).initial) : (H₁.rightState H₂ s).val ∈ H₂.initial := hi.2

theorem parallel_continuous_left {a b : (H₁.parallel H₂).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → Sum Var₁ Var₂ → ℝ}
    (step : (H₁.parallel H₂).ContinuousStep a b r γ) :
    H₁.ContinuousStep (H₁.leftState H₂ a) (H₁.leftState H₂ b) r
      (fun t x => γ t (.inl x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change a.val.1.1 = b.val.1.1
    exact congrArg (fun q : Mode₁ × Mode₂ => q.1) step.1
  · funext x
    exact congrFun step.2.1 (.inl x)
  · funext x
    exact congrFun step.2.2.1 (.inl x)
  · intro t
    exact ⟨(step.2.2.2 t).1.1, (step.2.2.2 t).2.1⟩

theorem parallel_continuous_right {a b : (H₁.parallel H₂).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → Sum Var₁ Var₂ → ℝ}
    (step : (H₁.parallel H₂).ContinuousStep a b r γ) :
    H₂.ContinuousStep (H₁.rightState H₂ a) (H₁.rightState H₂ b) r
      (fun t x => γ t (.inr x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change a.val.1.2 = b.val.1.2
    exact congrArg (fun q : Mode₁ × Mode₂ => q.2) step.1
  · funext x
    exact congrFun step.2.1 (.inr x)
  · funext x
    exact congrFun step.2.2.1 (.inr x)
  · intro t
    exact ⟨(step.2.2.2 t).1.2, (step.2.2.2 t).2.2⟩

theorem IdleJump.step_or_eq (H : HybridAutomaton Mode₁ Label₁ Var₁)
    (l : Option Label₁) {a b : H.State} (jump : H.IdleJump l a.val b.val) :
    H.DiscreteStep a b ∨ a = b := by
  cases l with
  | none => exact Or.inr (Subtype.ext jump)
  | some l =>
    obtain ⟨e, he, hj⟩ := jump
    exact Or.inl ⟨e, congrArg Prod.fst he,
      congrArg (fun x => x.2.2) he, hj⟩

/-- Each product jump projects to a genuine jump or an exact state stutter. -/
theorem parallel_step_left {a b : (H₁.parallel H₂).State}
    (step : (H₁.parallel H₂).DiscreteStep a b) :
    H₁.DiscreteStep (H₁.leftState H₂ a) (H₁.leftState H₂ b) ∨
      H₁.leftState H₂ a = H₁.leftState H₂ b := by
  obtain ⟨e, _, _, hj⟩ := step
  exact IdleJump.step_or_eq H₁ e.val.2.1.1 hj.1

theorem parallel_step_right {a b : (H₁.parallel H₂).State}
    (step : (H₁.parallel H₂).DiscreteStep a b) :
    H₂.DiscreteStep (H₁.rightState H₂ a) (H₁.rightState H₂ b) ∨
      H₁.rightState H₂ a = H₁.rightState H₂ b := by
  obtain ⟨e, _, _, hj⟩ := step
  exact IdleJump.step_or_eq H₂ e.val.2.1.2 hj.2

theorem parallel_no_both_idle
    (e : {e // e ∈ (H₁.parallel H₂).edge}) : e.val.2.1 ≠ (none, none) := e.property.1

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``parallel_continuous_left, ``parallel_continuous_right,
      ``parallel_step_left, ``parallel_step_right, ``parallel_no_both_idle] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end STLTableau.HybridAutomaton
