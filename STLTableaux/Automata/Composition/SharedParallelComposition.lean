import STLTableaux.Automata.Composition.ParallelComposition

/-! Parallel composition with shared variable names. The variable type is
exactly the union of the component name ranges. A single valuation supplies
both restrictions, so overlap is equality by construction, not an extra
assumption or a freely chosen copy of the observed signal. -/
namespace STLTableau.HybridAutomaton
variable {Mode₁ Label₁ Var₁ Mode₂ Label₂ Var₂ Name : Type*}

abbrev JoinedVar (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name) :=
  {x : Name // x ∈ Set.range ι₁ ∪ Set.range ι₂}

def leftVar (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name) (x : Var₁) : JoinedVar ι₁ ι₂ :=
  ⟨ι₁ x, Or.inl ⟨x, rfl⟩⟩

def rightVar (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name) (x : Var₂) : JoinedVar ι₁ ι₂ :=
  ⟨ι₂ x, Or.inr ⟨x, rfl⟩⟩

theorem shared_variable_eq (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name)
    {x : Var₁} {y : Var₂} (same : ι₁ x = ι₂ y) :
    leftVar ι₁ ι₂ x = rightVar ι₁ ι₂ y := Subtype.ext same

theorem every_joined_variable (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name)
    (x : JoinedVar ι₁ ι₂) :
    (∃ a, leftVar ι₁ ι₂ a = x) ∨ (∃ b, rightVar ι₁ ι₂ b = x) := by
  rcases x.property with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨a, Subtype.ext ha⟩
  · exact Or.inr ⟨b, Subtype.ext hb⟩

def parallelOn (H₁ : HybridAutomaton Mode₁ Label₁ Var₁)
    (H₂ : HybridAutomaton Mode₂ Label₂ Var₂) (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name) :
    HybridAutomaton (Mode₁ × Mode₂) (Option Label₁ × Option Label₂) (JoinedVar ι₁ ι₂) where
  modes_finite := by
    letI := H₁.modes_finite
    letI := H₂.modes_finite
    infer_instance
  variables_finite := by
    letI := H₁.variables_finite
    letI := H₂.variables_finite
    exact ((Set.finite_range ι₁).union (Set.finite_range ι₂)).to_subtype
  edge := {e | e.2.1 ≠ (none, none) ∧
    H₁.IdleEdge e.1.1 e.2.1.1 e.2.2.1 ∧ H₂.IdleEdge e.1.2 e.2.1.2 e.2.2.2}
  initial := {s | (s.1.1, s.2 ∘ leftVar ι₁ ι₂) ∈ H₁.initial ∧
    (s.1.2, s.2 ∘ rightVar ι₁ ι₂) ∈ H₂.initial}
  invariant := {s | (s.1.1, s.2 ∘ leftVar ι₁ ι₂) ∈ H₁.invariant ∧
    (s.1.2, s.2 ∘ rightVar ι₁ ι₂) ∈ H₂.invariant}
  flow := fun s t v =>
    H₁.flow (s.1.1, s.2 ∘ leftVar ι₁ ι₂) t (v ∘ leftVar ι₁ ι₂) ∧
    H₂.flow (s.1.2, s.2 ∘ rightVar ι₁ ι₂) t (v ∘ rightVar ι₁ ι₂)
  trajectory_closed := H₁.trajectory_closed.parallel H₂.trajectory_closed
    (leftVar ι₁ ι₂) (rightVar ι₁ ι₂)
  jump := fun e s s' =>
    H₁.IdleJump e.val.2.1.1 (s.1.1, s.2 ∘ leftVar ι₁ ι₂)
      (s'.1.1, s'.2 ∘ leftVar ι₁ ι₂) ∧
    H₂.IdleJump e.val.2.1.2 (s.1.2, s.2 ∘ rightVar ι₁ ι₂)
      (s'.1.2, s'.2 ∘ rightVar ι₁ ι₂)

variable (H₁ : HybridAutomaton Mode₁ Label₁ Var₁) (H₂ : HybridAutomaton Mode₂ Label₂ Var₂)
variable (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name)

def leftStateOn (s : (H₁.parallelOn H₂ ι₁ ι₂).State) : H₁.State :=
  ⟨(s.val.1.1, s.val.2 ∘ leftVar ι₁ ι₂), s.property.1⟩

def rightStateOn (s : (H₁.parallelOn H₂ ι₁ ι₂).State) : H₂.State :=
  ⟨(s.val.1.2, s.val.2 ∘ rightVar ι₁ ι₂), s.property.2⟩

theorem parallelOn_shared_value (s : (H₁.parallelOn H₂ ι₁ ι₂).State)
    {x : Var₁} {y : Var₂} (same : ι₁ x = ι₂ y) :
    (H₁.leftStateOn H₂ ι₁ ι₂ s).val.2 x =
      (H₁.rightStateOn H₂ ι₁ ι₂ s).val.2 y :=
  congrArg s.val.2 (shared_variable_eq ι₁ ι₂ same)

theorem parallelOn_initial_left (s : (H₁.parallelOn H₂ ι₁ ι₂).State)
    (hi : s.val ∈ (H₁.parallelOn H₂ ι₁ ι₂).initial) :
    (H₁.leftStateOn H₂ ι₁ ι₂ s).val ∈ H₁.initial := hi.1

theorem parallelOn_initial_right (s : (H₁.parallelOn H₂ ι₁ ι₂).State)
    (hi : s.val ∈ (H₁.parallelOn H₂ ι₁ ι₂).initial) :
    (H₁.rightStateOn H₂ ι₁ ι₂ s).val ∈ H₂.initial := hi.2

theorem parallelOn_continuous_left {a b : (H₁.parallelOn H₂ ι₁ ι₂).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → JoinedVar ι₁ ι₂ → ℝ}
    (step : (H₁.parallelOn H₂ ι₁ ι₂).ContinuousStep a b r γ) :
    H₁.ContinuousStep (H₁.leftStateOn H₂ ι₁ ι₂ a) (H₁.leftStateOn H₂ ι₁ ι₂ b) r
      (fun t x => γ t (leftVar ι₁ ι₂ x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun q : Mode₁ × Mode₂ => q.1) step.1
  · funext x
    exact congrFun step.2.1 (leftVar ι₁ ι₂ x)
  · funext x
    exact congrFun step.2.2.1 (leftVar ι₁ ι₂ x)
  · intro t
    exact ⟨(step.2.2.2 t).1.1, (step.2.2.2 t).2.1⟩

theorem parallelOn_continuous_right {a b : (H₁.parallelOn H₂ ι₁ ι₂).State} {r : NNReal}
    {γ : Set.Icc (0 : ℝ) r → JoinedVar ι₁ ι₂ → ℝ}
    (step : (H₁.parallelOn H₂ ι₁ ι₂).ContinuousStep a b r γ) :
    H₂.ContinuousStep (H₁.rightStateOn H₂ ι₁ ι₂ a) (H₁.rightStateOn H₂ ι₁ ι₂ b) r
      (fun t x => γ t (rightVar ι₁ ι₂ x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun q : Mode₁ × Mode₂ => q.2) step.1
  · funext x
    exact congrFun step.2.1 (rightVar ι₁ ι₂ x)
  · funext x
    exact congrFun step.2.2.1 (rightVar ι₁ ι₂ x)
  · intro t
    exact ⟨(step.2.2.2 t).1.2, (step.2.2.2 t).2.2⟩

theorem parallelOn_step_left {a b : (H₁.parallelOn H₂ ι₁ ι₂).State}
    (step : (H₁.parallelOn H₂ ι₁ ι₂).DiscreteStep a b) :
    H₁.DiscreteStep (H₁.leftStateOn H₂ ι₁ ι₂ a) (H₁.leftStateOn H₂ ι₁ ι₂ b) ∨
      H₁.leftStateOn H₂ ι₁ ι₂ a = H₁.leftStateOn H₂ ι₁ ι₂ b := by
  obtain ⟨e, _, _, hj⟩ := step
  exact IdleJump.step_or_eq H₁ e.val.2.1.1 hj.1

theorem parallelOn_step_right {a b : (H₁.parallelOn H₂ ι₁ ι₂).State}
    (step : (H₁.parallelOn H₂ ι₁ ι₂).DiscreteStep a b) :
    H₂.DiscreteStep (H₁.rightStateOn H₂ ι₁ ι₂ a) (H₁.rightStateOn H₂ ι₁ ι₂ b) ∨
      H₁.rightStateOn H₂ ι₁ ι₂ a = H₁.rightStateOn H₂ ι₁ ι₂ b := by
  obtain ⟨e, _, _, hj⟩ := step
  exact IdleJump.step_or_eq H₂ e.val.2.1.2 hj.2

theorem parallelOn_no_both_idle
    (e : {e // e ∈ (H₁.parallelOn H₂ ι₁ ι₂).edge}) :
    e.val.2.1 ≠ (none, none) := e.property.1

/-- An idle component keeps shared variables fixed as well; it does not
permit the other component to overwrite an overlapping coordinate. -/
theorem parallelOn_right_idle_shared {a b : (H₁.parallelOn H₂ ι₁ ι₂).State}
    (e : {e // e ∈ (H₁.parallelOn H₂ ι₁ ι₂).edge})
    (jump : (H₁.parallelOn H₂ ι₁ ι₂).jump e a.val b.val)
    (idle : e.val.2.1.2 = none) {x : Var₁} {y : Var₂} (same : ι₁ x = ι₂ y) :
    (H₁.leftStateOn H₂ ι₁ ι₂ a).val.2 x =
      (H₁.leftStateOn H₂ ι₁ ι₂ b).val.2 x := by
  have hj : H₂.IdleJump e.val.2.1.2
      (H₁.rightStateOn H₂ ι₁ ι₂ a).val (H₁.rightStateOn H₂ ι₁ ι₂ b).val := jump.2
  rw [idle] at hj
  have hv := congrFun (congrArg Prod.snd hj) y
  exact (H₁.parallelOn_shared_value H₂ ι₁ ι₂ a same).trans
    (hv.trans (H₁.parallelOn_shared_value H₂ ι₁ ι₂ b same).symm)

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``shared_variable_eq, ``every_joined_variable, ``parallelOn_shared_value,
      ``parallelOn_continuous_left, ``parallelOn_continuous_right,
      ``parallelOn_step_left, ``parallelOn_step_right, ``parallelOn_right_idle_shared] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end STLTableau.HybridAutomaton
