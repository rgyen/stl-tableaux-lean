import STLTableaux.Automata.Composition.SharedParallelComposition
import STLTableaux.Automata.Translation.PrelimStateGoal

/-! Execution projection for the shared-variable product. Jump blocks always
project to reflexive transitive closures. The printed trajectory requires a
nonempty jump block between flows, so the same-segmentation execution transfer
below explicitly requires those projected endpoints to admit a nonempty block.
Prefix membership projects unconditionally using just the first positive flow.
That shorter witness does not establish full-horizon trajectory membership or
preserve a later goal. Neither result is the complete model-checking reduction.
No flow concatenation/restart assumption is introduced. -/

namespace STLTableau.FiniteSignal
variable {Var Var' : Type*}

/-- Restrict real coordinates without changing time or the signal horizon. -/
def reindex (σ : FiniteSignal Var) (f : Var' → Var) : FiniteSignal Var' where
  horizon := σ.horizon
  horizon_pos := σ.horizon_pos
  value := fun t x => σ.value t (f x)

end STLTableau.FiniteSignal

namespace STLTableau.HybridAutomaton
variable {Mode₁ Label₁ Var₁ Mode₂ Label₂ Var₂ Name : Type*}
variable (H₁ : HybridAutomaton Mode₁ Label₁ Var₁) (H₂ : HybridAutomaton Mode₂ Label₂ Var₂)
variable (ι₁ : Var₁ ↪ Name) (ι₂ : Var₂ ↪ Name)
local notation "P" => H₁.parallelOn H₂ ι₁ ι₂
local notation "L" => H₁.leftStateOn H₂ ι₁ ι₂
local notation "R" => H₁.rightStateOn H₂ ι₁ ι₂

theorem parallelOn_jumpClosure_left {a b : (P).State}
    (steps : Relation.ReflTransGen (P).DiscreteStep a b) :
    Relation.ReflTransGen H₁.DiscreteStep (L a) (L b) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih =>
    rcases H₁.parallelOn_step_left H₂ ι₁ ι₂ step with jump | idle
    · exact ih.tail jump
    · exact idle ▸ ih

theorem parallelOn_jumpClosure_right {a b : (P).State}
    (steps : Relation.ReflTransGen (P).DiscreteStep a b) :
    Relation.ReflTransGen H₂.DiscreteStep (R a) (R b) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih =>
    rcases H₁.parallelOn_step_right H₂ ι₁ ι₂ step with jump | idle
    · exact ih.tail jump
    · exact idle ▸ ih

/-- A nonempty product block may consist entirely of left-component idles. -/
theorem parallelOn_nonemptyClosure_left {a b : (P).State}
    (steps : Relation.TransGen (P).DiscreteStep a b) :
    Relation.ReflTransGen H₁.DiscreteStep (L a) (L b) :=
  H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ steps.to_reflTransGen

theorem parallelOn_nonemptyClosure_right {a b : (P).State}
    (steps : Relation.TransGen (P).DiscreteStep a b) :
    Relation.ReflTransGen H₂.DiscreteStep (R a) (R b) :=
  H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ steps.to_reflTransGen

namespace PrelimExecution
variable {H₁ H₂ ι₁ ι₂} {σ : FiniteSignal (JoinedVar ι₁ ι₂)}

/-- Project each flow to the left component, keeping the same boundaries.
The supplied nonempty discrete block connects each pair of successive flows
in that component. A self-loop can supply such a block. -/
def leftOfSteps (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₁.DiscreteStep (L (e.finish i))
        (L (e.start ⟨i.val + 1, hi⟩))) :
    H₁.PrelimExecution (σ.reindex (leftVar ι₁ ι₂)) where
  count := e.count
  nonempty := e.nonempty
  initialState := L e.initialState
  initial_mem := e.initial_mem.1
  start := fun i => L (e.start i)
  finish := fun i => L (e.finish i)
  boundary := e.boundary
  first_zero := e.first_zero
  increasing := e.increasing
  last_le_horizon := e.last_le_horizon
  duration := e.duration
  duration_eq := e.duration_eq
  curve := fun i t x => e.curve i t (leftVar ι₁ ι₂ x)
  continuousStep := fun i => H₁.parallelOn_continuous_left H₂ ι₁ ι₂ (e.continuousStep i)
  initialSteps := H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ e.initialSteps
  discreteSteps := blocks
  signal_eq := by
    intro i t ht
    funext x
    exact congrFun (e.signal_eq i t ht) (leftVar ι₁ ι₂ x)

def rightOfSteps (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₂.DiscreteStep (R (e.finish i))
        (R (e.start ⟨i.val + 1, hi⟩))) :
    H₂.PrelimExecution (σ.reindex (rightVar ι₁ ι₂)) where
  count := e.count
  nonempty := e.nonempty
  initialState := R e.initialState
  initial_mem := e.initial_mem.2
  start := fun i => R (e.start i)
  finish := fun i => R (e.finish i)
  boundary := e.boundary
  first_zero := e.first_zero
  increasing := e.increasing
  last_le_horizon := e.last_le_horizon
  duration := e.duration
  duration_eq := e.duration_eq
  curve := fun i t x => e.curve i t (rightVar ι₁ ι₂ x)
  continuousStep := fun i => H₁.parallelOn_continuous_right H₂ ι₁ ι₂ (e.continuousStep i)
  initialSteps := H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ e.initialSteps
  discreteSteps := blocks
  signal_eq := by
    intro i t ht
    funext x
    exact congrFun (e.signal_eq i t ht) (rightVar ι₁ ι₂ x)

theorem leftOfSteps_visits (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₁.DiscreteStep (L (e.finish i))
        (L (e.start ⟨i.val + 1, hi⟩)))
    {s : (P).State} (visit : e.VisitsState s) :
    (e.leftOfSteps blocks).VisitsState (L s) := by
  rcases visit with ⟨i, t, hs⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
  · refine Or.inl ⟨i, t, ?_⟩
    exact congrArg (fun v => (v.1.1, v.2 ∘ leftVar ι₁ ι₂)) hs
  · exact Or.inr (Or.inl ⟨H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ before,
      H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ after⟩)
  · exact Or.inr (Or.inr ⟨i, hi, H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ before,
      H₁.parallelOn_jumpClosure_left H₂ ι₁ ι₂ after⟩)

theorem rightOfSteps_visits (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₂.DiscreteStep (R (e.finish i))
        (R (e.start ⟨i.val + 1, hi⟩)))
    {s : (P).State} (visit : e.VisitsState s) :
    (e.rightOfSteps blocks).VisitsState (R s) := by
  rcases visit with ⟨i, t, hs⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
  · refine Or.inl ⟨i, t, ?_⟩
    exact congrArg (fun v => (v.1.2, v.2 ∘ rightVar ι₁ ι₂)) hs
  · exact Or.inr (Or.inl ⟨H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ before,
      H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ after⟩)
  · exact Or.inr (Or.inr ⟨i, hi, H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ before,
      H₁.parallelOn_jumpClosure_right H₂ ι₁ ι₂ after⟩)

theorem leftOfSteps_reaches (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₁.DiscreteStep (L (e.finish i))
        (L (e.start ⟨i.val + 1, hi⟩)))
    {goal : Set H₁.State} {s : (P).State} (hg : L s ∈ goal) (visit : e.VisitsState s) :
    H₁.PrelimReachesState (σ.reindex (leftVar ι₁ ι₂)) goal :=
  ⟨e.leftOfSteps blocks, L s, hg, e.leftOfSteps_visits blocks visit⟩

theorem rightOfSteps_reaches (e : (P).PrelimExecution σ)
    (blocks : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      Relation.TransGen H₂.DiscreteStep (R (e.finish i))
        (R (e.start ⟨i.val + 1, hi⟩)))
    {goal : Set H₂.State} {s : (P).State} (hg : R s ∈ goal) (visit : e.VisitsState s) :
    H₂.PrelimReachesState (σ.reindex (rightVar ι₁ ι₂)) goal :=
  ⟨e.rightOfSteps blocks, R s, hg, e.rightOfSteps_visits blocks visit⟩

end PrelimExecution

namespace PrelimExecution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var}

/-- A first-flow prefix of the same signal. This establishes neither a
full-horizon system trajectory nor a goal visited at a later time. -/
def firstFlow (e : H.PrelimExecution σ) : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := e.initialState
  initial_mem := e.initial_mem
  start := fun _ => e.start ⟨0, e.nonempty⟩
  finish := fun _ => e.finish ⟨0, e.nonempty⟩
  boundary := fun i => if i.val = 0 then e.boundary 0 else
    e.boundary ⟨1, by have := e.nonempty; omega⟩
  first_zero := e.first_zero
  increasing := by
    intro i j hij
    have first := e.increasing
      (show (0 : Fin (e.count + 1)) < ⟨1, by have := e.nonempty; omega⟩ by
        change (0 : ℕ) < 1
        decide)
    fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := by
    exact (e.increasing.monotone
      (show (⟨1, by have := e.nonempty; omega⟩ : Fin (e.count + 1)) ≤
        ⟨e.count, by omega⟩ by change 1 ≤ e.count; have := e.nonempty; omega)).trans
      e.last_le_horizon
  duration := fun _ => e.duration ⟨0, e.nonempty⟩
  duration_eq := by
    intro i
    fin_cases i
    exact e.duration_eq ⟨0, e.nonempty⟩
  curve := fun _ => e.curve ⟨0, e.nonempty⟩
  continuousStep := fun _ => e.continuousStep ⟨0, e.nonempty⟩
  initialSteps := e.initialSteps
  discreteSteps := by
    intro i hi
    exact False.elim (by omega)
  signal_eq := by
    intro i t ht
    fin_cases i
    exact e.signal_eq ⟨0, e.nonempty⟩ t ht

end PrelimExecution

namespace PrelimExecution
variable {H₁ H₂ ι₁ ι₂} {σ : FiniteSignal (JoinedVar ι₁ ι₂)}

def firstFlowLeft (e : (P).PrelimExecution σ) :
    H₁.PrelimExecution (σ.reindex (leftVar ι₁ ι₂)) :=
  e.firstFlow.leftOfSteps (by intro i hi; exact False.elim (by change i.val + 1 < 1 at hi; omega))

def firstFlowRight (e : (P).PrelimExecution σ) :
    H₂.PrelimExecution (σ.reindex (rightVar ι₁ ι₂)) :=
  e.firstFlow.rightOfSteps (by intro i hi; exact False.elim (by change i.val + 1 < 1 at hi; omega))

end PrelimExecution

/-- Prefix membership only, not a full-horizon component trajectory. -/
theorem parallelOn_prefix_left (σ : FiniteSignal (JoinedVar ι₁ ι₂))
    (trajectory : (P).IsPrelimPrefix σ) :
    H₁.IsPrelimPrefix (σ.reindex (leftVar ι₁ ι₂)) := by
  obtain ⟨e⟩ := trajectory
  exact ⟨e.firstFlowLeft⟩

theorem parallelOn_prefix_right (σ : FiniteSignal (JoinedVar ι₁ ι₂))
    (trajectory : (P).IsPrelimPrefix σ) :
    H₂.IsPrelimPrefix (σ.reindex (rightVar ι₁ ι₂)) := by
  obtain ⟨e⟩ := trajectory
  exact ⟨e.firstFlowRight⟩

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``parallelOn_jumpClosure_left, ``parallelOn_jumpClosure_right,
      ``parallelOn_nonemptyClosure_left, ``parallelOn_nonemptyClosure_right,
      ``PrelimExecution.leftOfSteps, ``PrelimExecution.rightOfSteps,
      ``PrelimExecution.leftOfSteps_visits, ``PrelimExecution.rightOfSteps_visits,
      ``PrelimExecution.leftOfSteps_reaches, ``PrelimExecution.rightOfSteps_reaches,
      ``PrelimExecution.firstFlow, ``PrelimExecution.firstFlowLeft,
      ``PrelimExecution.firstFlowRight, ``parallelOn_prefix_left,
      ``parallelOn_prefix_right] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.HybridAutomaton
