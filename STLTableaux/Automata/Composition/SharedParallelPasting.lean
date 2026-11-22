import STLTableaux.Automata.Composition.SharedParallelConstruction
import STLTableaux.Automata.Composition.SharedParallelExecution
import STLTableaux.Automata.Execution.ObservedFlowExecution

/-! Finite pasting on a common time decomposition. The input contains only
component flow and jump/idle conditions, not a product execution. A joint
valuation expresses agreement of shared variables, including closed flow
endpoints and intermediate discrete states. Empty interflow connectors are
allowed; standard trajectory concatenation removes only idle boundaries.

This is the aligned finite-word step of the standard composition theorem.
Producing a common decomposition from independent component witnesses is a
separate step, not a premise hidden in an execution/goal equivalence. -/
namespace STLTableau.HybridAutomaton
variable {M₁ L₁ V₁ M₂ L₂ V₂ Name : Type*}
variable (H₁ : HybridAutomaton M₁ L₁ V₁) (H₂ : HybridAutomaton M₂ L₂ V₂)
variable (ι₁ : V₁ ↪ Name) (ι₂ : V₂ ↪ Name)
local notation "P" => H₁.parallelOn H₂ ι₁ ι₂
local notation "left" => H₁.leftStateOn H₂ ι₁ ι₂
local notation "right" => H₁.rightStateOn H₂ ι₁ ι₂

/-- One pair of component actions, including one-sided idles. Neither a
product edge nor a product jump is an input to this relation. -/
def ComponentStep (a b : (P).State) : Prop :=
  ∃ l₁ l₂, (l₁, l₂) ≠ (none, none) ∧
    H₁.IdleEdge (left a).val.1 l₁ (left b).val.1 ∧
    H₂.IdleEdge (right a).val.1 l₂ (right b).val.1 ∧
    H₁.IdleJump l₁ (left a).val (left b).val ∧
    H₂.IdleJump l₂ (right a).val (right b).val

theorem ComponentStep.discrete {a b : (P).State}
    (step : ComponentStep H₁ H₂ ι₁ ι₂ a b) : (P).DiscreteStep a b :=
  (H₁.parallelOn_discrete_iff H₂ ι₁ ι₂ a b).mpr step

theorem componentSteps_discrete {a b : (P).State}
    (steps : Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) a b) :
    Relation.ReflTransGen (P).DiscreteStep a b := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.discrete

/-- A finite common decomposition carrying only local component conditions.
The joint state type enforces the two invariants and shared-value agreement;
it does not assert any product flow, jump, execution, or goal reachability. -/
structure ParallelComponentData (σ : FiniteSignal (JoinedVar ι₁ ι₂)) where
  count : ℕ
  nonempty : 0 < count
  initialState : (P).State
  initial_left : (left initialState).val ∈ H₁.initial
  initial_right : (right initialState).val ∈ H₂.initial
  start : Fin count → (P).State
  finish : Fin count → (P).State
  boundary : Fin (count + 1) → ℝ
  first_zero : boundary 0 = 0
  increasing : StrictMono boundary
  last_le_horizon : boundary ⟨count, by omega⟩ ≤ σ.horizon
  duration : Fin count → NNReal
  duration_eq : ∀ i, (duration i : ℝ) = boundary i.succ - boundary i.castSucc
  curve : ∀ i, HybridFlow.Curve (JoinedVar ι₁ ι₂) (duration i)
  flow_left : ∀ i, H₁.ContinuousStep (left (start i)) (left (finish i)) (duration i)
    (fun t x => curve i t (leftVar ι₁ ι₂ x))
  flow_right : ∀ i, H₂.ContinuousStep (right (start i)) (right (finish i)) (duration i)
    (fun t x => curve i t (rightVar ι₁ ι₂ x))
  initialSteps : Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂)
    initialState (start ⟨0, nonempty⟩)
  discreteSteps : ∀ (i : Fin count) (hi : i.val + 1 < count),
    Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂)
      (finish i) (start ⟨i.val + 1, hi⟩)
  observe_left : ∀ (i : Fin count) (t : σ.Time)
    (ht : boundary i.castSucc ≤ t.val ∧ t.val < boundary i.succ),
    ∀ x, σ.value t (leftVar ι₁ ι₂ x) =
      curve i ⟨t.val - boundary i.castSucc, by
        constructor <;> linarith [ht.1, ht.2, duration_eq i]⟩ (leftVar ι₁ ι₂ x)
  observe_right : ∀ (i : Fin count) (t : σ.Time)
    (ht : boundary i.castSucc ≤ t.val ∧ t.val < boundary i.succ),
    ∀ x, σ.value t (rightVar ι₁ ι₂ x) =
      curve i ⟨t.val - boundary i.castSucc, by
        constructor <;> linarith [ht.1, ht.2, duration_eq i]⟩ (rightVar ι₁ ι₂ x)

namespace ParallelComponentData
variable {H₁ H₂ ι₁ ι₂} {σ : FiniteSignal (JoinedVar ι₁ ι₂)}
variable (d : ParallelComponentData H₁ H₂ ι₁ ι₂ σ)

def lastIndex : Fin d.count := ⟨d.count - 1, by have := d.nonempty; omega⟩

def finalState : (P).State := d.finish d.lastIndex

/-- Visits refer to the component word, including its discrete intermediate
states. No product reachability occurs in this definition. -/
def VisitsState (s : (P).State) : Prop :=
  (∃ i u, s.val = ((d.start i).val.1, d.curve i u)) ∨
  (Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) d.initialState s ∧
    Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) s (d.start ⟨0, d.nonempty⟩)) ∨
  ∃ (i : Fin d.count) (hi : i.val + 1 < d.count),
    Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) (d.finish i) s ∧
    Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) s (d.start ⟨i.val + 1, hi⟩)

def observedFlow (i : Fin d.count) : ObservedFlow (P) σ where
  start := d.start i
  finish := d.finish i
  beginTime := d.boundary i.castSucc
  endTime := d.boundary i.succ
  duration := d.duration i
  positive := by
    rw [d.duration_eq]
    exact sub_pos.mpr (d.increasing (show i.castSucc < i.succ by simp))
  duration_eq := d.duration_eq i
  curve := d.curve i
  step := (H₁.parallelOn_continuous_iff H₂ ι₁ ι₂).mpr ⟨d.flow_left i, d.flow_right i⟩
  observe := by
    intro t ht
    funext x
    rcases every_joined_variable ι₁ ι₂ x with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact d.observe_left i t ht v
    · exact d.observe_right i t ht v

theorem observedChain (k : ℕ) (hk : k < d.count) :
    ∃ word : ObservedFlowChain (P) σ (Relation.ReflTransGen (P).DiscreteStep)
        (d.start ⟨0, d.nonempty⟩) (d.boundary 0)
        (d.finish ⟨k, hk⟩) (d.boundary (⟨k, hk⟩ : Fin d.count).succ),
      (∀ (j : Fin d.count), j.val ≤ k → ∀ s,
        (d.observedFlow j).VisitsState s → word.VisitsState s) ∧
      (∀ (j : Fin d.count) (hj : j.val + 1 < d.count), j.val < k → ∀ s,
        Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) (d.finish j) s →
        Relation.ReflTransGen (ComponentStep H₁ H₂ ι₁ ι₂) s (d.start ⟨j.val + 1, hj⟩) →
        word.VisitsState s) := by
  induction k with
  | zero =>
    refine ⟨.single (d.observedFlow ⟨0, d.nonempty⟩), ?_, ?_⟩
    · intro j hj s visit
      have same : j = ⟨0, d.nonempty⟩ := Fin.ext (by change j.val = 0; omega)
      change (d.observedFlow ⟨0, d.nonempty⟩).VisitsState s
      simpa only [same] using visit
    · intro j hj impossible
      omega
  | succ k ih =>
    have old : k < d.count := by omega
    obtain ⟨word, flows, jumps⟩ := ih old
    let i : Fin d.count := ⟨k, old⟩
    let j : Fin d.count := ⟨k + 1, hk⟩
    refine ⟨.snoc word (d.observedFlow j) rfl
      (componentSteps_discrete H₁ H₂ ι₁ ι₂ (d.discreteSteps i hk)), ?_, ?_⟩
    · intro l hl s visit
      by_cases previous : l.val ≤ k
      · exact Or.inl (flows l previous s visit)
      · have same : l = j := Fin.ext (by dsimp [j]; omega)
        exact Or.inr (Or.inr (by simpa only [same] using visit))
    · intro l hl earlier s before after
      by_cases previous : l.val < k
      · exact Or.inl (jumps l hl previous s before after)
      · have same : l = i := Fin.ext (by dsimp [i]; omega)
        subst l
        exact Or.inr (Or.inl ⟨componentSteps_discrete H₁ H₂ ι₁ ι₂ before,
          componentSteps_discrete H₁ H₂ ι₁ ι₂ after⟩)

/-- Construct the product execution from local component data. The exact stop,
initial/final states and every represented state visit are preserved. -/
theorem execution :
    ∃ out : (P).PrelimExecution σ,
      out.initialState = d.initialState ∧ out.finalState = d.finalState ∧
      out.boundary ⟨out.count, by omega⟩ = d.boundary ⟨d.count, by omega⟩ ∧
      ∀ s, d.VisitsState s → out.VisitsState s := by
  obtain ⟨word, flows, jumps⟩ := d.observedChain (d.count - 1)
    (by have := d.nonempty; omega)
  obtain ⟨normal, normalize⟩ := word.normalize
  have lastTime : d.lastIndex.succ = (⟨d.count, by omega⟩ : Fin (d.count + 1)) := by
    apply Fin.ext
    change d.count - 1 + 1 = d.count
    have := d.nonempty
    omega
  obtain ⟨out, oi, of, ol, ot, preserve⟩ := normal.toExecution d.initialState
    ⟨d.initial_left, d.initial_right⟩ d.first_zero
    (componentSteps_discrete H₁ H₂ ι₁ ι₂ d.initialSteps)
    (lastTime.symm ▸ d.last_le_horizon)
  refine ⟨out, oi, ol, ot.trans (congrArg d.boundary lastTime), ?_⟩
  intro s visit
  rcases visit with ⟨i, t, hs⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
  · exact preserve s (normalize s (flows i (by have := i.isLt; omega) s ⟨t, hs⟩))
  · exact Or.inr (Or.inl ⟨oi.symm ▸ componentSteps_discrete H₁ H₂ ι₁ ι₂ before,
      of.symm ▸ componentSteps_discrete H₁ H₂ ι₁ ι₂ after⟩)
  · exact preserve s (normalize s (jumps i hi (by omega) s before after))

theorem full_execution (full : d.boundary ⟨d.count, by omega⟩ = σ.horizon) :
    ∃ out : (P).PrelimExecution σ, out.ReachesHorizon ∧
      out.finalState = d.finalState ∧ ∀ s, d.VisitsState s → out.VisitsState s := by
  obtain ⟨out, _, final, stop, visits⟩ := d.execution
  exact ⟨out, stop.trans full, final, visits⟩

/-- A component goal can be visited earlier than the horizon, including
inside a discrete block. The witness is the same full product execution. -/
theorem full_right_goal (full : d.boundary ⟨d.count, by omega⟩ = σ.horizon)
    (goal : Set H₂.State) (reached : ∃ s, right s ∈ goal ∧ d.VisitsState s) :
    ∃ out : (P).PrelimExecution σ, out.ReachesHorizon ∧
      ∃ s, right s ∈ goal ∧ out.VisitsState s := by
  obtain ⟨out, horizon, _, visits⟩ := d.full_execution full
  obtain ⟨s, member, visit⟩ := reached
  exact ⟨out, horizon, s, member, visits s visit⟩

run_elab do
  for n in #[``ComponentStep.discrete, ``componentSteps_discrete,
      ``observedChain, ``execution, ``full_execution, ``full_right_goal] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end ParallelComponentData
end STLTableau.HybridAutomaton
