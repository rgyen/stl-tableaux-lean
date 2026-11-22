import STLTableaux.Automata.Execution.HybridAutomata

/-! Regression for final endpoint observation. An early goal is permitted
when its value is observed, but a signal with x = -1 everywhere cannot enter
the goal x ≥ 0 early. No canonical finite-root counterexample is claimed. -/
namespace EarlyStopEndpointChecks
open STLTableau
noncomputable section

-- false = the real variable x, true = the global clock.
def value (x c : ℝ) : Bool → ℝ := fun b => if b then c else x

def H : HybridAutomaton Bool Unit Bool where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(false, (), true)}
  initial := {s | s.1 = false ∧ s.2 true = 0}
  invariant := {s | s.2 true ≤ 2 ∧ (s.1 = true → 0 ≤ s.2 false)}
  flow := fun s t v => v true = s.2 true + t
  trajectory_closed := by
    apply HybridFlow.Closed.of_rebase_add
    · intro q v a b r s first total
      dsimp only [Prod.snd] at *
      rw [total, first]
      push_cast
      ring
    · intro q v a b r s first second
      dsimp only [Prod.snd] at *
      rw [second, first]
      push_cast
      ring
  jump := fun _ s s' => s'.2 = s.2 ∧ s'.2 true < 2

def σ : FiniteSignal Bool := ⟨2, by norm_num, fun t => value (-1) t.val⟩

def observedSignal : FiniteSignal Bool :=
  ⟨2, by norm_num, fun t => value (if t.val = 1 then 1 else -1) t.val⟩

def start : H.State := ⟨(false, value (-1) 0), by simp [H, value]⟩
def finish : H.State := ⟨(false, value 1 1), by norm_num [H, value]⟩
def goal : H.State := ⟨(true, value 1 1), by norm_num [H, value]⟩

def curve (t : Set.Icc (0 : ℝ) (1 : NNReal)) : Bool → ℝ :=
  value (if t.val < 1 then -1 else 1) t.val

theorem final_jump : H.DiscreteStep finish goal := by
  refine ⟨⟨(false, (), true), rfl⟩, rfl, rfl, rfl, ?_⟩
  norm_num [goal, value]

def execution : H.Execution observedSignal where
  count := 1
  nonempty := by decide
  initialState := start
  initial_signal_eq := by simp [observedSignal, start]
  initial_mem := ⟨rfl, rfl⟩
  start := fun _ => start
  finish := fun _ => finish
  boundary := fun i => (i.val : ℝ)
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  last_le_horizon := by norm_num [observedSignal]
  duration := fun _ => 1
  duration_eq := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    norm_num
  curve := fun _ => curve
  continuousStep := by
    intro i
    refine ⟨rfl, ?_, ?_, ?_⟩
    · funext b
      simp [curve, start, value]
    · funext b
      simp [curve, finish, value]
    · intro t
      refine ⟨?_, ?_, ?_⟩
      · change t.val = 0 + t.val
        exact (zero_add _).symm
      · change t.val ≤ 2
        have := t.property.2
        norm_num at this
        linarith
      · intro he
        cases he
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  finalState := goal
  finalSteps := .single final_jump
  final_signal_eq := by
    intro t ht
    have ht' : t.val = 1 := by simpa using ht
    funext b
    simp [observedSignal, goal, value, ht']
  signal_eq := by
    intro i t ht positive
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have ht' : t.val < 1 := by simpa using ht.2
    funext b
    simp [observedSignal, curve, value, ht', ne_of_lt ht']

theorem reaches_goal : H.Reaches observedSignal {true} := ⟨execution, rfl⟩

theorem signal_atom_never_holds (t : σ.Time) : ¬ (0 ≤ σ.value t false) := by
  change ¬ (0 ≤ (-1 : ℝ))
  norm_num

theorem early_stop : execution.boundary ⟨execution.count, by decide⟩ < observedSignal.horizon := by
  change ((1 : ℕ) : ℝ) < 2
  norm_num

theorem constant_signal_no_early_goal (e : H.Execution σ)
    (he : e.boundary ⟨e.count, by omega⟩ < σ.horizon) :
    e.finalState.val.1 ≠ true := by
  intro hg
  have hn : 0 ≤ e.boundary ⟨e.count, by omega⟩ := by
    rw [← e.first_zero]
    exact e.increasing.monotone (by change 0 ≤ e.count; omega)
  let t : σ.Time := ⟨e.boundary ⟨e.count, by omega⟩, hn, he⟩
  have ha : 0 ≤ e.finalState.val.2 false := e.finalState.property.2 hg
  rw [← e.final_signal_eq t rfl] at ha
  exact signal_atom_never_holds t ha

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execution, ``final_jump, ``reaches_goal,
      ``signal_atom_never_holds, ``early_stop, ``constant_signal_no_early_goal] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

end
end EarlyStopEndpointChecks
