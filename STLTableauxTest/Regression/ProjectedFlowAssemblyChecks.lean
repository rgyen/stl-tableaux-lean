import STLTableaux.Automata.Recognition.ProjectedFlowAssembly

/-! Assemble two nonconstant flows with a two-jump connector. The leading
jump block visits a goal. Auxiliary coordinates can reset while the
physical coordinate stays fixed. -/
namespace ProjectedFlowAssemblyChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton (Fin 5) Unit Bool where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := Set.univ
  initial := {s | s.1 = 0 ∧ s.2 false = 0 ∧ s.2 true = 0}
  invariant := Set.univ
  flow := fun s t v => v false = s.2 false + t ∧ v true = s.2 true
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total
        dsimp only [Prod.snd] at *
        constructor
        · rw [total.1, first.1]; push_cast; ring
        · exact total.2.trans first.2.symm)
    (by intro q v a b r s first second
        dsimp only [Prod.snd] at *
        constructor
        · rw [second.1, first.1]; push_cast; ring
        · exact second.2.trans first.2)
  jump := fun _ a b => b.2 false = a.2 false

def state (m : Fin 5) (x z : ℝ) : H.State :=
  ⟨(m, fun b => if b then z else x), Set.mem_univ _⟩
noncomputable def ρ : FiniteSignal Unit := ⟨2, by norm_num, fun t _ => t.val⟩
def coordinate (_ : Unit) : Bool := false
def extend (v : Unit → ℝ) : Bool → ℝ := fun b => if b then 0 else v ()

theorem jump (m n : Fin 5) (x a b : ℝ) :
    H.DiscreteStep (state m x a) (state n x b) :=
  ⟨⟨(m, (), n), Set.mem_univ _⟩, rfl, rfl, rfl⟩

noncomputable def piece (m : Fin 5) (base aux : ℝ) :
    ProjectedFlowPiece H ρ coordinate where
  left := base
  duration := 1
  positive := by norm_num
  start := state m base aux
  finish := state m (base + 1) aux
  curve := fun u b => if b then aux else base + u.val
  step := by
    refine ⟨rfl, ?_, rfl, ?_⟩
    · funext b; cases b <;> simp [state]
    · intro u
      exact ⟨⟨rfl, rfl⟩, Set.mem_univ _⟩
  observe := by intro t u equal before x; exact equal

noncomputable def first := piece 2 0 0
noncomputable def second := piece 4 (0 + 1) 9
def middleGoal : H.State := state 3 (0 + 1) 7
def initial : H.State := state 0 0 0
def initialGoal : H.State := state 1 0 5

theorem connector : Relation.ReflTransGen H.DiscreteStep first.finish second.start :=
  (Relation.ReflTransGen.single (jump 2 3 (0 + 1) 0 7)).trans
    (.single (jump 3 4 (0 + 1) 7 9))
noncomputable def word := ProjectedFlowWord.cons first connector (.last second)

theorem middle_visit : word.VisitsState middleGoal :=
  Or.inr (Or.inl ⟨.single (jump 2 3 (0 + 1) 0 7),
    .single (jump 3 4 (0 + 1) 7 9)⟩)

theorem packed_full_and_skipped_goals :
    ∃ (aug : FiniteSignal Bool) (e : H.PrelimExecution aug),
      aug.horizon = ρ.horizon ∧ e.ReachesHorizon ∧
      (∀ (t : aug.Time) (u : ρ.Time), t.val = u.val →
        aug.value t false = ρ.value u ()) ∧
      e.VisitsState middleGoal ∧ e.VisitsState initialGoal := by
  obtain ⟨aug, e, horizon, projects, _, _, _, stop, visits, initials⟩ :=
    word.toExecution extend (by intro v x; cases x; rfl) initial
      ⟨rfl, rfl, rfl⟩ rfl
      ((Relation.ReflTransGen.single (jump 0 1 0 0 5)).trans
        (.single (jump 1 2 0 5 0))) (by norm_num [word, first, second, piece, ρ])
  refine ⟨aug, e, horizon, ?_, ?_, visits _ middle_visit, ?_⟩
  · unfold PrelimExecution.ReachesHorizon
    rw [stop, horizon]
    norm_num [ρ, first, second, piece]
  · intro t u equal
    exact projects t u equal ()
  · exact initials initialGoal (.single (jump 0 1 0 0 5))
      (.single (jump 1 2 0 5 0))

run_elab do
  for name in #[``connector, ``middle_visit, ``packed_full_and_skipped_goals] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"
end ProjectedFlowAssemblyChecks
