import STLTableaux.Automata.Composition.SharedParallelComposition

namespace SharedParallelCompositionChecks
open STLTableau STLTableau.HybridAutomaton

def ι : Unit ↪ Unit := Function.Embedding.refl _

def resetter (k : ℝ) : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := Set.univ
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ s' => s'.2 () = k

def state (k l x : ℝ) : ((resetter k).parallelOn (resetter l) ι ι).State :=
  ⟨(((), ()), fun _ => x), Set.mem_univ _, Set.mem_univ _⟩

def both (k l : ℝ) : {e // e ∈ ((resetter k).parallelOn (resetter l) ι ι).edge} :=
  ⟨(((), ()), (some (), some ()), ((), ())),
    by exact ⟨by decide, Set.mem_univ _, Set.mem_univ _⟩⟩

def leftOnly (k l : ℝ) : {e // e ∈ ((resetter k).parallelOn (resetter l) ι ι).edge} :=
  ⟨(((), ()), (some (), none), ((), ())),
    by exact ⟨by decide, Set.mem_univ _, rfl⟩⟩

theorem shared_value (k l : ℝ)
    (s : ((resetter k).parallelOn (resetter l) ι ι).State) :
    ((resetter k).leftStateOn (resetter l) ι ι s).val.2 () =
      ((resetter k).rightStateOn (resetter l) ι ι s).val.2 () :=
  (resetter k).parallelOn_shared_value (resetter l) ι ι s rfl

theorem compatible_shared_reset :
    ((resetter 1).parallelOn (resetter 1) ι ι).DiscreteStep (state 1 1 0) (state 1 1 1) := by
  let old : {e // e ∈ (resetter 1).edge} := ⟨((), (), ()), Set.mem_univ _⟩
  exact ⟨both 1 1, rfl, rfl, ⟨old, rfl, rfl⟩, ⟨old, rfl, rfl⟩⟩

theorem incompatible_shared_reset
    (a b : ((resetter 1).parallelOn (resetter 2) ι ι).State) :
    ¬ ((resetter 1).parallelOn (resetter 2) ι ι).jump (both 1 2) a.val b.val := by
  rintro ⟨⟨_, _, hl⟩, ⟨_, _, hr⟩⟩
  change b.val.2 (leftVar ι ι ()) = 1 at hl
  change b.val.2 (rightVar ι ι ()) = 2 at hr
  have same := shared_variable_eq ι ι (x := ()) (y := ()) rfl
  rw [same] at hl
  linarith

theorem idle_cannot_overwrite_shared :
    ¬ ((resetter 1).parallelOn (resetter 1) ι ι).jump (leftOnly 1 1)
      (state 1 1 0).val (state 1 1 1).val := by
  intro jump
  have equal : ((), fun _ : Unit => (0 : ℝ)) = ((), fun _ : Unit => (1 : ℝ)) := jump.2
  have value := congrFun (congrArg Prod.snd equal) ()
  norm_num at value

def fixed (k : ℝ) : HybridAutomaton Unit Unit Unit :=
  { resetter k with
    invariant := {s | s.2 () = k}
    trajectory_closed := HybridFlow.Closed.constant _ }

theorem incompatible_shared_invariants
    (s : ((fixed 0).parallelOn (fixed 1) ι ι).State) : False := by
  have hl : s.val.2 (leftVar ι ι ()) = 0 := s.property.1
  have hr : s.val.2 (rightVar ι ι ()) = 1 := s.property.2
  rw [shared_variable_eq ι ι (x := ()) (y := ()) rfl] at hl
  linarith

/-- One common coordinate and one private coordinate in each component. -/
def leftName : Fin 2 ↪ Fin 3 := ⟨Fin.castSucc, Fin.castSucc_injective 2⟩

def rightName : Fin 2 ↪ Fin 3 :=
  ⟨fun i => if i = 0 then 0 else 2, by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

example : leftVar leftName rightName 0 = rightVar leftName rightName 0 :=
  shared_variable_eq _ _ rfl

example : leftVar leftName rightName 1 ≠ rightVar leftName rightName 1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [leftVar, rightVar, leftName, rightName] at hv
  exact (by decide : (1 : Fin 3) ≠ 2) hv

def privateReset : HybridAutomaton Unit Unit (Fin 2) where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := Set.univ
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ s' => s'.2 1 = 1

def mixedState (update : Bool) : (privateReset.parallelOn privateReset leftName rightName).State :=
  ⟨(((), ()), fun x => if update ∧ x.val = 1 then 1 else 0),
    Set.mem_univ _, Set.mem_univ _⟩

/-- Idling the right side does not freeze a left-private variable. -/
theorem private_update_with_idle :
    (privateReset.parallelOn privateReset leftName rightName).DiscreteStep
      (mixedState false) (mixedState true) := by
  let e : {e // e ∈ (privateReset.parallelOn privateReset leftName rightName).edge} :=
    ⟨(((), ()), (some (), none), ((), ())),
      by exact ⟨by decide, Set.mem_univ _, rfl⟩⟩
  let old : {e // e ∈ privateReset.edge} := ⟨((), (), ()), Set.mem_univ _⟩
  refine ⟨e, rfl, rfl, ⟨old, rfl, ?_⟩, ?_⟩
  · change (if (true : Bool) ∧ (leftVar leftName rightName 1).val = 1
        then (1 : ℝ) else 0) = 1
    norm_num [leftVar, leftName]
  · change ((), _) = ((), _)
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> norm_num [Function.comp_def, mixedState, rightVar, rightName,
        show (2 : Fin 3) ≠ 1 from by decide]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``shared_value, ``compatible_shared_reset, ``incompatible_shared_reset,
      ``idle_cannot_overwrite_shared, ``incompatible_shared_invariants,
      ``private_update_with_idle] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end SharedParallelCompositionChecks
