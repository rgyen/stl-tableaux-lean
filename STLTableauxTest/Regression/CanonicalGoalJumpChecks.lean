import STLTableaux.Automata.Translation.CanonicalTableauExecution

/-! Definition 5.3 and Lemma 5.5. A horizon jump enters a final mode labelled
only by the closed marker. The jump uses the last flow endpoint. -/
namespace CanonicalGoalJumpChecks
open STLTableau STLTableau.Section3 STLTableau.Section4

def guard : Guard Unit := ⟨(), .ge, 1⟩
def action : EdgeLabel Unit := ⟨{guard}, Set.finite_singleton _, ClockResetSet.empty⟩

def T (m : Marker) : Tableau Unit Unit Bool where
  realVariables := Set.univ
  clocks := Set.univ
  states := Set.univ
  edges := {(false,action,true)}
  initial := ∅
  final := {true}
  label := fun q => if q = true then {Local.marker m} else ∅
  label_atomic := by
    intro q l hl
    cases q
    · simp at hl
    · have eq : l = Local.marker m := by simpa using hl
      subst l
      trivial

theorem ready (m : Marker) : (T m).TranslationReady where
  states_finite := Set.finite_univ
  variables_finite := Set.finite_univ
  clocks_finite := Set.finite_univ
  edge_states := fun _ _ => ⟨Set.mem_univ _,Set.mem_univ _⟩
  initial_states := fun _ _ => Set.mem_univ _
  final_states := Set.subset_univ _
  edge_guards := fun _ _ _ _ => Set.mem_univ _
  initial_guards := fun _ _ _ _ => Set.mem_univ _
  edge_resets := fun _ _ => Set.subset_univ _
  initial_resets := fun _ _ => Set.subset_univ _
  atom_variables := fun _ _ _ _ _ => Set.mem_univ _

abbrev A (m : Marker) := (T m).canonicalAutomaton (ready m) 1

def mode (m : Marker) (q : Bool) : (T m).states := ⟨q,Set.mem_univ _⟩

def value (m : Marker) (t c : ℝ) : (T m).HAVar → ℝ
  | .inl _ => 7
  | .inr (.inl _) => c
  | .inr (.inr _) => t

def state (m : Marker) (q : Bool) (t c : ℝ) (within : t ≤ 1) : (A m).State :=
  ⟨(mode m q,value m t c), by
    refine ⟨?_,fun _ => within⟩
    intro a ha
    cases q <;> simp [T,mode] at ha⟩

def edge (m : Marker) : {e // e ∈ (A m).edge} :=
  ⟨(mode m false,action,mode m true),rfl⟩

private theorem guards_hold (m : Marker) (t : ℝ) : (T m).guardsHold action (value m t 1) := by
  intro g hg
  change g = guard at hg
  subst g
  exact ⟨Set.mem_univ _,le_rfl⟩

private theorem end_closed : (T ●).EndGoal (mode ● true) := by
  refine ⟨rfl,?_⟩
  intro l hl
  exact Or.inr hl

theorem horizon_enters_goal_without_star :
    ∃ b : (A ●).State, (A ●).DiscreteStep (state ● false 1 1 le_rfl) b ∧
      b ∈ (T ●).canonicalGoal (ready ●) 1 ∧ b.val.1 ∉ (T ●).terminalModes ∧
      ∀ x : (T ●).realVariables, b.val.2 (.inl x) = 7 := by
  obtain ⟨b,step,target,real⟩ := (T ●).horizon_entry (ready ●) 1 (state ● false 1 1 le_rfl)
    rfl action (mode ● true) rfl (guards_hold ● 1) end_closed
  refine ⟨b,step,?_,?_,real⟩
  · change b.val.1 ∈ (T ●).goalModes
    rw [target]
    exact end_closed.1
  · intro terminal
    change Local.terminal ∈ (T ●).label b.val.1.val at terminal
    rw [target] at terminal
    change Local.terminal ∈ ({Local.marker ●} : Set (Local Unit Unit)) at terminal
    cases terminal

theorem source_is_not_goal (t c : ℝ) (within : t ≤ 1) :
    state ● false t c within ∉ (T ●).canonicalGoal (ready ●) 1 := by
  intro final
  change false = true at final
  cases final

theorem failing_guard_cannot_jump (b : (A ●).State) :
    ¬ (A ●).DiscreteStep (state ● false 1 0 le_rfl) b := by
  rintro ⟨e,_,_,_,_,guards,_,_,_,_⟩
  have he : (e.val.1.val,e.val.2.1,e.val.2.2.val) = (false,action,true) := e.property
  have eq : e.val.2.1 = action := congrArg (fun z : Bool × EdgeLabel Unit × Bool => z.2.1) he
  rw [eq] at guards
  obtain ⟨_,impossible⟩ := guards guard rfl
  change (1 : ℝ) ≤ 0 at impossible
  norm_num at impossible

private theorem not_end_open (q : (T ○).states) : ¬ (T ○).EndGoal q := by
  intro h
  have target : q.val = true := h.1
  have label : Local.marker ○ ∈ (T ○).label q.val := by
    rw [target]
    rfl
  rcases h.2 _ label with bad | bad <;> cases bad

theorem open_final_entry_before_horizon :
    ∃ b : (A ○).State, (A ○).DiscreteStep (state ○ false 0 1 (by norm_num)) b ∧
      b ∈ (T ○).canonicalGoal (ready ○) 1 := by
  refine ⟨state ○ true 0 1 (by norm_num), ⟨edge ○,rfl,rfl,?_⟩,rfl⟩
  refine ⟨rfl,rfl,guards_hold ○ 0,fun _ => rfl,rfl,?_,fun _ => ?_⟩
  · intro terminal
    change Local.terminal ∈ ({Local.marker ○} : Set (Local Unit Unit)) at terminal
    cases terminal
  · change (0 : ℝ) < 1
    norm_num

theorem open_final_cannot_enter_at_horizon (b : (A ○).State) :
    ¬ (A ○).DiscreteStep (state ○ false 1 1 le_rfl) b := by
  rintro ⟨_,_,_,_,_,_,_,global,_,before⟩
  have early := before (not_end_open b.val.1)
  rw [global] at early
  exact lt_irrefl (1 : ℝ) early

run_elab do
  for decl in #[``horizon_enters_goal_without_star, ``source_is_not_goal, ``failing_guard_cannot_jump,
      ``open_final_entry_before_horizon, ``open_final_cannot_enter_at_horizon] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} uses unexpected axiom {ax}"

end CanonicalGoalJumpChecks
