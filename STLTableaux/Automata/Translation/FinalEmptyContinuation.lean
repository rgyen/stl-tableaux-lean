import STLTableaux.Automata.Translation.NormalizedInputTranslation
import STLTableaux.Automata.Recognition.TypedTerminalPartition

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T" => (inputTableau (Clock := Clock) X root)

/-- A final state in the input tableau has no outgoing edge. -/
theorem old_final_has_no_edge {q q' : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (hf : q ∈ (T).final) : (q,l,q') ∉ (T).edges := by
  intro he
  obtain ⟨_, _, N, hn, _, _⟩ := he.1
  have hnone : q.nextPart = none := hf.1
  rw [hnone] at hn
  contradiction

def emptyMode : Section3.TransitionForm Clock Var := .ofState Section3.StateForm.empty
def emptyIncoming : EdgeLabel Clock := ⟨∅,Set.finite_empty,ClockResetSet.empty⟩

/-- Add `emptyMode` as a final state and an edge to it from each other final state. -/
noncomputable def withEmptyContinuation : Tableau Clock Var (Section3.TransitionForm Clock Var) :=
  { T with
    states := insert emptyMode (T).states
    final := insert emptyMode (T).final
    edges := {e | e ∈ (T).edges ∨
      (e.1 ∈ (T).final ∧ e.1 ≠ emptyMode ∧ e.2.1 = emptyIncoming ∧ e.2.2 = emptyMode)} }

theorem final_empty_edge (q : Section3.TransitionForm Clock Var) (hq : q ∈ (T).final)
    (hne : q ≠ emptyMode) :
    (q,emptyIncoming,emptyMode) ∈ (withEmptyContinuation (Clock := Clock) X root).edges :=
  Or.inr ⟨hq,hne,rfl,rfl⟩

theorem empty_label : (withEmptyContinuation (Clock := Clock) X root).label emptyMode = ∅ := by
  ext l
  change (l ∈ (∅ : Set (Local Clock Var)) ∧ _) ↔ l ∈ (∅ : Set (Local Clock Var))
  simp

theorem withEmptyContinuation_ready (h : (T).TranslationReady) :
    (withEmptyContinuation (Clock := Clock) X root).TranslationReady where
  states_finite := h.states_finite.insert _
  variables_finite := h.variables_finite
  clocks_finite := h.clocks_finite
  edge_states := by
    intro e he
    rcases he with old | ⟨hf,_,_,hq⟩
    · exact ⟨Or.inr (h.edge_states _ old).1,Or.inr (h.edge_states _ old).2⟩
    · exact ⟨Or.inr (h.final_states hf),Or.inl hq⟩
  initial_states := fun e he => Or.inr (h.initial_states e he)
  final_states := fun _ hq => hq.elim Or.inl (fun hf => Or.inr (h.final_states hf))
  edge_guards := by
    intro e he g hg
    rcases he with old | ⟨_,_,hl,_⟩
    · exact h.edge_guards _ old g hg
    · change g ∈ e.2.1.guards at hg
      rw [hl] at hg
      exact hg.elim
  initial_guards := h.initial_guards
  edge_resets := by
    intro e he
    rcases he with old | ⟨_,_,hl,_⟩
    · exact h.edge_resets _ old
    · rw [hl]
      intro c hc
      obtain ⟨a,ha⟩ := hc
      cases ha
  initial_resets := h.initial_resets
  atom_variables := by
    intro q hq a ha
    rcases hq with he | old
    · subst q
      rw [empty_label] at ha
      exact ha.elim
    · exact h.atom_variables _ old a ha

/-- The empty edge is present but cannot be executed at the horizon,
because its target has no star. No outgoing edge deletion is used. -/
theorem no_empty_jump_at_horizon (h : (T).TranslationReady) (τ : ℝ)
    {a b : ((withEmptyContinuation (Clock := Clock) X root).typedAutomaton
      (withEmptyContinuation_ready X root h) τ).State}
    (ht : a.val.2 (.inl (withEmptyContinuation (Clock := Clock) X root).globalClock) = τ)
    (hb : b.val.1.val = emptyMode) :
    ¬ ((withEmptyContinuation (Clock := Clock) X root).typedAutomaton
      (withEmptyContinuation_ready X root h) τ).DiscreteStep a b := by
  intro hj
  have hs := (withEmptyContinuation (Clock := Clock) X root).typed_horizon_jump_target _ τ hj ht
  change Local.terminal ∈ (withEmptyContinuation (Clock := Clock) X root).label b.val.1.val at hs
  rw [hb,empty_label] at hs
  exact hs

/-- Before the horizon a closed singleton final visit really can take
the new edge. Keep X unchanged for this witness, reset h and open the
successor. The source atoms are then checked at the actual post-value. -/
theorem early_singleton_to_empty (h : (T).TranslationReady) (τ : ℝ)
    (a : ((withEmptyContinuation (Clock := Clock) X root).typedAutomaton
      (withEmptyContinuation_ready X root h) τ).State)
    (hf : a.val.1.val ∈ (T).final) (hne : a.val.1.val ≠ emptyMode)
    (ht : a.val.2 (.inl (withEmptyContinuation (Clock := Clock) X root).globalClock) < τ)
    (closed : a.val.2 (withEmptyContinuation (Clock := Clock) X root).bit = 1) :
    ∃ b, ((withEmptyContinuation (Clock := Clock) X root).typedAutomaton
      (withEmptyContinuation_ready X root h) τ).DiscreteStep a b ∧ b.val.1.val = emptyMode := by
  let U := withEmptyContinuation (Clock := Clock) X root
  let v : U.TypedVar → ℝ := fun x => match x with
    | .inl y => a.val.2 (.inl y)
    | .inr _ => 0
  let q : U.states := ⟨emptyMode,Or.inl rfl⟩
  have hem : U.label q.val = ∅ := empty_label X root
  have inv : (q,v) ∈ (U.typedAutomaton (withEmptyContinuation_ready X root h) τ).invariant := by
    refine ⟨Or.inl rfl,fun _ => ht.le,?_,?_⟩
    · intro p hp
      rw [hem] at hp
      exact hp.elim
    · intro m hm
      rw [hem] at hm
      exact hm.elim
  let b := (⟨(q,v),inv⟩ : (U.typedAutomaton (withEmptyContinuation_ready X root h) τ).State)
  refine ⟨b,?_,rfl⟩
  let edge := (a.val.1,emptyIncoming (Clock := Clock),q)
  have he : edge ∈ (U.typedAutomaton (withEmptyContinuation_ready X root h) τ).edge :=
    final_empty_edge X root _ hf hne
  refine ⟨⟨edge,he⟩,rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,?_,fun _ => ⟨closed,rfl⟩,?_⟩
  · intro g hg
    exact hg.elim
  · intro c
    rfl
  · change Local.terminal ∈ U.label q.val ↔ τ ≤ a.val.2 (.inl U.globalClock)
    rw [hem]
    simpa using ht
  · intro _ p hp
    exact a.property.2.2.1 p hp

end STLTableau.Section4.Finiteness
