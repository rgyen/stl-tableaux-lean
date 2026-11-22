import STLTableaux.Finiteness.Correctness.FiniteRootTableau
import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence
import STLTableaux.Automata.Recognition.TableauExecutionTime
import STLTableaux.Automata.Execution.TerminalPruning
import STLTableaux.Automata.Recognition.ExecutionObservedExtraction
import STLTableaux.Automata.Recognition.ExecutionInducedPartitionReview

/-! Eliminate an initial zero-time prefix by selecting an already admissible
initial closure. No intermediate trace positions are equated or erased. -/
namespace STLTableau

namespace HybridAutomaton.Execution
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
    {σ : FiniteSignal Var}

/-- Start at an already initial state without changing the initial observation.
Admissibility alone is insufficient: the initial visit owns `σ(0)`. -/
def rebaseInitialState (e : H.Execution σ) (s : H.State)
    (hi : s.val ∈ H.initial)
    (hs : Relation.ReflTransGen H.DiscreteStep s (e.start ⟨0, e.nonempty⟩))
    (same : s.val.2 = e.initialState.val.2) :
    H.Execution σ :=
  { e with
    initialState := s
    initial_mem := hi
    initialSteps := hs
    initial_signal_eq := e.initial_signal_eq.trans same.symm }

/-- Select the last already-admissible initial state on a finite jump chain.
The remaining chain has no initial targets. This uses actual edges only and
does not assert minimality among all possible executions. -/
theorem exists_last_initial {s t : H.State} (hs : s.val ∈ H.initial)
    (steps : Relation.ReflTransGen H.DiscreteStep s t) :
    ∃ u : H.State, u.val ∈ H.initial ∧
      Relation.ReflTransGen H.DiscreteStep s u ∧
      Relation.ReflTransGen
        (fun a b : H.State => H.DiscreteStep a b ∧ b.val ∉ H.initial) u t := by
  classical
  induction steps with
  | refl => exact ⟨s, hs, .refl, .refl⟩
  | @tail b c hsteps hstep ih =>
      by_cases hc : c.val ∈ H.initial
      · exact ⟨c, hc, .tail hsteps hstep, .refl⟩
      · obtain ⟨u, hu, hprefix, hsuffix⟩ := ih
        exact ⟨u, hu, hprefix, .tail hsuffix ⟨hstep, hc⟩⟩

noncomputable def lastInitialState (e : H.Execution σ) : H.State :=
  (exists_last_initial e.initial_mem e.initialSteps).choose

theorem lastInitialState_spec (e : H.Execution σ) :
    (e.lastInitialState).val ∈ H.initial ∧
      Relation.ReflTransGen H.DiscreteStep e.initialState e.lastInitialState ∧
      Relation.ReflTransGen
        (fun a b : H.State => H.DiscreteStep a b ∧ b.val ∉ H.initial)
        e.lastInitialState (e.start ⟨0, e.nonempty⟩) :=
  (exists_last_initial e.initial_mem e.initialSteps).choose_spec

/-- Start the execution at the selected state of the initial jump block
when its valuation agrees with the initial observation. -/
noncomputable def normalizeInitialBlock (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) : H.Execution σ :=
  e.rebaseInitialState e.lastInitialState e.lastInitialState_spec.1
    (Relation.ReflTransGen.mono (fun _ _ hj => hj.1) _ _ e.lastInitialState_spec.2.2)
    same

/-- Initial witness selection does not change the execution boundaries used
by the review partition, including its early-stop suffix. -/
theorem normalizeInitialBlock_reviewInducedPartition (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    (e.normalizeInitialBlock same).reviewInducedPartition = e.reviewInducedPartition := rfl

theorem normalizeInitialBlock_initialSteps (e : H.Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    Relation.ReflTransGen
      (fun a b : H.State => H.DiscreteStep a b ∧ b.val ∉ H.initial)
      (e.normalizeInitialBlock same).initialState
      ((e.normalizeInitialBlock same).start ⟨0, (e.normalizeInitialBlock same).nonempty⟩) :=
  e.lastInitialState_spec.2.2

/-- When the first flow can already initialize the automaton, the selected
initial block has no preceding states. No new initialization is assumed. -/
theorem normalizeInitialBlock_initial_eq_firstFlow (e : H.Execution σ)
    (hi : (e.start ⟨0, e.nonempty⟩).val ∈ H.initial)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    (e.normalizeInitialBlock same).initialState = e.start ⟨0, e.nonempty⟩ := by
  rcases e.lastInitialState_spec.2.2.cases_tail with heq | ⟨_, _, hj⟩
  · exact heq.symm
  · exact (hj.2 hi).elim

/-- If the first flow state is itself initial, start there. Every observed
flow, later jump, stopping time and final observation is unchanged. -/
def rebaseAtFirstFlow (e : H.Execution σ)
    (hi : (e.start ⟨0, e.nonempty⟩).val ∈ H.initial)
    (same : (e.start ⟨0, e.nonempty⟩).val.2 = e.initialState.val.2) : H.Execution σ :=
  { e with
    initialState := e.start ⟨0, e.nonempty⟩
    initial_mem := hi
    initial_signal_eq := e.initial_signal_eq.trans same.symm
    initialSteps := .refl }

end HybridAutomaton.Execution

namespace Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- Extract a single accepting path after selecting an admissible initial
suffix. All observations refer to that same execution; its signal, flow data,
stopping time and final state are unchanged. This does not construct a partition. -/
theorem pruned_execution_accepting_observed_path_normalized
    (h : T.TranslationReady) {σ : FiniteSignal T.HAVar}
    (e : (T.toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    (hgoal : e.finalState.val.1 ∈ T.pruneTerminal.goalModes)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    let e' := e.normalizeInitialBlock same
    ∃ p ds, p.run T ∧ p.accepting T ∧
      T.pruneTerminal.ExecutionPathWitness (T.pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e'.initialState e.finalState p ∧
      T.pruneTerminal.TimedPath p e'.initialState.val.2 e.finalState.val.2 ds ∧
      T.pruneTerminal.ObservedPath (T.pruneTerminal_translationReady h)
        σ.horizon σ.horizon_pos e' p 0 (e.boundary ⟨e.count, by omega⟩) ds ∧
      ∃ u : T.HAVar → ℝ, T.pruneTerminal.guardsHold p.firstIncoming u ∧
        e'.initialState.val.2 = T.pruneTerminal.initialReset p.firstIncoming.resets u := by
  exact T.pruned_execution_accepting_observed_path h (e.normalizeInitialBlock same) hgoal

theorem initialReset_eq_reset_at_zero (Λ : ClockResetSet Clock)
    (v : T.HAVar → ℝ) (hz : v T.globalClock = 0) :
    T.initialReset Λ v = T.reset Λ v := by
  funext x
  cases x with
  | inl => rfl
  | inr x =>
    cases x with
    | inl => rfl
    | inr u => cases u; exact hz.symm

/-- The actual last jump's pre-reset valuation witnesses initialization.
Its guard and reset are kept, not dropped or assumed to be empty. -/
theorem initial_of_zero_time_jump (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {s s' : (T.toAutomaton h τ hτ).State}
    (hj : (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hz : s.val.2 T.globalClock = 0)
    (hi : ∀ l, (s.val.1.val, l, s'.val.1.val) ∈ T.edges →
      (l, s'.val.1.val) ∈ T.initial) :
    s'.val ∈ (T.toAutomaton h τ hτ).initial := by
  obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff h τ hτ).mp hj
  exact ⟨l, hi l he, s.val.2, hg,
    hr.trans (T.initialReset_eq_reset_at_zero l.resets s.val.2 hz).symm⟩

end Section4.Tableau

namespace Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Literal return to the root generator makes the same destination and
incoming label an initial entry, including the finite-inventory restriction. -/
theorem finiteRootTableau_root_return_initial (X : Set Var) (root : Formula Var)
    {F G : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (he : (F, l, G) ∈ (finiteRootTableau X root).edges)
    (hn : F.nextPart = some (Section3.StateForm.ofLocal (.predicate (.plain root)))) :
    (l, G) ∈ (finiteRootTableau X root).initial := by
  obtain ⟨_, _, N, hN, hd, hinc⟩ := he.1
  change F.nextPart = some N at hN
  have hNr := Option.some.inj (hN.symm.trans hn)
  subst N
  exact ⟨⟨hd, hinc⟩, he.2.2⟩

/-- Applies to a root-return jump immediately before the first positive flow.
The source need not equal the destination and resets need not be identities. -/
theorem finiteRootTableau_firstFlow_initial_of_root_return
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau X root).toAutomaton h τ hτ).Execution σ)
    {s : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep
      s (e.start ⟨0, e.nonempty⟩))
    (hn : s.val.1.val.nextPart =
      some (Section3.StateForm.ofLocal (.predicate (.plain root)))) :
    (e.start ⟨0, e.nonempty⟩).val ∈ ((finiteRootTableau X root).toAutomaton h τ hτ).initial := by
  apply Tableau.initial_of_zero_time_jump _ h τ hτ hj
  · have hz := Tableau.execution_start_clock (finiteRootTableau X root) h τ hτ e
      ⟨0, e.nonempty⟩
    rw [e.first_zero] at hz
    exact (Tableau.jump_globalClock_preserved _ h τ hτ hj).symm.trans hz
  · intro l hl
    exact finiteRootTableau_root_return_initial X root hl hn

/-- A root-return jump anywhere in the actual initial block admits its target
as a new initial state of the pruned translation. No same-mode or identity-
reset assumption is needed: the actual incoming guard/reset are retained. -/
theorem finiteRootTableau_pruned_root_return_initial
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).Execution σ)
    {s t : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep e.initialState s)
    (hj : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s t)
    (hn : s.val.1.val.nextPart =
      some (Section3.StateForm.ofLocal (.predicate (.plain root)))) :
    t.val ∈ ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).initial := by
  let T := finiteRootTableau (Clock := Clock) X root
  let hp := T.pruneTerminal_translationReady h
  apply T.pruneTerminal.initial_of_zero_time_jump hp τ hτ hj
  · exact (T.pruneTerminal.discreteSteps_globalClock_preserved hp τ hτ hprefix).trans
      (T.pruneTerminal.initial_globalClock_zero hp τ hτ e.initial_mem)
  · intro l he
    exact ⟨finiteRootTableau_root_return_initial X root he.1 hn, t.val.1.property.2⟩

/-- Choose the suffix after an actual initial root-return jump. This changes
only the initial witness, not the signal, positive flows or final state.
It does not claim that arbitrary distinct-state jump blocks can be removed. -/
noncomputable def rebasePrunedInitialRootReturn
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).Execution σ)
    {s t : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State}
    (hprefix : Relation.ReflTransGen
      ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep e.initialState s)
    (hj : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s t)
    (hn : s.val.1.val.nextPart =
      some (Section3.StateForm.ofLocal (.predicate (.plain root))))
    (hsuffix : Relation.ReflTransGen
      ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep
      t (e.start ⟨0, e.nonempty⟩))
    (same : t.val.2 = e.initialState.val.2) :
    ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).Execution σ :=
  e.rebaseInitialState t
    (finiteRootTableau_pruned_root_return_initial X root h τ hτ e hprefix hj hn) hsuffix same

/-- After selecting the last initial state, no remaining initial-block edge
has the root as its literal next generator. Such an edge would make its target
initial again. This retains all edges of the selected suffix; it does not bound
its length or remove edges whose generators differ from the root. -/
theorem normalized_initialSteps_no_root_return
    (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).Execution σ)
    (same : e.lastInitialState.val.2 = e.initialState.val.2) :
    Relation.ReflTransGen
      (fun s t : ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).State =>
        ((finiteRootTableau X root).toPrunedAutomaton h τ hτ).DiscreteStep s t ∧
        s.val.1.val.nextPart ≠
          some (Section3.StateForm.ofLocal (.predicate (.plain root))))
      (e.normalizeInitialBlock same).initialState (e.start ⟨0, e.nonempty⟩) := by
  let T := finiteRootTableau (Clock := Clock) X root
  let hp := T.pruneTerminal_translationReady h
  let H := T.toPrunedAutomaton h τ hτ
  have lift : ∀ {s t : H.State},
      Relation.ReflTransGen (fun a b : H.State =>
        H.DiscreteStep a b ∧ b.val ∉ H.initial) s t →
      s.val.2 T.globalClock = 0 →
      Relation.ReflTransGen (fun a b : H.State =>
        H.DiscreteStep a b ∧ a.val.1.val.nextPart ≠
          some (Section3.StateForm.ofLocal (.predicate (.plain root)))) s t := by
    intro s t steps
    induction steps using Relation.ReflTransGen.head_induction_on with
    | refl => intro _; exact .refl
    | @head a b hab _ ih =>
      intro hz
      have hbz : b.val.2 T.globalClock = 0 :=
        (T.pruneTerminal.jump_globalClock_preserved hp τ hτ hab.1).trans hz
      refine (Relation.ReflTransGen.single ⟨hab.1, ?_⟩).trans (ih hbz)
      intro hn
      apply hab.2
      apply T.pruneTerminal.initial_of_zero_time_jump hp τ hτ hab.1 hz
      intro l he
      exact ⟨finiteRootTableau_root_return_initial X root he.1 hn, b.val.1.property.2⟩
  exact lift (e.normalizeInitialBlock_initialSteps same)
    (T.pruneTerminal.initial_globalClock_zero hp τ hτ (e.normalizeInitialBlock same).initial_mem)

end Section4.Finiteness
end STLTableau
