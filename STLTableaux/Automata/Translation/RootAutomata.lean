import STLTableaux.Finiteness.Correctness.FiniteRootTableauEdges
import STLTableaux.Finiteness.Correctness.NormalizedRootTableau
import STLTableaux.Automata.Translation.TableauAutomata

/-! Discharge the translation interface for the concrete finite root tableau.
This constructs the automaton, not the run/trajectory equivalence. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

variable [DecidableEq Clock] [Infinite Clock]

theorem finiteRootTableau_incoming_guard_support (X : Set Var) (root : Formula Var)
    (F : Section3.TransitionForm Clock Var)
    (hF : F ∈ (finiteRootTableau (Clock := Clock) X root).states)
    (g : Guard Clock) (hg : g ∈ F.current.guards) :
    g.clock ∈ (finiteRootTableau (Clock := Clock) X root).clocks := by
  apply finiteRootTableau_state_clock_support X root F hF
  exact Or.inl (Or.inl ⟨g, hg, rfl⟩)

theorem finiteRootTableau_incoming_reset_support (X : Set Var) (root : Formula Var)
    (F : Section3.TransitionForm Clock Var)
    (hF : F ∈ (finiteRootTableau (Clock := Clock) X root).states) :
    F.current.resets.clocks ⊆ (finiteRootTableau (Clock := Clock) X root).clocks := by
  intro c hc
  apply finiteRootTableau_state_clock_support X root F hF
  exact Or.inr (Or.inl hc)

theorem finiteRootTableau_translationReady (X : Set Var) (hX : X.Finite)
    (root : Formula Var) (hvars : ∀ x ∈ rootVariables root, x ∈ X) :
    (finiteRootTableau (Clock := Clock) X root).TranslationReady where
  states_finite := finiteRootTableau_states_finite X root
  variables_finite := hX
  clocks_finite := finiteRootTableau_clocks_finite X root
  edge_states := fun _ he => he.2
  initial_states := fun _ he => he.2
  final_states := fun _ he => he.2
  edge_guards := by
    intro e he g hg
    obtain ⟨_, _, N, _, _, hl⟩ := he.1
    rw [hl] at hg
    exact finiteRootTableau_incoming_guard_support X root e.2.2 he.2.2 g hg
  initial_guards := by
    intro e he g hg
    rw [he.1.2] at hg
    exact finiteRootTableau_incoming_guard_support X root e.2 he.2 g hg
  edge_resets := by
    intro e he
    obtain ⟨_, _, N, _, _, hl⟩ := he.1
    rw [hl]
    exact finiteRootTableau_incoming_reset_support X root e.2.2 he.2.2
  initial_resets := by
    intro e he
    rw [he.1.2]
    exact finiteRootTableau_incoming_reset_support X root e.2 he.2
  atom_variables := by
    intro F hF a ha i
    apply hvars
    apply atom_arguments_mem_rootVariables
    exact FiniteInventory.atom_mem_plain_inventory _ _ a (hF.2.1.1 ha.1)

/-- Low-level translation with no assumed support certificate. Its input is
unrestricted syntax; use `inputAutomaton` for the normalized input contract.
This construction alone does not assert recognition/trajectory equivalence. -/
noncomputable def rootAutomaton (root : Formula Var) (τ : ℝ) (hτ : 0 < τ) :=
  (finiteRootTableau (Clock := Clock) (rootVariables root : Set Var) root).toAutomaton
    (finiteRootTableau_translationReady _ (Finset.finite_toSet _) root (fun _ hx => hx))
    τ hτ

/-- General raw input is normalized before taking its finite variable support.
This broader API is not the checked normalized input API and has no HA correctness
theorem; normalization can retain a standalone false constant. -/
noncomputable def normalizedRootAutomaton (root : Formula Var) (τ : ℝ) (hτ : 0 < τ) :=
  rootAutomaton (Clock := Clock) root.normalizeForTableau τ hτ

end STLTableau.Section4.Finiteness
