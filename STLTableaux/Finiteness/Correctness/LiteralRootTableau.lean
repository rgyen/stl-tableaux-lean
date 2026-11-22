import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Finiteness.Correctness.LiteralMinimization

/-! Restricts the finite graph to original minimal closures. Each initial
state and each successor uses a minimal closure of its generator. Inclusion
in the larger graph gives finiteness and recognition soundness. -/
namespace STLTableau.Section4.Finiteness
variable {Clock Var : Type*} [DecidableEq Clock]

def LiteralDerives (N : Section3.StateForm Clock Var)
    (F : Section3.TransitionForm Clock Var) : Prop :=
  Section3.ConcreteContextual.catalogue.IsClosure (.ofState N) F ∧ N.Ready

theorem LiteralDerives.toDerives {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : LiteralDerives N F) : Derives N F :=
  .original h.1 h.2

variable [Infinite Clock]

noncomputable def finiteLiteralRootTableau (X : Set Var) (root : Formula Var) :=
  Subgraph.restrict
    (JudgementTableau.tableau X
      (FiniteInventory.clocks (rootSlotTriples (Clock := Clock) root) : Set Clock)
      (.ofLocal (.predicate (.plain root))) LiteralDerives)
    {F | FiniteInventory.TransitionWithin
      (FiniteInventory.locals (Finiteness.rootPlainFormulas root) (rootSlotTriples root))
      (FiniteInventory.guards (rootSlotTriples root))
      (FiniteInventory.resets (rootSlotTriples root)) F}

theorem finiteLiteralRootTableau_states_subset (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).states ⊆
      (finiteRootTableau X root).states := by
  rintro F ⟨⟨N, hN⟩, hF⟩
  exact ⟨⟨N, hN.toDerives⟩, hF⟩

/-- A satisfied closed extension inside the finite inventory contains a satisfied
minimal closure of the same generator. -/
theorem finiteLiteralRootTableau_exists_minimal_state
    (X : Set Var) (root : Formula Var) {N : Section3.StateForm Clock Var}
    {U : Section3.TransitionForm Clock Var} (hn : N.Ready)
    (hu : Section3.SyntacticallySubsumed (.ofState N) U)
    (hc : Section3.ConcreteContextual.catalogue.IsClosed U)
    (hi : FiniteInventory.TransitionWithin
      (FiniteInventory.locals (Finiteness.rootPlainFormulas root) (rootSlotTriples root))
      (FiniteInventory.guards (rootSlotTriples root))
      (FiniteInventory.resets (rootSlotTriples root)) U)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : U.holds σ P α k) :
    ∃ V, V ∈ (finiteLiteralRootTableau X root).states ∧
      LiteralDerives N V ∧ Section3.SyntacticallySubsumed V U ∧ V.holds σ P α k := by
  obtain ⟨V, hv, hVU, hiV, hsV⟩ :=
    FiniteInventory.exists_satisfied_minimal_within _ hu hc hi σ P α k hs
  exact ⟨V, ⟨⟨N, hv, hn⟩, hiV⟩, ⟨hv, hn⟩, hVU, hsV⟩

/-- Edge admission uses the predecessor's actual next generator, not merely
the fact that the target is a closure of some unrelated generator. -/
theorem finiteLiteralRootTableau_edge_closure (X : Set Var) (root : Formula Var)
    {F G : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (he : (F, l, G) ∈ (finiteLiteralRootTableau X root).edges) :
    ∃ N, F.nextPart = some N ∧
      Section3.ConcreteContextual.catalogue.IsClosure (.ofState N) G := by
  obtain ⟨_, _, N, hn, hd, _⟩ := he.1
  exact ⟨N, hn, hd.1⟩

theorem finiteLiteralRootTableau_initial_closure (X : Set Var) (root : Formula Var)
    {F : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (hi : (l, F) ∈ (finiteLiteralRootTableau X root).initial) :
    Section3.ConcreteContextual.catalogue.IsClosure
      (.ofState (.ofLocal (.predicate (.plain root)))) F := hi.1.1.1

theorem finiteLiteralRootTableau_edges_subset (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).edges ⊆
      (finiteRootTableau X root).edges := by
  intro e he
  obtain ⟨⟨M, hM⟩, ⟨N, hN⟩, K, hk, hd, hl⟩ := he.1
  exact ⟨⟨⟨M, hM.toDerives⟩, ⟨N, hN.toDerives⟩, K, hk, hd.toDerives, hl⟩,
    finiteLiteralRootTableau_states_subset X root he.2.1,
    finiteLiteralRootTableau_states_subset X root he.2.2⟩

theorem finiteLiteralRootTableau_initial_subset (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).initial ⊆
      (finiteRootTableau X root).initial := by
  intro e he
  exact ⟨⟨he.1.1.toDerives, he.1.2⟩, finiteLiteralRootTableau_states_subset X root he.2⟩

theorem finiteLiteralRootTableau_final_subset (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).final ⊆
      (finiteRootTableau X root).final := by
  intro F hF
  exact ⟨hF.1, finiteLiteralRootTableau_states_subset X root hF.2⟩

theorem finiteLiteralRootTableau_states_finite (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).states.Finite :=
  (finiteRootTableau_states_finite X root).subset
    (finiteLiteralRootTableau_states_subset X root)

theorem finiteLiteralRootTableau_edges_finite (X : Set Var) (root : Formula Var) :
    (finiteLiteralRootTableau (Clock := Clock) X root).edges.Finite :=
  (finiteRootTableau_edges_finite X root).subset
    (finiteLiteralRootTableau_edges_subset X root)

theorem finiteLiteralRootTableau_state_clock_support (X : Set Var) (root : Formula Var)
    (F : Section3.TransitionForm Clock Var)
    (hF : F ∈ (finiteLiteralRootTableau X root).states) :
    F.allClocks ⊆ (finiteLiteralRootTableau X root).clocks :=
  finiteRootTableau_state_clock_support X root F
    (finiteLiteralRootTableau_states_subset X root hF)

theorem finiteLiteralRootTableau_valid_to_extended (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hp : p.valid (finiteLiteralRootTableau X root)) : p.valid (finiteRootTableau X root) := by
  induction p with
  | last => exact finiteLiteralRootTableau_states_subset X root hp
  | step l F p ih =>
      exact ⟨finiteLiteralRootTableau_states_subset X root hp.1, ih hp.2.1,
        finiteLiteralRootTableau_edges_subset X root hp.2.2⟩

/-- The same path, labels, resets, and partition are preserved by inclusion. -/
theorem finiteLiteralRootTableau_recognizes_to_extended
    (X : Set Var) (root : Formula Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain)
    (hs : (finiteLiteralRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) :
    (finiteRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P := by
  obtain ⟨p, hr, ha, ht⟩ := hs
  have hv := finiteLiteralRootTableau_valid_to_extended X root p hr.1
  exact ⟨p, ⟨hv, finiteLiteralRootTableau_initial_subset X root hr.2⟩,
    ⟨hv, finiteLiteralRootTableau_final_subset X root ha.2⟩, ht⟩

theorem finiteLiteralRootTableau_sound (X : Set Var) (root : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hs : (finiteLiteralRootTableau (Clock := Clock) X root).recognizes
      JudgementTableau.labels_finite σ P) :
    σ.Satisfies root ⟨0, le_rfl, σ.horizon_pos⟩ :=
  finiteRootTableau_sound X root σ P
    (finiteLiteralRootTableau_recognizes_to_extended X root σ P hs)

theorem finiteLiteralRootTableau_translationReady (X : Set Var) (hX : X.Finite)
    (root : Formula Var) (hvars : ∀ x ∈ rootVariables root, x ∈ X) :
    (finiteLiteralRootTableau (Clock := Clock) X root).TranslationReady where
  states_finite := finiteLiteralRootTableau_states_finite X root
  variables_finite := hX
  clocks_finite := finiteRootTableau_clocks_finite X root
  edge_states := fun _ he => he.2
  initial_states := fun _ hi => hi.2
  final_states := fun _ hf => hf.2
  edge_guards := fun e he =>
    (finiteRootTableau_translationReady X hX root hvars).edge_guards e
      (finiteLiteralRootTableau_edges_subset X root he)
  initial_guards := fun e he =>
    (finiteRootTableau_translationReady X hX root hvars).initial_guards e
      (finiteLiteralRootTableau_initial_subset X root he)
  edge_resets := fun e he =>
    (finiteRootTableau_translationReady X hX root hvars).edge_resets e
      (finiteLiteralRootTableau_edges_subset X root he)
  initial_resets := fun e he =>
    (finiteRootTableau_translationReady X hX root hvars).initial_resets e
      (finiteLiteralRootTableau_initial_subset X root he)
  atom_variables := fun F hF =>
    (finiteRootTableau_translationReady X hX root hvars).atom_variables F
      (finiteLiteralRootTableau_states_subset X root hF)

end STLTableau.Section4.Finiteness
