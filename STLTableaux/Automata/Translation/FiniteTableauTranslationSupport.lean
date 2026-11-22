/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Correctness.FiniteTableau
import STLTableaux.Finiteness.Inventory.ClockSupport
import STLTableaux.Automata.Translation.InitialTerminalSupport
import STLTableaux.ModelChecking.Preprocessing.NormalizedInputPreservation
import STLTableaux.Automata.Translation.TableauAutomata

/-! The translation interface for the actual finite tableau of Section 4.
Closure construction ends in Section 4; the automaton only reads the graph,
labels, guards and resets. -/
namespace STLTableau.Section4.Finiteness
open Section3

namespace CompletedDerivation
open ResetTrimming
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem merge_guard_ready {R : ClockResetSet Clock} {c : Clock} {b : Marker}
    {J K : MixedJ Clock Var} (g : MergeGuard R c b J K) (h : judgementNormalizedReady J) :
    judgementNormalizedReady K := by
  cases g with
  | closed | fixed => exact h
  | free Γ _ => exact (withBoundaryGuard_normalizedReady _ _ _).mpr h

theorem Tree.normalizedReady {J H A : MixedJ Clock Var} (D : Tree J H A)
    (hi : judgementNormalizedReady J) : judgementNormalizedReady H := by
  induction D with
  | leaf => exact hi
  | conj _ _ ih ig => exact ⟨ih hi.1, ig hi.2⟩
  | reset _ _ ih => exact ih hi
  | structural he _ ih => exact ih (he.normalizedReady_iff.mp hi)
  | expandCtx hb _ _ _ ih => exact ⟨hi.1, ih ⟨hb.normalizedReady hi.1, hi.2⟩⟩
  | expandSolo hb _ _ _ ih => exact ⟨hi, ih (hb.normalizedReady hi)⟩
  | merge _ _ _ g _ ih => exact ih ⟨hi.1.1, merge_guard_ready g hi.2⟩
  | mergeOptional _ _ _ g _ ih => exact ih ⟨hi.1, trivial, merge_guard_ready g hi.2.2⟩
  | boundaryRequired _ _ _ _ ih =>
    exact ih ⟨hi.1.1, trivial, (withBoundaryGuard_normalizedReady _ _ _).mpr hi.2.2⟩
  | boundaryOptional _ _ _ _ ih =>
    exact ih ⟨hi.1, trivial, (withBoundaryGuard_normalizedReady _ _ _).mpr hi.2.2⟩
  | unusedReset _ _ _ _ _ ih => exact ih hi

omit [DecidableEq Clock] in
private theorem merge_guard_noStar {R : ClockResetSet Clock} {c : Clock} {b : Marker}
    {J K : MixedJ Clock Var} (g : MergeGuard R c b J K) (h : NoCurrentTerminal J) :
    NoCurrentTerminal K := by
  cases g with
  | closed | fixed => exact h
  | free Γ _ => exact (noCurrentTerminal_withBoundaryGuard _ _ _).mpr h

theorem Tree.noCurrentTerminal {J H A : MixedJ Clock Var} (D : Tree J H A)
    (hi : NoCurrentTerminal J) : NoCurrentTerminal H := by
  induction D with
  | leaf => exact hi
  | conj _ _ ih ig => exact ⟨ih hi.1, ig hi.2⟩
  | reset _ _ ih => exact ih hi
  | structural he _ ih => exact ih (he.noCurrentTerminal_iff.mp hi)
  | expandCtx hb _ _ _ ih => exact ⟨trivial, ih ⟨hb.noCurrentTerminal, hi.2⟩⟩
  | expandSolo hb _ _ _ ih => exact ⟨trivial, ih hb.noCurrentTerminal⟩
  | merge _ _ _ g _ ih => exact ih ⟨trivial, merge_guard_noStar g hi.2⟩
  | mergeOptional _ _ _ g _ ih => exact ih ⟨trivial, trivial, merge_guard_noStar g hi.2.2⟩
  | boundaryRequired _ _ _ _ ih => exact ih ⟨trivial, trivial,
      (noCurrentTerminal_withBoundaryGuard _ _ _).mpr hi.2.2⟩
  | boundaryOptional _ _ _ _ ih => exact ih ⟨trivial, trivial,
      (noCurrentTerminal_withBoundaryGuard _ _ _).mpr hi.2.2⟩
  | unusedReset _ _ _ _ _ ih => exact ih hi

theorem Member.normalizedReady {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : Member N F)
    (ready : N.NormalizedReady) : F.NormalizedReady := by
  have hr : (Section3.TransitionForm.ofState N).NormalizedReady := by simpa using ready
  cases h with
  | original h _ => exact ConcreteContextual.closure_normalizedReady h hr
  | completed D hJ hH _ => exact
      hH.normalizedReady.mpr (Tree.normalizedReady D (hJ.normalizedReady.mp hr))

theorem Admitted.normalizedReady {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : Admitted N F)
    (ready : N.NormalizedReady) : F.NormalizedReady := by
  cases h with
  | original h hR => exact Member.normalizedReady (.original h hR) ready
  | replayed he hm ht =>
    rw [← ht]
    have eq := congrArg Section3.StateForm.locals he
    have ho := Member.normalizedReady hm (by
      intro l hl
      exact ready l (eq ▸ hl))
    refine ⟨ho.1, ?_⟩
    intro M hM
    obtain ⟨K, hk, rfl⟩ := Option.map_eq_some_iff.mp hM
    exact ho.2 K hk

theorem Member.noCurrentTerminal {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : Member N F)
    (hs : Local.terminal ∉ N.locals) : Local.terminal ∉ F.current.locals := by
  cases h with
  | original h _ => exact closure_no_terminal h hs
  | completed D hJ hH _ =>
    exact (normalize_noCurrentTerminal _ hH.normalizes).mpr
      (Tree.noCurrentTerminal D ((normalize_noCurrentTerminal _ hJ.normalizes).mp hs))

theorem Admitted.noCurrentTerminal {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : Admitted N F)
    (hs : Local.terminal ∉ N.locals) : Local.terminal ∉ F.current.locals := by
  cases h with
  | original h hr => exact Member.noCurrentTerminal (.original h hr) hs
  | replayed he hm ht =>
    rw [← ht]
    have eq := congrArg Section3.StateForm.locals he
    have hstar := Member.noCurrentTerminal hm (fun h => hs (eq ▸ h))
    exact hstar

end CompletedDerivation

variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

section
variable (X : Set Var) (root : Formula Var)
local notation "T" => finiteTableau (Clock := Clock) X root

theorem finiteTableau_atom_subformula (q : (T).states) (a : AtomicProposition Var)
    (hm : Local.predicate (.plain (.atom a)) ∈ (T).label q.val) :
    Formula.IsSubformula (.atom a) root :=
  Finiteness.subformula_of_mem_rootPlainFormulas
    (FiniteInventory.atom_mem_plain_inventory _ _ a (q.property.2.1.1.1 hm.1))

/-- All guards, reset clocks, and atom arguments are covered by the finite inventory. -/
theorem finiteTableau_translationReady (hX : X.Finite)
    (vars : ∀ x ∈ rootVariables root, x ∈ X) : (T).TranslationReady := by
  have guard (q : ClosureState Clock Var) (hq : q ∈ (T).states)
      (g : Guard Clock) (hg : g ∈ q.incoming.guards) : g.clock ∈ (T).clocks :=
    FiniteInventory.guard_support (rootSlotTriples root) (hq.2.1.1.2.1 hg)
  have reset (q : ClosureState Clock Var) (hq : q ∈ (T).states) :
      q.incoming.resets.clocks ⊆ (T).clocks := by
    rintro c ⟨a, ha⟩
    exact FiniteInventory.reset_support (rootSlotTriples root) (hq.2.1.1.2.2 c a ha)
  refine ⟨finiteTableau_states_finite X root, hX, finiteTableau_clocks_finite X root,
    fun _ he => finiteTableau_edge_states X root he,
    fun _ hi => hi.2, fun _ hf => hf.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he g hg
    rw [finiteTableau_edge_incoming X root he] at hg
    exact guard e.2.2 (finiteTableau_edge_states X root he).2 g hg
  · intro e he g hg
    rw [he.1.2.2] at hg
    exact guard e.2 he.2 g hg
  · intro e he
    rw [finiteTableau_edge_incoming X root he]
    exact reset e.2.2 (finiteTableau_edge_states X root he).2
  · intro e he
    rw [he.1.2.2]
    exact reset e.2 he.2
  · intro q hq a ha i
    exact vars _ (atom_arguments_mem_rootVariables root a
      (FiniteInventory.atom_mem_plain_inventory _ _ a (hq.2.1.1.1 ha.1)) i)

theorem finiteTableau_initial_nonterminal
    {e : EdgeLabel Clock × ClosureState Clock Var} (h : e ∈ (T).initial) :
    Local.terminal ∉ (T).label e.2 := by
  have hn := h.1.2.1.noCurrentTerminal (by simp [plainInitialState, Section3.StateForm.ofLocal])
  exact fun ht => hn ht.1

theorem finiteTableau_edge_normalizedReady
    {e : ClosureState Clock Var × EdgeLabel Clock × ClosureState Clock Var}
    (h : e ∈ (T).edges) (hs : e.1.form.NormalizedReady) : e.2.2.form.NormalizedReady := by
  rcases finiteTableau_edge_input_or_empty X root h with ⟨M, hn, hM⟩ | hempty
  · exact hM.normalizedReady (hs.2 M hn)
  · rw [hempty]
    simp [emptyFinalState]

theorem finiteTableau_final_continuation :
    ∃ empty : (T).states, empty ∈ (T).goalModes ∧ (T).label empty.val = ∅ ∧
      ∀ f : (T).states, f ∈ (T).goalModes → f ≠ empty →
        ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ (T).edges ∧ l.guards = ∅ := by
  have hf := finiteTableau_empty_final (Clock := Clock) X root
  let empty : (T).states := ⟨emptyFinalState, hf.2⟩
  refine ⟨empty, hf, emptyFinalState_labels, ?_⟩
  intro f final ne
  exact ⟨empty.val.incoming,
    finiteTableau_final_empty_edge X root final (fun he => ne (Subtype.ext he)), rfl⟩

end

theorem finiteTableau_initial_normalizedReady (X : Set Var) (root : Formula.NormalizedInput Var)
    {e : EdgeLabel Clock × ClosureState Clock Var}
    (h : e ∈ (finiteTableau (Clock := Clock) X root.val).initial) :
    e.2.form.NormalizedReady := by
  apply h.1.2.1.normalizedReady
  simpa only [plainInitialState, Section3.StateForm.normalizedReady_ofLocal, Local.NormalizedReady,
    Predicate.NormalizedReady, predicateNormalizedReady] using root.property

end STLTableau.Section4.Finiteness
