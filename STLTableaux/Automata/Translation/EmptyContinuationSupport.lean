import STLTableaux.Automata.Translation.EndPositionCorrectness

/-! Trace closure, normalized input support and final continuations for the
unfiltered tableau. No local contradiction filter is imposed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T₀" => inputTableau (Clock := Clock) X root
local notation "U" => withEmptyContinuation (Clock := Clock) X root

theorem emptyContinuation_edge_empty_absurd {l : EdgeLabel Clock}
    {q : Section3.TransitionForm Clock Var}
    (he : (emptyMode, l, q) ∈ (U).edges) : False := by
  rcases he with old | added
  · obtain ⟨_, _, N, hn, _, _⟩ := old.1
    cases hn
  · exact added.2.1 rfl

private theorem emptyContinuation_old_clock_witness
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hv : p.valid U) (hs : p.firstState ∈ (T₀).states) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.valid T₀ ∧ q.firstState = p.firstState ∧ q.firstIncoming = p.firstIncoming ∧
      (q.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks =
      (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks := by
  induction p with
  | last l s => exact ⟨.last l s, hs, rfl, rfl, rfl⟩
  | step l s p ih =>
    rcases hv.2.2 with he | ha
    · obtain ⟨q, hq, hqs, hql, hc⟩ := ih hv.2.1 he.2.2
      refine ⟨.step l s q, ⟨hs, hq, ?_⟩, rfl, rfl, ?_⟩
      · simpa only [hqs, hql] using he
      · simp only [Path.trace, Trace.freeClocks, hc]
    · obtain ⟨_, _, hin, hst⟩ := ha
      cases p with
      | step l' s' p' =>
        change s' = emptyMode at hst
        subst s'
        exact (emptyContinuation_edge_empty_absurd X root hv.2.1.2.2).elim
      | last l' s' =>
        change l' = emptyIncoming at hin
        change s' = emptyMode at hst
        subst l'
        subst s'
        refine ⟨.last l s, hs, rfl, rfl, ?_⟩
        have hem : JudgementTableau.labels (emptyMode : Section3.TransitionForm Clock Var) = ∅ :=
          empty_label X root
        simp [Path.trace, Trace.freeClocks, emptyIncoming, hem, Section3.StateForm.freeClocks,
          Section3.StateForm.guardClocks, Section3.StateForm.localClocks]

theorem emptyContinuation_closed (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run U) :
    (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks = ∅ := by
  have hi : (p.firstIncoming, p.firstState) ∈ (T₀).initial := hr.2
  obtain ⟨q, hq, hs, hl, hc⟩ := emptyContinuation_old_clock_witness X root p hr.1 hi.2
  exact hc.symm.trans (finiteRootTableau_trace_closed X root.val q
    ⟨hq, by rw [hs, hl]; exact hi⟩)

theorem emptyContinuation_visits_ready {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).typedAutomaton h τ).Execution σ) {i xs}
    (hp : Tableau.BeforeFlow U h τ e i xs) (cut : ℝ) :
    ∀ v ∈ xs ++ [⟨e.start i, e.boundary i.castSucc, cut⟩],
      ∀ l ∈ (U).label v.state.val.1.val, l.NormalizedReady := by
  obtain ⟨l, hi, _, _, _, _, _⟩ := e.initial_mem
  have inv := (U).beforeFlow_preserves h τ e
    (inputTableau_initial_normalizedReady X root hi) (fun a l b he ha => by
      rcases he with old | added
      · exact inputTableau_edge_normalizedReady X root old ha
      · rw [show b = emptyMode from added.2.2.2]
        exact ⟨fun _ hm => hm.elim, fun _ hn => by cases hn⟩) hp
  intro v hv l hl
  have hs : v.state.val.1.val.NormalizedReady := by
    rcases List.mem_append.mp hv with hx | hx
    · exact inv.1 v hx
    · obtain rfl := List.mem_singleton.mp hx
      exact inv.2
  exact hs.1 l hl.1

theorem empty_continuation_data :
    ∃ empty : (U).states, empty.val = emptyMode ∧ empty ∈ (U).goalModes ∧
      (U).label empty.val = ∅ ∧
      ∀ f : (U).states, f ∈ (U).goalModes → f ≠ empty →
        ∃ l : EdgeLabel Clock, (f.val, l, empty.val) ∈ (U).edges ∧ l.guards = ∅ ∧
          l.resets = ClockResetSet.empty := by
  let q : (U).states := ⟨emptyMode, Or.inl rfl⟩
  refine ⟨q, rfl, Or.inl rfl, empty_label X root, ?_⟩
  intro f hf hne
  have hneq : f.val ≠ emptyMode := fun he => hne (Subtype.ext he)
  exact ⟨emptyIncoming, final_empty_edge X root _ (hf.resolve_left hneq) hneq, rfl, rfl⟩

private theorem emptyContinuation_subformula_of_inventory {φ root : Formula Var}
    (hm : φ ∈ Finiteness.rootPlainFormulas root) : Formula.IsSubformula φ root := by
  classical
  induction root with
  | truth | atom =>
    simp only [Finiteness.rootPlainFormulas, Finset.mem_singleton] at hm
    exact hm ▸ .refl _
  | neg φ ih =>
    simp only [Finiteness.rootPlainFormulas, Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact .refl _
    · exact .neg (ih hm)
  | and φ ψ ih ik =>
    simp only [Finiteness.rootPlainFormulas, Finset.mem_insert, Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .and_left (ih hm)
    · exact .and_right (ik hm)
  | «until» I φ ψ ih ik =>
    simp only [Finiteness.rootPlainFormulas, Finset.mem_insert, Finset.mem_union] at hm
    rcases hm with rfl | hm | hm
    · exact .refl _
    · exact .until_left (ih hm)
    · exact .until_right (ik hm)

theorem emptyContinuation_atom_subformula (q : (U).states) (a : AtomicProposition Var)
    (hm : Local.predicate (.plain (.atom a)) ∈ (U).label q.val) :
    Formula.IsSubformula (.atom a) root.val := by
  rcases q.property with he | old
  · rw [he, empty_label] at hm
    exact hm.elim
  · exact emptyContinuation_subformula_of_inventory (FiniteInventory.atom_mem_plain_inventory _ _ a
      (old.2.1.1 hm.1))

theorem emptyContinuation_final_successor (a b : (U).states) (l : EdgeLabel Clock)
    (goal : a ∈ (U).goalModes) (edge : (a.val, l, b.val) ∈ (U).edges) :
    b ∈ (U).goalModes := by
  rcases edge with old | added
  · rcases goal with he | hf
    · have hn : a.val.nextPart = none := he ▸ rfl
      obtain ⟨_, _, N, hN, _, _⟩ := old.1
      rw [hn] at hN
      cases hN
    · exact (old_final_has_no_edge X root hf old).elim
  · exact Or.inl added.2.2.2

end STLTableau.Section4.Finiteness
