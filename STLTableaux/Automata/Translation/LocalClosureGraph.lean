import STLTableaux.Automata.Translation.FinalEmptyContinuation
import STLTableaux.Automata.Translation.NormalizedInputTypedCuts

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T₀" => (inputTableau (Clock := Clock) X root)
local notation "T₁" => (withEmptyContinuation (Clock := Clock) X root)

/-- Test full local judgements, not just the projected atomic labels. -/
def ConsistentPart (S : Section3.StateForm Clock Var) : Prop :=
  Local.terminal ∈ S.locals → ∀ l ∈ S.locals, l = .terminal ∨ l = .marker ●

def ConsistentClosure (F : Section3.TransitionForm Clock Var) : Prop :=
  ConsistentPart F.current ∧ ∀ N ∈ F.nextPart, ConsistentPart N

noncomputable def localClosureGraph :=
  Subgraph.restrict T₁ {F | ConsistentClosure F}
local notation "U" => (localClosureGraph (Clock := Clock) X root)

omit [DecidableEq Clock] [Infinite Clock] in
theorem empty_consistent : ConsistentClosure (emptyMode : Section3.TransitionForm Clock Var) :=
  ⟨fun ht => ht.elim,fun _ hm => by cases hm⟩

theorem localClosure_final_empty_edge {q : Section3.TransitionForm Clock Var}
    (hf : q ∈ (U).final) (hne : q ≠ emptyMode) : (q,emptyIncoming,emptyMode) ∈ (U).edges := by
  have hq : q ∈ (T₀).final := hf.1.resolve_left hne
  exact ⟨final_empty_edge X root q hq hne,hf.2,Or.inl rfl,empty_consistent⟩

theorem localClosure_terminal_labels (q : (U).states) (ht : q ∈ (U).terminalModes) :
    ∀ l ∈ (U).label q.val, l = .terminal ∨ l = .marker ● :=
  fun l hl => q.property.2.1 ht.1 l hl.1

theorem localClosure_ready (h : (T₀).TranslationReady) : (U).TranslationReady where
  states_finite := (withEmptyContinuation_ready X root h).states_finite.subset Set.inter_subset_left
  variables_finite := h.variables_finite
  clocks_finite := h.clocks_finite
  edge_states := fun _ he => he.2
  initial_states := fun _ he => he.2
  final_states := fun _ he => he.2
  edge_guards := fun e he => (withEmptyContinuation_ready X root h).edge_guards e he.1
  edge_resets := fun e he => (withEmptyContinuation_ready X root h).edge_resets e he.1
  initial_guards := fun e he => h.initial_guards e he.1
  initial_resets := fun e he => h.initial_resets e he.1
  atom_variables := fun q hq => (withEmptyContinuation_ready X root h).atom_variables q hq.1

private theorem edge_empty_absurd {l : EdgeLabel Clock} {q : Section3.TransitionForm Clock Var}
    (he : (emptyMode,l,q) ∈ (U).edges) : False := by
  rcases he.1 with old | added
  · obtain ⟨_,_,N,hn,_,_⟩ := old.1
    cases hn
  · exact added.2.1 rfl

/-- The added empty frame carries no free clock: remove it only for this
syntactic calculation, not from the execution or its recognition witness. -/
private theorem old_clock_witness (p : Path Clock (Section3.TransitionForm Clock Var))
    (hv : p.valid U) (hs : p.firstState ∈ (T₀).states) :
    ∃ q : Path Clock (Section3.TransitionForm Clock Var),
      q.valid T₀ ∧ q.firstState = p.firstState ∧ q.firstIncoming = p.firstIncoming ∧
      (q.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks =
      (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks := by
  induction p with
  | last l s => exact ⟨.last l s,hs,rfl,rfl,rfl⟩
  | step l s p ih =>
    rcases hv.2.2.1 with he | ha
    · obtain ⟨q,hq,hqs,hql,hc⟩ := ih hv.2.1 he.2.2
      refine ⟨.step l s q,⟨hs,hq,?_⟩,rfl,rfl,?_⟩
      · simpa only [hqs,hql] using he
      · simp only [Path.trace,Trace.freeClocks,hc]
    · obtain ⟨_,_,hin,hst⟩ := ha
      cases p with
      | step l' s' p' =>
        change s' = emptyMode at hst
        subst s'
        exact (edge_empty_absurd X root hv.2.1.2.2).elim
      | last l' s' =>
        change l' = emptyIncoming at hin
        change s' = emptyMode at hst
        subst l'; subst s'
        refine ⟨.last l s,hs,rfl,rfl,?_⟩
        have hem : JudgementTableau.labels (emptyMode : Section3.TransitionForm Clock Var) = ∅ :=
          empty_label X root
        simp [Path.trace,Trace.freeClocks,emptyIncoming,hem,Section3.StateForm.freeClocks,Section3.StateForm.guardClocks,
          Section3.StateForm.localClocks]

theorem localClosure_closed (p : Path Clock (Section3.TransitionForm Clock Var)) (hr : p.run U) :
    (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks = ∅ := by
  have hi : (p.firstIncoming,p.firstState) ∈ (T₀).initial := hr.2.1
  obtain ⟨q,hq,hs,hl,hc⟩ := old_clock_witness X root p hr.1 hi.2
  exact hc.symm.trans (finiteRootTableau_trace_closed X root.val q
    ⟨hq,by rw [hs,hl]; exact hi⟩)

theorem localClosure_visits_ready {τ : ℝ} (h : (U).TranslationReady) {σ : FiniteSignal (U).TypedVar}
    (e : ((U).typedAutomaton h τ).Execution σ) {i xs}
    (hp : Tableau.BeforeFlow U h τ e i xs) (cut : ℝ) :
    ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ (U).label v.state.val.1.val, l.NormalizedReady := by
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have inv := (U).beforeFlow_preserves h τ e
    (inputTableau_initial_normalizedReady X root hi.1) (fun a l b he ha => by
      rcases he.1 with old | added
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

theorem localClosure_ordinary {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).typedAutomaton h τ).Execution σ)
    (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    {i xs} (hp : Tableau.BeforeFlow U h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (goal : (e.start i).val.1 ∈ (U).goalModes) (hh : σ.horizon = τ)
    (P : IntervalPartition ρ.domain)
    (induced : (U).CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P) :
    (U).recognizes JudgementTableau.labels_finite ρ P := by
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  exact (U).recognizes_on_induced_ordinary_cut h τ e ρ proj hp hl hr goal
    JudgementTableau.labels_finite (localClosure_closed X root) (localClosure_visits_ready X root h e hp cut)
    hh (finiteRootTableau_initial_nonterminal X root.val _ hi.1) P induced

/-- Terminal cut entered directly from the last flow. The continuation
edge is retained in this graph; no terminal label premise is supplied. -/
theorem localClosure_terminal_jump {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).typedAutomaton h τ).Execution σ)
    (ρ : FiniteSignal Var) (proj : (U).TypedProjectsTo σ ρ)
    {i xs} (hp : Tableau.BeforeFlow U h τ e i xs)
    (jump : ((U).typedAutomaton h τ).DiscreteStep (e.finish i) e.finalState)
    (term : e.finalState.val.1 ∈ (U).terminalModes)
    (goal : e.finalState.val.1 ∈ (U).goalModes) (hh : σ.horizon = τ)
    (P : IntervalPartition ρ.domain)
    (induced : (U).CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P) :
    (U).recognizes JudgementTableau.labels_finite ρ P := by
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  exact (U).recognizes_on_induced_terminal_cut h τ e ρ proj hp jump term goal hh
    (finiteRootTableau_initial_nonterminal X root.val _ hi.1) JudgementTableau.labels_finite
    (localClosure_closed X root) (localClosure_visits_ready X root h e hp τ)
    (localClosure_terminal_labels X root _ term) P induced

/-- On entry into a terminal state, its generator already contains star.
The local contradiction test on the predecessor's next part therefore
excludes even non-atomic interval predicates from this generator. -/
theorem terminal_entry_generator {s t : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (he : (s,l,t) ∈ (U).edges) (ht : Local.terminal ∈ (U).label t) :
    ∃ N, s.nextPart = some N ∧ Derives N t ∧ Local.terminal ∈ N.locals ∧
      ∀ x ∈ N.locals, x = .terminal ∨ x = .marker ● := by
  rcases he.1 with old | added
  · obtain ⟨_,_,N,hn,hd,_⟩ := old.1
    have hh : Local.terminal ∈ N.locals := by
      by_contra hno
      exact derives_no_terminal hd hno ht.1
    exact ⟨N,hn,hd,hh,he.2.1.2.2 N hn hh⟩
  · have hte : t = emptyMode := added.2.2.2
    subst t
    change Local.terminal ∈ (T₁).label emptyMode at ht
    rw [empty_label] at ht
    exact ht.elim

end STLTableau.Section4.Finiteness
