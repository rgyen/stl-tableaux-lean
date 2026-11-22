import STLTableaux.Automata.Recognition.LocalClosureRecognition

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "U" => (localClosureGraph (Clock := Clock) X root)

/-- An ordinary goal observed on a positive residence decides truth on every
signal with the same original values before that cut. A terminal goal
is deliberately not covered by this statement. -/
theorem early_goal_forces_prefix_truth {τ : ℝ} (h : (U).TranslationReady)
    {σ : FiniteSignal (U).TypedVar} (e : ((U).typedAutomaton h τ).Execution σ)
    (i : Fin e.count) {cut : ℝ} (hl : e.boundary i.castSucc < cut)
    (hr : cut ≤ e.boundary i.succ) (goal : (e.start i).val.1 ∈ (U).goalModes)
    (hh : σ.horizon = τ) (ρ : FiniteSignal Var) (proj : (U).TypedProjectsThrough σ ρ cut) :
    ρ.Satisfies root.val ⟨0,le_rfl,ρ.horizon_pos⟩ := by
  obtain ⟨xs,hp⟩ := (U).exists_beforeFlow h τ e i
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have hi' := finiteRootTableau_initial_nonterminal X root.val _ hi.1
  obtain ⟨pre,last⟩ := (U).ordinary_visits_of_initial h τ e hh hi' hp
  have ord : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ (U).terminalModes := by
    intro v hv
    rcases List.mem_append.mp hv with hx | hx
    · exact pre v hx
    · obtain rfl := List.mem_singleton.mp hx
      exact last
  obtain ⟨P,_,hrec⟩ := (U).ordinary_cut_layout_trace_through h τ e ρ proj hp hl hr goal
    JudgementTableau.labels_finite (localClosure_closed X root)
    (localClosure_visits_ready X root h e hp cut) ord
  exact original_formula_of_localClosure_recognizes X root ρ P hrec

end STLTableau.Section4.Finiteness
