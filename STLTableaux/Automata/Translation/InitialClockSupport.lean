import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Finiteness.ClockAllocation.AllocatedSelectedPath
import STLTableaux.Closure.Support.ClosureGuardSupport

/-! Closed initial judgements do not inspect pre-reset clock values.
Only clocks read by the body are matched; unused negative real coordinates
are not excluded from the automaton. Closure is an explicit premise here. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var State : Type*}

theorem closed_initial_guards_empty (F : Section3.TransitionForm Clock Var)
    (hf : F.freeClocks = ∅) : F.current.guards = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hc : g.clock ∈ F.freeClocks := Or.inl ⟨g, hg, rfl⟩
  simp only [hf, Set.mem_empty_iff_false] at hc

theorem closed_initial_body_reset (F : Section3.TransitionForm Clock Var)
    (hf : F.freeClocks = ∅) : F.bodyFreeClocks ⊆ F.current.resets.clocks := by
  intro c hc
  by_contra hn
  have hfree : c ∈ F.freeClocks := Or.inr ⟨hc, hn⟩
  simp only [hf, Set.mem_empty_iff_false] at hfree

theorem closed_initial_guardsHold (T : Tableau Clock Var State)
    (F : Section3.TransitionForm Clock Var) (hf : F.freeClocks = ∅)
    (v : T.HAVar → ℝ) : T.guardsHold (JudgementTableau.incoming F) v := by
  intro g hg
  have hn := closed_initial_guards_empty F hf
  change g ∈ F.current.guards at hg
  rw [hn] at hg
  exact hg.elim

/-- Arbitrary real pre-reset values match every nonnegative tableau valuation
after reset, on precisely the clocks read by the remaining judgement. -/
theorem closed_initial_body_clock_agreement (T : Tableau Clock Var State)
    (F : Section3.TransitionForm Clock Var) (hf : F.freeClocks = ∅)
    (v : T.HAVar → ℝ) (α : ClockValuation Clock) (c : T.clocks)
    (hc : c.val ∈ F.bodyFreeClocks) :
    T.initialReset F.current.resets v (.inr (.inl c)) =
      (F.current.resets.apply α c.val : ℝ) := by
  obtain ⟨a, ha⟩ := closed_initial_body_reset F hf hc
  simp only [Tableau.initialReset, Tableau.reset, ClockResetSet.apply, ha]

theorem closed_initial_body_nonnegative (T : Tableau Clock Var State)
    (F : Section3.TransitionForm Clock Var) (hf : F.freeClocks = ∅)
    (v : T.HAVar → ℝ) (c : T.clocks) (hc : c.val ∈ F.bodyFreeClocks) :
    0 ≤ T.initialReset F.current.resets v (.inr (.inl c)) := by
  rw [closed_initial_body_clock_agreement T F hf v (fun _ => 0) c hc]
  exact (F.current.resets.apply (fun _ => 0) c.val).coe_nonneg

variable [DecidableEq Clock]

/-- Even arbitrary original closures introduce no current guards. Resolved
derivations have the stronger free-clock support property. -/
theorem derives_closed_input_guards_empty {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (hd : Derives N F)
    (hn : N.freeClocks = ∅) : F.current.guards = ∅ := by
  cases hd with
  | original hc _ =>
    rw [ConcreteContextual.closure_current_guards_eq hc]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hf : g.clock ∈ N.freeClocks := Or.inl ⟨g, hg, rfl⟩
    simp only [hn, Set.mem_empty_iff_false] at hf
  | resolved hd hi hf _ =>
    exact closed_initial_guards_empty F
      (Set.eq_empty_of_subset_empty (hn ▸ selected_resolution_free_subset hd hi hf))

/-- The selected free-safe construction supplies the closure premise.
This does not claim that every edge of the larger `Derives` graph is free-safe. -/
theorem freeDerives_closed_initial {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : FreeDerives N F)
    (hn : N.freeClocks = ∅) : F.freeClocks = ∅ :=
  Set.eq_empty_of_subset_empty (hn ▸ h.2)

theorem finiteRootTableau_initial_guards_empty [Infinite Clock]
    (X : Set Var) (root : Formula Var) (e : EdgeLabel Clock × Section3.TransitionForm Clock Var)
    (he : e ∈ (finiteRootTableau (Clock := Clock) X root).initial) : e.1.guards = ∅ := by
  rw [he.1.2]
  apply derives_closed_input_guards_empty he.1.1
  simp [Section3.StateForm.freeClocks, Section3.StateForm.guardClocks,
    Section3.StateForm.localClocks, Section3.StateForm.ofLocal,
    Section3.Local.freeClocks, Section3.Local.toJudgement, Section3.Judgement.freeClocks]

end STLTableau.Section4.Finiteness
