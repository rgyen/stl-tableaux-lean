import STLTableaux.Automata.Translation.InitialClockSupport
import STLTableaux.Finiteness.Correctness.JudgementTraceFreeSupport
import STLTableaux.Closure.Support.ClosureFreeSupport
import STLTableaux.Automata.Recognition.TraceClockSchedule
import STLTableaux.Automata.Recognition.RealClockTrace

/-! All actual finite-root runs, not just selected free-safe runs, have closed
traces. Thus one satisfied trace suffices for all initial clock valuations. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

theorem derives_freeClocks_subset {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (hd : Derives N F) :
    F.freeClocks ⊆ N.freeClocks := by
  cases hd with
  | original hc _ =>
    simpa only [Section3.TransitionForm.freeClocks, Section3.TransitionForm.bodyFreeClocks,
      Section3.TransitionForm.ofState, Set.union_empty, Section3.StateForm.freeClocks] using
      ConcreteContextual.closure_freeClocks_subset hc
  | resolved hd hi hf _ => exact selected_resolution_free_subset hd hi hf

theorem derives_iff_freeDerives (N : Section3.StateForm Clock Var)
    (F : Section3.TransitionForm Clock Var) : Derives N F ↔ FreeDerives N F :=
  ⟨fun h => ⟨h, derives_freeClocks_subset h⟩, fun h => h.1⟩

variable [Infinite Clock]

theorem finiteRootTableau_initial_freeClocks_empty (X : Set Var) (root : Formula Var)
    (e : EdgeLabel Clock × Section3.TransitionForm Clock Var)
    (he : e ∈ (finiteRootTableau (Clock := Clock) X root).initial) :
    e.2.freeClocks = ∅ := by
  apply Set.eq_empty_of_subset_empty (derives_freeClocks_subset he.1.1 |>.trans ?_)
  simp [Section3.StateForm.freeClocks, Section3.StateForm.guardClocks,
    Section3.StateForm.localClocks, Section3.StateForm.ofLocal,
    Section3.Local.freeClocks, Section3.Local.toJudgement, Section3.Judgement.freeClocks]

theorem finiteRootTableau_fullTrace_closed (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root)) :
    (JudgementTableau.fullTrace p).freeClocks = ∅ := by
  have hlift := ((Subgraph.run_iff _ _ p).mp hr).1
  apply JudgementTableau.fullTrace_closed_of_run _ _ _ Derives
    (fun _ _ h => derives_freeClocks_subset h) p hlift
  simp [Section3.StateForm.freeClocks, Section3.StateForm.guardClocks,
    Section3.StateForm.localClocks, Section3.StateForm.ofLocal,
    Section3.Local.freeClocks, Section3.Local.toJudgement, Section3.Judgement.freeClocks]

theorem finiteRootTableau_trace_closed (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root)) :
    (p.trace JudgementTableau.labels JudgementTableau.labels_finite).freeClocks = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rw [← finiteRootTableau_fullTrace_closed X root p hr]
  exact ordinaryTrace_free_subset_fullTrace p

/-- The same accepting path works for every valuation; no exchange of
`∃ path` and `∀ valuation` is assumed. Trace satisfaction still has to be proved. -/
theorem finiteRootTableau_recognizes_of_one_trace (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root))
    (ha : p.accepting (finiteRootTableau (Clock := Clock) X root))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (hs : (p.trace JudgementTableau.labels JudgementTableau.labels_finite).holds
      σ P α ⟨0, by omega⟩) :
    (finiteRootTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite σ P :=
  Tableau.recognizes_of_closed_trace _ _ σ P p hr ha
    (finiteRootTableau_trace_closed X root p hr) α hs

/-- A single aligned clock schedule for the same accepting path suffices.
Schedule existence, label alignment and reset/duration recurrence remain
explicit obligations; no execution-to-partition theorem is assumed here. -/
theorem finiteRootTableau_recognizes_of_clock_schedule (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root))
    (ha : p.accepting (finiteRootTableau (Clock := Clock) X root))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
    ∀ (ν : ℕ → ClockValuation Clock) (hlen : t.length ≤ P.size + 1),
      (∀ i : Fin t.length, ∀ g ∈ (t.frameAt i).guards, g.holds (ν i.val)) →
      (∀ i : Fin t.length, ∀ l ∈ (t.frameAt i).locals,
        l.holds σ P ((t.frameAt i).resets.apply (ν i.val))
          ⟨i.val, by have := i.isLt; omega⟩) →
      (∀ (i : Fin t.length) (hi : i.val + 1 < t.length),
        ν (i.val + 1) = ClockResetSet.elapse ((t.frameAt i).resets.apply (ν i.val))
          (STLTableau.Judgement.duration P ⟨i.val, by omega⟩)) →
      (finiteRootTableau (Clock := Clock) X root).recognizes
        JudgementTableau.labels_finite σ P := by
  intro t ν hlen hg hl hn
  apply finiteRootTableau_recognizes_of_one_trace X root p hr ha σ P (ν 0)
  exact Trace.holdsWith_of_clock_schedule Section3.StateForm.locals σ P t ν
    ⟨0, by omega⟩ (by simpa only [Nat.zero_add] using hlen) hg
    (by simpa only [Nat.zero_add] using hl)
    (by simpa only [Nat.zero_add] using hn)

/-- Arbitrarily many frames can use the real clock traversal from an execution.
Closure removes all initial nonnegativity/compatibility requirements. Local
label and partition alignment must still be established on this same path. -/
theorem finiteRootTableau_given_trace_holds_of_realGuards (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
    ∀ (v : Clock → ℝ) (hlen : t.length ≤ P.size + 1),
      t.realGuardsHold σ P v ⟨0, by omega⟩ →
      (∀ (i : Fin t.length) (β : ClockValuation Clock), ∀ l ∈ (t.frameAt i).locals,
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) →
      ∀ α, t.holds σ P α ⟨0, by omega⟩ := by
  intro t v hlen hg hl
  exact t.forall_holds_of_closed_realGuards σ P v ⟨0, by omega⟩
    (by simpa only [Nat.zero_add] using hlen)
    (finiteRootTableau_trace_closed X root p hr) hg
    (by simpa only [Nat.zero_add] using hl)

/-- Recognition uses exactly the supplied run, without deleting any frame. -/
theorem finiteRootTableau_recognizes_of_realGuards (X : Set Var) (root : Formula Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (finiteRootTableau (Clock := Clock) X root))
    (ha : p.accepting (finiteRootTableau (Clock := Clock) X root))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
    ∀ (v : Clock → ℝ) (hlen : t.length ≤ P.size + 1),
      t.realGuardsHold σ P v ⟨0, by omega⟩ →
      (∀ (i : Fin t.length) (β : ClockValuation Clock), ∀ l ∈ (t.frameAt i).locals,
        l.holds σ P β ⟨i.val, by have := i.isLt; omega⟩) →
      (finiteRootTableau (Clock := Clock) X root).recognizes
        JudgementTableau.labels_finite σ P := by
  intro t v hlen hg hl
  exact ⟨p, hr, ha,
    finiteRootTableau_given_trace_holds_of_realGuards X root p hr σ P v hlen hg hl⟩

end STLTableau.Section4.Finiteness
