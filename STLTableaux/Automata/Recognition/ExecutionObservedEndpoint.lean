import STLTableaux.Automata.Recognition.ExecutionObservedPath
import STLTableaux.Automata.Recognition.TraceClockSchedule
import STLTableaux.Automata.Execution.TerminalPruning

/-! Endpoint labels follow from actual frame start times and terminal pruning,
not merely from the number of partition positions. -/
namespace STLTableau.Section4
namespace Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem ObservedPath.frame_terminal_of_horizon_le {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite)
    (i : Fin (p.trace T.label hf).length)
    (hi : σ.horizon ≤ l + residenceBoundary ds i.val) :
    Section3.Local.terminal ∈ ((p.trace T.label hf).frameAt i).locals := by
  induction hp with
  | @last incoming s l r d ho hd =>
      have hz : i.val = 0 := by
        have hiz := i.isLt
        change i.val < 1 at hiz
        omega
      have hi' : σ.horizon ≤ l := by simpa [hz, residenceBoundary] using hi
      rcases ho with ho | ⟨_, _, ht⟩
      · exact (not_le_of_gt (ho.left_lt_horizon T h τ hτ e) hi').elim
      · exact ht
  | @step incoming s p l r z ds d ho hd hp ih =>
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        have hi' : σ.horizon ≤ l := by simpa [residenceBoundary] using hi
        exact (not_le_of_gt (ho.left_lt_horizon T h τ hτ e) hi').elim
      · intro hi
        apply ih j
        simpa [residenceBoundary, hd, add_assoc] using hi

end Tableau

namespace Path
variable {Clock Var State : Type*}

theorem pruned_frame_terminal_labels (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (hp : p.valid T.pruneTerminal)
    (i : Fin (p.trace T.label hf).length)
    (ht : Section3.Local.terminal ∈ ((p.trace T.label hf).frameAt i).locals)
    (q : Section3.Local Clock Var)
    (hq : q ∈ ((p.trace T.label hf).frameAt i).locals) :
    q = .terminal ∨ q = .marker ● := by
  induction p with
  | last incoming s => exact hp.2 ht q hq
  | step incoming s tail ih =>
      cases i using Fin.cases with
      | zero => exact hp.1.2 ht q hq
      | succ j => exact ih hp.2.1 j ht hq

end Path

namespace Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem ObservedPath.frame_endpoint_labels {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite) (hvalid : p.valid T.pruneTerminal)
    (i : Fin (p.trace T.label hf).length)
    (htime : σ.horizon ≤ l + residenceBoundary ds i.val)
    (q : Section3.Local Clock Var)
    (hq : q ∈ ((p.trace T.label hf).frameAt i).locals) :
    q = .terminal ∨ q = .marker ● :=
  p.pruned_frame_terminal_labels T hf hvalid i
    (hp.frame_terminal_of_horizon_le T h τ hτ e hf i htime) q hq

end Tableau
end STLTableau.Section4
