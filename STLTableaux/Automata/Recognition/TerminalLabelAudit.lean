import STLTableaux.Automata.Recognition.DirectFlowRecognition

/-! Necessary local conditions for a genuine satisfied trace. These lemmas
do not assert that arbitrary automaton paths satisfy these conditions. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var : Type*}

namespace Trace

/-- Every frame of a satisfied trace has one joint local satisfaction witness.
This is weaker than extracting the full clock schedule, but preserves the
fact that all locals in the frame must hold at the SAME position/valuation. -/
theorem frame_locals_satisfiable (t : Trace Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : t.holds σ P α k) (i : Fin t.length) :
    ∃ (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P),
      ∀ l ∈ (t.frameAt i).locals, l.holds σ P β j := by
  induction t generalizing α k with
  | last S => exact ⟨S.resets.apply α, k, hs.2⟩
  | step S t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨S.resets.apply α, k, hs.1.2⟩
    · by_cases hk : k.val < P.size
      · have ht : t.holds σ P
            (ClockResetSet.elapse (S.resets.apply α)
              (STLTableau.Judgement.duration P ⟨k.val, hk⟩)) ⟨k.val + 1, by omega⟩ := by
          simpa only [holds, dif_pos hk] using hs.2
        exact ih _ _ ht j
      · have hf : False := by simpa only [dif_neg hk] using hs.2
        exact hf.elim

/-- A terminal local forces its entire frame to contain only terminal or
closed-marker locals. This is a consequence of trace satisfaction, not an
invariant assumed for every structurally generated state. -/
theorem terminal_frame_compatible (t : Trace Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : t.holds σ P α k) (i : Fin t.length)
    (ht : Local.terminal ∈ (t.frameAt i).locals) :
    ∀ l ∈ (t.frameAt i).locals, l = .terminal ∨ l = .marker ● := by
  obtain ⟨β, j, hj⟩ := t.frame_locals_satisfiable σ P α k hs i
  have he : j.val = P.size := hj .terminal ht
  have he' : j = ⟨P.size, by omega⟩ := Fin.ext he
  rw [he'] at hj
  intro l hl
  exact (Finiteness.local_holds_terminal_iff σ P β l).mp (hj l hl)

theorem not_holds_of_terminal_predicate (t : Trace Clock Var)
    (i : Fin t.length) (ht : Local.terminal ∈ (t.frameAt i).locals)
    (p : Predicate Clock Var) (hp : Local.predicate p ∈ (t.frameAt i).locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    ¬ t.holds σ P α k := by
  intro hs
  have h := t.terminal_frame_compatible σ P α k hs i ht (.predicate p) hp
  rcases h with h | h <;> cases h

theorem not_holds_of_terminal_open_marker (t : Trace Clock Var)
    (i : Fin t.length) (ht : Local.terminal ∈ (t.frameAt i).locals)
    (ho : Local.marker ○ ∈ (t.frameAt i).locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    ¬ t.holds σ P α k := by
  intro hs
  have h := t.terminal_frame_compatible σ P α k hs i ht (.marker ○) ho
  rcases h with h | h <;> cases h

/-- A single frame cannot demand two different boundary markers, including
at the terminal position. This does not choose markers for an arbitrary run. -/
theorem frame_markers_equal (t : Trace Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : t.holds σ P α k) (i : Fin t.length) (a b : Marker)
    (ha : Local.marker a ∈ (t.frameAt i).locals)
    (hb : Local.marker b ∈ (t.frameAt i).locals) : a = b := by
  obtain ⟨β, j, hj⟩ := t.frame_locals_satisfiable σ P α k hs i
  have hma := hj (.marker a) ha
  have hmb := hj (.marker b) hb
  by_cases hpos : j.val < P.size
  · simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hpos] at hma hmb
    exact hma.symm.trans hmb
  · simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_neg hpos] at hma hmb
    exact hma.trans hmb.symm

end Trace
end STLTableau.Section4
