import STLTableaux.Tableau.Construction.Tableau

/-! Assemble trace satisfaction from one indexed sequence of incoming clock
valuations. Guards, resets, labels and partition durations use that same
sequence. The last frame may occupy the terminal position. -/
namespace STLTableau.Section4.Trace
open Section3
variable {Clock Var : Type*}

def frameAt : (t : Trace Clock Var) → Fin t.length → Section3.StateForm Clock Var
  | .last S, _ => S
  | .step S t, i => Fin.cases S t.frameAt i

/-- No existence of an aligned schedule or partition is assumed implicitly.
In particular, zero-time jumps cannot be turned into trace next steps unless
their assigned partition pieces have the matching duration. -/
theorem holdsWith_of_clock_schedule
    (labels : Section3.StateForm Clock Var → Set (Local Clock Var))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (ν : ℕ → ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hlen : k.val + t.length ≤ P.size + 1)
    (hguards : ∀ i : Fin t.length, ∀ g ∈ (t.frameAt i).guards, g.holds (ν i.val))
    (hlabels : ∀ i : Fin t.length, ∀ l ∈ labels (t.frameAt i),
      l.holds σ P ((t.frameAt i).resets.apply (ν i.val))
        ⟨k.val + i.val, by have := i.isLt; omega⟩)
    (hnext : ∀ (i : Fin t.length) (hi : i.val + 1 < t.length),
      ν (i.val + 1) = ClockResetSet.elapse ((t.frameAt i).resets.apply (ν i.val))
        (STLTableau.Judgement.duration P ⟨k.val + i.val, by omega⟩)) :
    t.holdsWith labels σ P (ν 0) k := by
  induction t generalizing ν k with
  | last S =>
    exact ⟨hguards ⟨0, by simp [length]⟩,
      by simpa only [frameAt, Nat.add_zero] using hlabels ⟨0, by simp [length]⟩⟩
  | step S t ih =>
    have hpos := t.length_pos
    have hk : k.val < P.size := by simp only [length] at hlen; omega
    have hz : (0 : ℕ) < (Trace.step S t).length := by simp [length]
    have hzero : (Trace.step S t).frameAt ⟨0, hz⟩ = S := rfl
    have hhead : (∀ g ∈ S.guards, g.holds (ν 0)) ∧
        ∀ l ∈ labels S, l.holds σ P (S.resets.apply (ν 0)) k := by
      constructor
      · simpa only [hzero] using hguards ⟨0, hz⟩
      · simpa only [hzero, Nat.add_zero] using hlabels ⟨0, hz⟩
    have hstep : ν 1 = ClockResetSet.elapse (S.resets.apply (ν 0))
        (STLTableau.Judgement.duration P ⟨k.val, hk⟩) := by
      simpa only [hzero, Nat.add_zero] using hnext ⟨0, hz⟩ (by simp only [length]; omega)
    refine ⟨hhead, ?_⟩
    simp only [dif_pos hk]
    rw [← hstep]
    refine ih (fun n => ν (n + 1)) ⟨k.val + 1, by omega⟩
      (by simp only [length] at hlen; change k.val + 1 + t.length ≤ P.size + 1; omega)
      ?_ ?_ ?_
    · intro i
      simpa [frameAt] using hguards i.succ
    · intro i
      simpa [frameAt, Nat.add_assoc, Nat.add_comm 1 i.val] using hlabels i.succ
    · intro i hi
      simpa [frameAt, Nat.add_assoc, Nat.add_comm 1 i.val] using
        hnext i.succ (by change i.val + 1 + 1 < t.length + 1; omega)

end STLTableau.Section4.Trace
