import STLTableaux.Automata.Recognition.TraceClockSchedule
import STLTableaux.Automata.Translation.TableauAutomata

/-! Proof-only transfer of real-valued guard calculations to NNReal tableau
valuations. This does not change trace semantics or invent partition positions. -/
namespace STLTableau.Section4.Trace
open Section3
variable {Clock Var : Type*}

def realReset (Λ : ClockResetSet Clock) (v : Clock → ℝ) : Clock → ℝ :=
  fun c => match Λ.value c with | some a => a | none => v c

/-- Numerical guard/reset traversal only; local labels are checked separately
on the SAME trace and partition. There is no nonnegativity premise on `v`. -/
def realGuardsHold (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (v : Clock → ℝ) (k : STLTableau.Judgement.Position P) : Trace Clock Var → Prop
  | .last S => ∀ g ∈ S.guards, Tableau.realComparison g.relation (v g.clock) g.bound
  | .step S t =>
      (∀ g ∈ S.guards, Tableau.realComparison g.relation (v g.clock) g.bound) ∧
      if hk : k.val < P.size then
        realGuardsHold σ P
          (fun c => realReset S.resets v c + STLTableau.Judgement.duration P ⟨k.val, hk⟩)
          ⟨k.val + 1, by omega⟩ t
      else False

/-- Assemble the real guard traversal from the incoming values at each frame.
The recurrence uses precisely this partition's durations, not independently
chosen execution times. Initial real values need not be nonnegative. -/
theorem realGuardsHold_of_schedule
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (ν : ℕ → Clock → ℝ)
    (k : STLTableau.Judgement.Position P)
    (hlen : k.val + t.length ≤ P.size + 1)
    (hg : ∀ i : Fin t.length, ∀ g ∈ (t.frameAt i).guards,
      Tableau.realComparison g.relation (ν i.val g.clock) g.bound)
    (hn : ∀ (i : Fin t.length) (hi : i.val + 1 < t.length),
      ν (i.val + 1) = fun c => realReset (t.frameAt i).resets (ν i.val) c +
        STLTableau.Judgement.duration P ⟨k.val + i.val, by omega⟩) :
    t.realGuardsHold σ P (ν 0) k := by
  induction t generalizing ν k with
  | last S => exact hg ⟨0, by simp [length]⟩
  | step S t ih =>
    have ht := t.length_pos
    have hk : k.val < P.size := by simp only [length] at hlen; omega
    have hz : 0 < (Trace.step S t).length := by simp [length]
    have hzero : (Trace.step S t).frameAt ⟨0, hz⟩ = S := rfl
    refine ⟨hg ⟨0, hz⟩, ?_⟩
    simp only [dif_pos hk]
    have hstep : ν 1 = fun c => realReset S.resets (ν 0) c +
        STLTableau.Judgement.duration P ⟨k.val, hk⟩ := by
      simpa only [hzero, Nat.add_zero] using hn ⟨0, hz⟩ (by simp only [length]; omega)
    rw [← hstep]
    refine ih (fun j => ν (j + 1)) ⟨k.val + 1, by omega⟩
      (by simp only [length] at hlen; change k.val + 1 + t.length ≤ P.size + 1; omega)
      ?_ ?_
    · intro i
      simpa [frameAt] using hg i.succ
    · intro i hi
      simpa [frameAt, Nat.add_assoc, Nat.add_comm 1 i.val] using
        hn i.succ (by change i.val + 1 + 1 < t.length + 1; omega)

/-- Agreement is needed only on free clocks of the remaining trace. A reset
establishes agreement regardless of the old real value, even if negative. -/
theorem holds_of_realGuards
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (v : Clock → ℝ) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hlen : k.val + t.length ≤ P.size + 1)
    (ha : ∀ c ∈ t.freeClocks, v c = (α c : ℝ))
    (hg : t.realGuardsHold σ P v k)
    (hl : ∀ (i : Fin t.length) (β : ClockValuation Clock),
      ∀ l ∈ (t.frameAt i).locals,
        l.holds σ P β ⟨k.val + i.val, by have := i.isLt; omega⟩) :
    t.holds σ P α k := by
  induction t generalizing v α k with
  | last S =>
    refine ⟨?_, ?_⟩
    · intro g hmem
      have hcmp := hg g hmem
      rw [ha g.clock (Or.inl ⟨g, hmem, rfl⟩)] at hcmp
      exact (Tableau.realComparison_coe _ _ _).mp hcmp
    · simpa only [frameAt, Nat.add_zero] using hl ⟨0, by simp [length]⟩ (S.resets.apply α)
  | step S t ih =>
    have htpos := t.length_pos
    have hk : k.val < P.size := by simp only [length] at hlen; omega
    have hz : 0 < (Trace.step S t).length := by simp [length]
    have hzero : (Trace.step S t).frameAt ⟨0, hz⟩ = S := rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro g hmem
      have hcmp := hg.1 g hmem
      rw [ha g.clock (Or.inl ⟨g, hmem, rfl⟩)] at hcmp
      exact (Tableau.realComparison_coe _ _ _).mp hcmp
    · simpa only [hzero, Nat.add_zero] using hl ⟨0, hz⟩ (S.resets.apply α)
    · simp only [dif_pos hk]
      apply ih (fun c => realReset S.resets v c +
        STLTableau.Judgement.duration P ⟨k.val, hk⟩)
        (ClockResetSet.elapse (S.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val, hk⟩))
        ⟨k.val + 1, by omega⟩
        (by simp only [length] at hlen; change k.val + 1 + t.length ≤ P.size + 1; omega)
      · intro c hc
        have he : realReset S.resets v c = (S.resets.apply α c : ℝ) := by
          cases hr : S.resets.value c with
          | some a => simp [realReset, ClockResetSet.apply, hr]
          | none =>
            have hn : c ∉ S.resets.clocks := by
              rintro ⟨a, he⟩
              rw [hr] at he
              cases he
            simpa only [realReset, ClockResetSet.apply, hr] using
              ha c (Or.inr ⟨Or.inr hc, hn⟩)
        simpa only [ClockResetSet.elapse, NNReal.coe_add] using
          congrArg (fun z : ℝ => z + STLTableau.Judgement.duration P ⟨k.val, hk⟩) he
      · simpa only [dif_pos hk] using hg.2
      · intro i β
        simpa [frameAt, Nat.add_assoc, Nat.add_comm 1 i.val] using hl i.succ β

/-- Arbitrary real initial clocks suffice for a closed trace, including
negative unused values. The same trace then holds for EVERY NNReal valuation. -/
theorem forall_holds_of_closed_realGuards
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (v : Clock → ℝ) (k : STLTableau.Judgement.Position P)
    (hlen : k.val + t.length ≤ P.size + 1) (hclosed : t.freeClocks = ∅)
    (hg : t.realGuardsHold σ P v k)
    (hl : ∀ (i : Fin t.length) (β : ClockValuation Clock),
      ∀ l ∈ (t.frameAt i).locals,
        l.holds σ P β ⟨k.val + i.val, by have := i.isLt; omega⟩) :
    ∀ α : ClockValuation Clock, t.holds σ P α k := by
  intro α
  exact t.holds_of_realGuards σ P v α k hlen (by simp [hclosed]) hg hl

end STLTableau.Section4.Trace
