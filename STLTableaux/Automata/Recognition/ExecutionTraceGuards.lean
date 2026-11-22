import STLTableaux.Automata.Recognition.ExecutionPathTiming
import STLTableaux.Automata.Recognition.RealClockTrace

/-! The incoming-clock calculation on the unchanged execution path.
Only correspondence of residence times with partition durations is supplied;
the sequential guard checks come from `TimedPath` itself. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

theorem TimedPath.realGuardsHold {p v w ds} (ht : T.TimedPath p v w ds)
    (labels : State → Set (Section3.Local Clock Var)) (hf : ∀ s, (labels s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : STLTableau.Judgement.Position P) (ν : Clock → ℝ)
    (hlen : k.val + ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) =
        STLTableau.Judgement.duration P ⟨k.val + i.val, by omega⟩)
    (hg : ∀ g ∈ p.firstIncoming.guards, realComparison g.relation (ν g.clock) g.bound)
    (hv : ∀ c : T.clocks, v (.inr (.inl c)) =
      Trace.realReset p.firstIncoming.resets ν c.val) :
    (p.trace labels hf).realGuardsHold σ P ν k := by
  induction ht generalizing k ν with
  | last incoming s he => exact hg
  | @step incoming s p v u w r ds he hguard ht ih =>
    have hpos : 0 < ds.length := by
      rw [ht.frame_count T labels hf]
      exact Trace.length_pos _
    have hk : k.val < P.size := by simp only [List.length_cons] at hlen; omega
    have hr : (r : ℝ) = STLTableau.Judgement.duration P ⟨k.val, hk⟩ := by
      simpa using hd ⟨0, by simp⟩ (by simp only [List.length_cons]; omega)
    have hu (c : T.clocks) : u (.inr (.inl c)) =
        Trace.realReset incoming.resets ν c.val +
          STLTableau.Judgement.duration P ⟨k.val, hk⟩ := by
      rw [he.1 c, hv c, hr]
      rfl
    refine ⟨hg, ?_⟩
    simp only [dif_pos hk]
    apply ih ⟨k.val + 1, by omega⟩
      (fun c => Trace.realReset incoming.resets ν c +
        STLTableau.Judgement.duration P ⟨k.val, hk⟩)
      (by change k.val + 1 + ds.length ≤ P.size + 1
          simp only [List.length_cons] at hlen
          omega)
    · intro i hi
      simpa only [Fin.val_succ, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i.val] using
        hd i.succ (by change i.val + 1 + 1 < ds.length + 1; omega)
    · intro g hmem
      obtain ⟨hc, hcmp⟩ := hguard g hmem
      rw [hu ⟨g.clock, hc⟩] at hcmp
      exact hcmp
    · intro c
      cases hrst : p.firstIncoming.resets.value c.val with
      | none => simp only [reset, Trace.realReset, hrst]; exact hu c
      | some a => simp only [reset, Trace.realReset, hrst]

/-- Start with the actual pre-reset incoming valuation. No separately supplied
full clock schedule or nonnegative-clock premise is needed. -/
theorem TimedPath.realGuardsHold_of_initialReset {p v w ds}
    (ht : T.TimedPath p v w ds)
    (labels : State → Set (Section3.Local Clock Var)) (hf : ∀ s, (labels s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (k : STLTableau.Judgement.Position P)
    (hlen : k.val + ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) =
        STLTableau.Judgement.duration P ⟨k.val + i.val, by omega⟩)
    (u : T.HAVar → ℝ) (hg : T.guardsHold p.firstIncoming u)
    (hv : v = T.initialReset p.firstIncoming.resets u) :
    ∃ ν : Clock → ℝ,
      (∀ c : T.clocks, ν c.val = u (.inr (.inl c))) ∧
      (p.trace labels hf).realGuardsHold σ P ν k := by
  classical
  let ν : Clock → ℝ := fun c => if hc : c ∈ T.clocks then u (.inr (.inl ⟨c, hc⟩)) else 0
  have hν (c : T.clocks) : ν c.val = u (.inr (.inl c)) := by simp [ν, c.property]
  refine ⟨ν, hν, ht.realGuardsHold T labels hf σ P k ν hlen hd ?_ ?_⟩
  · intro g hmem
    obtain ⟨hc, hcmp⟩ := hg g hmem
    rw [hν ⟨g.clock, hc⟩]
    exact hcmp
  · intro c
    rw [hv]
    change T.reset p.firstIncoming.resets u (.inr (.inl c)) = _
    cases hr : p.firstIncoming.resets.value c.val with
    | none => simp only [reset, Trace.realReset, hr]; exact (hν c).symm
    | some a => simp only [reset, Trace.realReset, hr]

/-- The guard/reset calculation assembles a closed trace on the same
aligned partition. This statement is independent of input formulas and of the
tableau construction. Partition alignment and local labels must be established
separately; they are not consequences of `TimedPath` alone. -/
theorem TimedPath.forall_trace_holds_of_initialReset {p v w ds}
    (ht : T.TimedPath p v w ds)
    (labels : State → Set (Section3.Local Clock Var)) (hf : ∀ s, (labels s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hlen : ds.length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by omega⟩)
    (u : T.HAVar → ℝ) (hg : T.guardsHold p.firstIncoming u)
    (hv : v = T.initialReset p.firstIncoming.resets u)
    (hclosed : (p.trace labels hf).freeClocks = ∅)
    (hl : ∀ (i : Fin (p.trace labels hf).length) (β : ClockValuation Clock),
      ∀ l ∈ ((p.trace labels hf).frameAt i).locals,
        l.holds σ P β ⟨i.val, by
          have := ht.frame_count T labels hf
          have := i.isLt
          omega⟩) :
    ∀ α, (p.trace labels hf).holds σ P α ⟨0, by omega⟩ := by
  obtain ⟨ν, _, hguards⟩ := ht.realGuardsHold_of_initialReset T labels hf σ P
    ⟨0, by omega⟩ (by simpa using hlen) (by simpa using hd) u hg hv
  apply Trace.forall_holds_of_closed_realGuards σ P (p.trace labels hf) ν
    ⟨0, by omega⟩
    (by have := ht.frame_count T labels hf; simpa only [Nat.zero_add] using
          (show (p.trace labels hf).length ≤ P.size + 1 by omega))
    hclosed hguards
  simpa only [Nat.zero_add] using hl

end STLTableau.Section4.Tableau
