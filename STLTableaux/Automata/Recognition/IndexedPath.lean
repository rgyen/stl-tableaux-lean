import STLTableaux.Automata.Recognition.TraceClockSchedule

/-! Assemble a single path from ordered flow states and incoming labels.
This supplies graph bookkeeping, not a choice of representatives or markers. -/
namespace STLTableau.Section4.Path
variable {Clock Var State : Type*}

/-- `n` transitions, hence `n + 1` frames. Label zero is the initial
incoming label; label `i + 1` belongs to the edge from state `i` to `i + 1`. -/
def ofIndexed : (n : ℕ) → (Fin (n + 1) → EdgeLabel Clock) →
    (Fin (n + 1) → State) → Path Clock State
  | 0, incoming, states => .last (incoming 0) (states 0)
  | n + 1, incoming, states => .step (incoming 0) (states 0)
      (ofIndexed n (fun i => incoming i.succ) (fun i => states i.succ))

@[simp] theorem ofIndexed_firstState (n : ℕ) (incoming) (states) :
    (ofIndexed (Clock := Clock) (State := State) n incoming states).firstState = states 0 := by
  cases n <;> rfl

@[simp] theorem ofIndexed_firstIncoming (n : ℕ) (incoming) (states) :
    (ofIndexed (Clock := Clock) (State := State) n incoming states).firstIncoming = incoming 0 := by
  cases n <;> rfl

@[simp] theorem ofIndexed_lastState (n : ℕ) (incoming) (states) :
    (ofIndexed (Clock := Clock) (State := State) n incoming states).lastState =
      states (Fin.last n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _ _

theorem ofIndexed_valid (T : Tableau Clock Var State) (n : ℕ) (incoming) (states)
    (hs : ∀ i, states i ∈ T.states)
    (he : ∀ i : Fin n, (states i.castSucc, incoming i.succ, states i.succ) ∈ T.edges) :
    (ofIndexed n incoming states).valid T := by
  induction n with
  | zero => exact hs 0
  | succ n ih =>
    refine ⟨hs 0, ih _ _ (fun i => hs i.succ) (fun i => he i.succ), ?_⟩
    simpa using he 0

theorem ofIndexed_run (T : Tableau Clock Var State) (n : ℕ) (incoming) (states)
    (hs : ∀ i, states i ∈ T.states)
    (he : ∀ i : Fin n, (states i.castSucc, incoming i.succ, states i.succ) ∈ T.edges)
    (hi : (incoming 0, states 0) ∈ T.initial) :
    (ofIndexed n incoming states).run T :=
  ⟨ofIndexed_valid T n incoming states hs he, by simpa using hi⟩

theorem ofIndexed_accepting (T : Tableau Clock Var State) (n : ℕ) (incoming) (states)
    (hs : ∀ i, states i ∈ T.states)
    (he : ∀ i : Fin n, (states i.castSucc, incoming i.succ, states i.succ) ∈ T.edges)
    (hf : states (Fin.last n) ∈ T.final) :
    (ofIndexed n incoming states).accepting T :=
  ⟨ofIndexed_valid T n incoming states hs he, by simpa using hf⟩

@[simp] theorem ofIndexed_trace_length (labels : State → Set (Section3.Local Clock Var))
    (hfinite : ∀ s, (labels s).Finite) (n : ℕ) (incoming) (states) :
    ((ofIndexed n incoming states).trace labels hfinite).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ofIndexed, trace, Trace.length, ih]

/-- Frame lookup preserves the exact incoming guard/reset and state label. -/
theorem ofIndexed_trace_frameAt (labels : State → Set (Section3.Local Clock Var))
    (hfinite : ∀ s, (labels s).Finite) (n : ℕ) (incoming) (states) (i : Fin (n + 1)) :
    ((ofIndexed n incoming states).trace labels hfinite).frameAt
      (i.cast (ofIndexed_trace_length labels hfinite n incoming states).symm) =
      ⟨(incoming i).guards, (incoming i).guards_finite, (incoming i).resets,
        labels (states i), hfinite (states i)⟩ := by
  induction n with
  | zero => have : i = 0 := Fin.ext (by have := i.isLt; omega); subst i; rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih _ _ j

end STLTableau.Section4.Path
