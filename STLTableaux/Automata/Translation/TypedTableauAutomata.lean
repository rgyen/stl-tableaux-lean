import STLTableaux.Automata.Translation.TableauAutomata

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- The original coordinates plus the residence clock and endpoint-type bit. -/
abbrev TypedVar := Sum T.HAVar Bool

def dwell : T.TypedVar := .inr false
def bit : T.TypedVar := .inr true

def old (v : T.TypedVar → ℝ) : T.HAVar → ℝ := fun x => v (.inl x)

def atomsAt (q : T.states) (v : T.TypedVar → ℝ) : Prop :=
  ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → T.atomHolds a (T.old v)

/-- Translation with the type invariant and boundary observation at jumps. -/
def typedAutomaton (h : T.TranslationReady) (τ : ℝ) :
    HybridAutomaton T.states (EdgeLabel Clock) T.TypedVar where
  modes_finite := h.states_finite.to_subtype
  variables_finite := by
    letI := h.variables_finite.to_subtype
    letI := h.clocks_finite.to_subtype
    unfold TypedVar HAVar
    infer_instance
  edge := {e | (e.1.val, e.2.1, e.2.2.val) ∈ T.edges}
  initial := {s | ∃ l, (l, s.1.val) ∈ T.initial ∧ ∃ v,
    T.guardsHold l v ∧ T.old s.2 = T.initialReset l.resets v ∧
    s.2 T.dwell = 0 ∧ s.2 T.bit = 1}
  invariant := {s | (s.2 T.bit = 0 ∨ s.2 T.bit = 1) ∧
    (s.1 ∉ T.terminalModes → s.2 (.inl T.globalClock) ≤ τ) ∧
    T.atomsAt s.1 s.2 ∧ ∀ m, Local.marker m ∈ T.label s.1.val →
      (m = Marker.closed ↔ s.2 T.bit = 1)}
  flow := fun s t v =>
    (∀ c : T.clocks, v (.inl (.inr (.inl c))) = s.2 (.inl (.inr (.inl c))) + t) ∧
    v (.inl T.globalClock) = s.2 (.inl T.globalClock) + t ∧
    v T.dwell = s.2 T.dwell + t ∧ v T.bit = s.2 T.bit
  trajectory_closed := by
    apply HybridFlow.Closed.of_rebase_add
    · intro q v a b r s first total
      dsimp only [Prod.snd] at *
      rcases first with ⟨fc, fg, fd, fb⟩
      rcases total with ⟨tc, tg, td, tb⟩
      refine ⟨?_, ?_, ?_, tb.trans fb.symm⟩
      · intro c
        rw [tc c, fc c]
        push_cast
        ring
      · rw [tg, fg]
        push_cast
        ring
      · rw [td, fd]
        push_cast
        ring
    · intro q v a b r s first second
      dsimp only [Prod.snd] at *
      rcases first with ⟨fc, fg, fd, fb⟩
      rcases second with ⟨sc, sg, sd, sb⟩
      refine ⟨?_, ?_, ?_, sb.trans fb⟩
      · intro c
        rw [sc c, fc c]
        push_cast
        ring
      · rw [sg, fg]
        push_cast
        ring
      · rw [sd, fd]
        push_cast
        ring
  jump := fun e s s' =>
    s.1 = e.val.1 ∧ s'.1 = e.val.2.2 ∧ T.guardsHold e.val.2.1 (T.old s.2) ∧
    (∀ c : T.clocks, s'.2 (.inl (.inr (.inl c))) =
      T.reset e.val.2.1.resets (T.old s.2) (.inr (.inl c))) ∧
    s'.2 (.inl T.globalClock) = s.2 (.inl T.globalClock) ∧ s'.2 T.dwell = 0 ∧
    (s'.1 ∈ T.terminalModes ↔ τ ≤ s'.2 (.inl T.globalClock)) ∧
    (s.2 T.dwell = 0 → s.2 T.bit = 1 ∧ s'.2 T.bit = 0) ∧
    (s'.2 T.bit = 0 → T.atomsAt s.1 s'.2)

/-- After a zero-residence jump another immediate jump is impossible. -/
theorem no_adjacent_zero (h : T.TranslationReady) (τ : ℝ)
    {a b c : (T.typedAutomaton h τ).State}
    (hab : (T.typedAutomaton h τ).DiscreteStep a b) (ha : a.val.2 T.dwell = 0) :
    ¬ (T.typedAutomaton h τ).DiscreteStep b c := by
  obtain ⟨_, _, _, _, _, _, _, _, hb, _, hz, _⟩ := hab
  intro hbc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hz', _⟩ := hbc
  linarith [(hz ha).2, (hz' hb).1]

end STLTableau.Section4.Tableau
