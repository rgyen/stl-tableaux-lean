import STLTableaux.Automata.Translation.TypedTableauAutomata
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)

noncomputable def visitMarker (s : (T.typedAutomaton h τ).State) : Marker :=
  if s.val.2 T.bit = 1 then .closed else .open

theorem label_eq_visitMarker (s : (T.typedAutomaton h τ).State) (m : Marker)
    (hm : Local.marker m ∈ T.label s.val.1.val) :
    T.visitMarker h τ s = m := by
  have hi := s.property.2.2.2 m hm
  cases m with
  | closed => simp [visitMarker, hi.mp rfl]
  | «open» =>
    have hn : s.val.2 T.bit ≠ 1 := fun he => Marker.noConfusion (hi.mpr he)
    simp [visitMarker, hn]

theorem zero_jump_markers {s s' : (T.typedAutomaton h τ).State}
    (hj : (T.typedAutomaton h τ).DiscreteStep s s') (hz : s.val.2 T.dwell = 0) :
    T.visitMarker h τ s = .closed ∧ T.visitMarker h τ s' = .open := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hzero, _⟩ := hj
  obtain ⟨hs, hs'⟩ := hzero hz
  simp [visitMarker, hs, hs']

theorem execution_first_closed {σ : FiniteSignal T.TypedVar}
    (e : (T.typedAutomaton h τ).Execution σ) :
    T.visitMarker h τ e.initialState = .closed := by
  obtain ⟨_, _, _, _, _, _, hb⟩ := e.initial_mem
  simp [visitMarker, hb]

theorem open_jump_checks_source {s s' : (T.typedAutomaton h τ).State}
    (hj : (T.typedAutomaton h τ).DiscreteStep s s')
    (ho : T.visitMarker h τ s' = .open) : T.atomsAt s.val.1 s'.val.2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpost⟩ := hj
  apply hpost
  rcases s'.property.1 with hz | hone
  · exact hz
  · simp [visitMarker, hone] at ho

/-- For indexed visits, zero-width pieces need actual zero-residence jumps,
not an additional marker compatibility hypothesis. The final boundary marker
is a sentinel making the last right endpoint open. -/
noncomputable def partitionOfVisitBounds {n : ℕ} (b : Fin (n+1) → ℝ)
    (hb : Monotone b) (m : Fin (n+1) → Marker)
    (first : m 0 = .closed) (last : m (Fin.last n) = .closed)
    (zero : ∀ i : Fin n, b i.castSucc = b i.succ →
      ∃ s s' : (T.typedAutomaton h τ).State,
        (T.typedAutomaton h τ).DiscreteStep s s' ∧ s.val.2 T.dwell = 0 ∧
        m i.castSucc = T.visitMarker h τ s ∧ m i.succ = T.visitMarker h τ s') :
    IntervalPartition (Set.Ico (b 0) (b (Fin.last n))) := by
  apply IntervalPartition.ofSingletonBoundaries b hb m _ first last
  intro i he
  obtain ⟨s, s', hj, hz, hs, hs'⟩ := zero i he
  obtain ⟨hc, ho⟩ := T.zero_jump_markers h τ hj hz
  exact ⟨hs.trans hc, hs'.trans ho⟩

end STLTableau.Section4.Tableau
