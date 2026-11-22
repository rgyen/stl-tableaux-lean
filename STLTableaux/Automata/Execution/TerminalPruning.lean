import STLTableaux.Automata.Translation.TableauAutomata

/-! Remove positional contradictions before translation. No signal value at the
horizon is introduced, and neither judgement nor trace semantics is changed. -/
namespace STLTableau.Section4
open Section3
variable {Clock Var State : Type*}

namespace Tableau

def TerminalCompatible (T : Tableau Clock Var State) (s : State) : Prop :=
  Local.terminal ∈ T.label s →
    ∀ l ∈ T.label s, l = .terminal ∨ l = .marker ●

/-- Terminal-labelled states cannot carry interval obligations or open markers.
An outgoing edge would require a next position, so it is removed as well. -/
def pruneTerminal (T : Tableau Clock Var State) : Tableau Clock Var State where
  realVariables := T.realVariables
  clocks := T.clocks
  states := {s | s ∈ T.states ∧ T.TerminalCompatible s}
  edges := {e | e ∈ T.edges ∧ T.TerminalCompatible e.1 ∧
    T.TerminalCompatible e.2.2 ∧ Local.terminal ∉ T.label e.1}
  initial := {e | e ∈ T.initial ∧ T.TerminalCompatible e.2}
  final := {s | s ∈ T.final ∧ T.TerminalCompatible s}
  label := T.label
  label_atomic := T.label_atomic

theorem terminalCompatible_of_holds (T : Tableau Clock Var State)
    (s : State) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : ∀ l ∈ T.label s, l.holds σ P α k) : T.TerminalCompatible s := by
  intro ht l hl
  have hk : k.val = P.size := hs .terminal ht
  have hn : ¬ k.val < P.size := by omega
  have h := hs l hl
  cases l with
  | terminal => exact Or.inl rfl
  | marker m =>
      right
      have hm : m = ● := by
        simpa only [Local.holds, Local.toJudgement, Judgement.holds, dif_neg hn] using h
      exact congrArg Local.marker hm
  | predicate p =>
      simp only [Local.holds, Local.toJudgement, Judgement.holds, dif_neg hn] at h

theorem pruneTerminal_translationReady (T : Tableau Clock Var State)
    (h : T.TranslationReady) : T.pruneTerminal.TranslationReady where
  states_finite := h.states_finite.subset (fun _ hs => hs.1)
  variables_finite := h.variables_finite
  clocks_finite := h.clocks_finite
  edge_states := fun _ he => ⟨⟨(h.edge_states _ he.1).1, he.2.1⟩,
    ⟨(h.edge_states _ he.1).2, he.2.2.1⟩⟩
  initial_states := fun _ hi => ⟨h.initial_states _ hi.1, hi.2⟩
  final_states := fun _ hf => ⟨h.final_states hf.1, hf.2⟩
  edge_guards := fun _ he => h.edge_guards _ he.1
  initial_guards := fun _ hi => h.initial_guards _ hi.1
  edge_resets := fun _ he => h.edge_resets _ he.1
  initial_resets := fun _ hi => h.initial_resets _ hi.1
  atom_variables := fun _ hs => h.atom_variables _ hs.1

end Tableau

namespace Path

/-- Restriction only deletes states/edges: every retained path is an original
path, independently of signal satisfaction. -/
theorem valid_of_pruned (p : Path Clock State) (T : Tableau Clock Var State)
    (h : p.valid T.pruneTerminal) : p.valid T := by
  induction p with
  | last => exact h.1
  | step e s t ih => exact ⟨h.1.1, ih h.2.1, h.2.2.1⟩

theorem run_of_pruned (p : Path Clock State) (T : Tableau Clock Var State)
    (h : p.run T.pruneTerminal) : p.run T :=
  ⟨p.valid_of_pruned T h.1, h.2.1⟩

theorem accepting_of_pruned (p : Path Clock State) (T : Tableau Clock Var State)
    (h : p.accepting T.pruneTerminal) : p.accepting T :=
  ⟨p.valid_of_pruned T h.1, h.2.1⟩

theorem terminalCompatible_first_of_trace (p : Path Clock State)
    (T : Tableau Clock Var State) (hf : ∀ s, (T.label s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : (p.trace T.label hf).holds σ P α k) :
    T.TerminalCompatible p.firstState := by
  cases p with
  | last e s => exact T.terminalCompatible_of_holds s σ P _ k hs.2
  | step e s t => exact T.terminalCompatible_of_holds s σ P _ k hs.1.2

theorem valid_pruneTerminal_iff_of_trace (p : Path Clock State)
    (T : Tableau Clock Var State) (hf : ∀ s, (T.label s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : (p.trace T.label hf).holds σ P α k) :
    p.valid T.pruneTerminal ↔ p.valid T := by
  induction p generalizing α k with
  | last e s =>
      exact ⟨And.left, fun hv => ⟨hv, T.terminalCompatible_of_holds s σ P _ k hs.2⟩⟩
  | step e s t ih =>
      have hk : k.val < P.size := by
        by_contra hn
        have hh := hs.2
        simp only [dif_neg hn] at hh
      have ht : (t.trace T.label hf).holds σ P
          (ClockResetSet.elapse (e.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.val, hk⟩)) ⟨k.val + 1, by omega⟩ := by
        simpa only [Trace.holds, Trace.holdsWith, trace, dif_pos hk] using hs.2
      have hc := T.terminalCompatible_of_holds s σ P _ k hs.1.2
      have hc' := t.terminalCompatible_first_of_trace T hf σ P _ _ ht
      have hn : Local.terminal ∉ T.label s := by
        intro hm
        have he : k.val = P.size := hs.1.2 .terminal hm
        omega
      change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      exact ⟨fun h => ⟨h.1.1, (ih _ _ ht).mp h.2.1, h.2.2.1⟩,
        fun h => ⟨⟨h.1, hc⟩, (ih _ _ ht).mpr h.2.1, h.2.2, hc, hc', hn⟩⟩

theorem terminalCompatible_last_of_valid_pruned (p : Path Clock State)
    (T : Tableau Clock Var State) (h : p.valid T.pruneTerminal) :
    T.TerminalCompatible p.lastState := by
  induction p with
  | last => exact h.2
  | step e s t ih => exact ih h.2.1

end Path

namespace Tableau

/-- The very same path and partition witness recognition in both directions. -/
theorem pruneTerminal_recognizes_iff (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    T.pruneTerminal.recognizes hf σ P ↔ T.recognizes hf σ P := by
  constructor
  · rintro ⟨p, hr, ha, hs⟩
    have hv := (p.valid_pruneTerminal_iff_of_trace T hf σ P (fun _ => 0) _
      (hs (fun _ => 0))).mp hr.1
    exact ⟨p, ⟨hv, hr.2.1⟩, ⟨hv, ha.2.1⟩, hs⟩
  · rintro ⟨p, hr, ha, hs⟩
    have hv := (p.valid_pruneTerminal_iff_of_trace T hf σ P (fun _ => 0) _
      (hs (fun _ => 0))).mpr hr.1
    have hi := p.terminalCompatible_first_of_trace T hf σ P (fun _ => 0) _
      (hs (fun _ => 0))
    exact ⟨p, ⟨hv, hr.2, hi⟩,
      ⟨hv, ha.2, p.terminalCompatible_last_of_valid_pruned T hv⟩, hs⟩

/-- Explicit translation entry point for the language-preserving restriction. -/
def toPrunedAutomaton (T : Tableau Clock Var State) (h : T.TranslationReady)
    (τ : ℝ) (hτ : 0 < τ) :=
  T.pruneTerminal.toAutomaton (T.pruneTerminal_translationReady h) τ hτ

theorem pruned_terminal_labels (T : Tableau Clock Var State)
    (s : T.pruneTerminal.states) (ht : Local.terminal ∈ T.label s.val) :
    ∀ l ∈ T.label s.val, l = .terminal ∨ l = .marker ● :=
  s.property.2 ht

theorem terminal_predicate_not_mem_pruned (T : Tableau Clock Var State)
    (s : State) (p : Predicate Clock Var)
    (ht : Local.terminal ∈ T.label s) (hp : Local.predicate p ∈ T.label s) :
    s ∉ T.pruneTerminal.states := by
  intro hs
  rcases hs.2 ht (.predicate p) hp with h | h <;> cases h

theorem nonterminal_mem_pruned_iff (T : Tableau Clock Var State)
    (s : State) (ht : Local.terminal ∉ T.label s) :
    s ∈ T.pruneTerminal.states ↔ s ∈ T.states :=
  ⟨And.left, fun hs => ⟨hs, fun h => (ht h).elim⟩⟩

end Tableau
end STLTableau.Section4
