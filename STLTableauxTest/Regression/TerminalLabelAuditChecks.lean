import STLTableaux.Automata.Recognition.TerminalLabelAudit

open STLTableau STLTableau.Section4

namespace TerminalNormalizationRegression
variable {Clock Var : Type*}

/-- A raw normalization diagnostic, NOT a reachable finite-root state or an
automaton language counterexample. The atom is within normalized input syntax. -/
def form (a : AtomicProposition Var) : Section3.TransitionForm Clock Var :=
  (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal .terminal)).union
    (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal (.predicate (.plain (.atom a)))))

theorem normalization_retains_conflict (a : AtomicProposition Var) :
    Section3.TransitionForm.normalize? (Clock := Clock)
      (.conj .terminal (.predicate (.plain (.atom a)))) = some (form a) := rfl

theorem retained_conflict_never_holds (a : AtomicProposition Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    ¬ (Trace.last (form (Clock := Clock) a).current).holds σ P α k := by
  apply Trace.not_holds_of_terminal_predicate _ ⟨0, by simp [Trace.length]⟩
    ?_ (.plain (.atom a)) ?_ σ P α k
  · simp [Trace.frameAt, form, Section3.TransitionForm.union, Section3.TransitionForm.ofState,
      Section3.StateForm.union, Section3.StateForm.ofLocal]
  · simp [Trace.frameAt, form, Section3.TransitionForm.union, Section3.TransitionForm.ofState,
      Section3.StateForm.union, Section3.StateForm.ofLocal]

end TerminalNormalizationRegression

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Trace.frame_locals_satisfiable, ``Trace.terminal_frame_compatible,
      ``Trace.not_holds_of_terminal_predicate, ``Trace.not_holds_of_terminal_open_marker,
      ``Trace.frame_markers_equal, ``TerminalNormalizationRegression.normalization_retains_conflict,
      ``TerminalNormalizationRegression.retained_conflict_never_holds] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
