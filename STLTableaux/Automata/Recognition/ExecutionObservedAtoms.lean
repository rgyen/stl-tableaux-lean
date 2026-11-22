import STLTableaux.Automata.Recognition.ExecutionObservedPath
import STLTableaux.Automata.Recognition.TraceClockSchedule

/-! Numeric atoms for each frame of the unchanged observed path. Absolute
frame bounds are computed from its actual residence times, not postulated.
The exceptional horizon point is outside the signal domain. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)

theorem ObservedPath.frame_atom {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite)
    {ρ : FiniteSignal Var} (hproj : T.ProjectsTo σ ρ)
    (i : Fin (p.trace T.label hf).length) (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ ((p.trace T.label hf).frameAt i).locals)
    (u : ρ.Time)
    (hu : u.val ∈ Set.Icc (l + residenceBoundary ds i.val)
      (l + residenceBoundary ds (i.val + 1))) :
    a.Holds (ρ.value u) := by
  induction hp with
  | @last incoming s l r d ho hd =>
    have hi : i.val = 0 := by have := i.isLt; simp [Path.trace, Trace.length] at *
    have hu' : u.val ∈ Set.Icc l r := by simpa [hi, residenceBoundary, hd] using hu
    rcases ho with ho | ⟨hl, _⟩
    · exact ho.closed_atom T h τ hτ e hproj a ha u hu'
    · have huLt : u.val < σ.horizon := lt_of_lt_of_eq u.property.2 hproj.1.symm
      rw [hl] at hu'
      exact (not_lt_of_ge hu'.1 huLt).elim
  | @step incoming s p l r z ds d ho hd hp ih =>
    revert ha hu
    refine Fin.cases ?_ (fun j => ?_) i
    · intro ha hu
      exact ho.closed_atom T h τ hτ e hproj a ha u
        (by simpa [residenceBoundary, hd] using hu)
    · intro ha hu
      apply ih j (by simpa [Path.trace, Trace.frameAt] using ha)
      simpa [residenceBoundary, hd, add_assoc] using hu

/-- Any assigned partition piece contained in the observed closed bounds
inherits the frame's numerical atoms. Endpoint ownership may vary. -/
theorem ObservedPath.frame_atom_on_partition {p l r ds}
    (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite)
    {ρ : FiniteSignal Var} (hproj : T.ProjectsTo σ ρ)
    (i : Fin (p.trace T.label hf).length)
    (P : IntervalPartition ρ.domain) (j : Fin P.size)
    (hsubset : (P.interval j).carrier ⊆
      Set.Icc (l + residenceBoundary ds i.val) (l + residenceBoundary ds (i.val + 1)))
    (a : AtomicProposition Var)
    (ha : Section3.Local.predicate (.plain (.atom a)) ∈ ((p.trace T.label hf).frameAt i).locals)
    (u : ρ.Time) (hu : u.val ∈ (P.interval j).carrier) : a.Holds (ρ.value u) :=
  hp.frame_atom T h τ hτ e hf hproj i a ha u (hsubset hu)

end STLTableau.Section4.Tableau
