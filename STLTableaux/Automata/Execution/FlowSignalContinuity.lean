import STLTableaux.Automata.Recognition.ForwardWellBehaved

/-! Flow-local regularity transfers at every observed time, including zero.
Whole-signal regularity requires a witness covering the horizon. -/
namespace STLTableau.HybridAutomaton.PrelimExecution
open STLTableau
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var} {e : H.PrelimExecution σ} {φ : Formula Var}

/-- Local metric transfer on one right-owned flow cell. -/
private theorem atom_continuousWithinAt_of_flow (hw : e.WellBehaved φ)
    (a : AtomicProposition Var) (sub : Formula.IsSubformula (.atom a) φ)
    (i : Fin e.count) (t : σ.Time)
    (lower : e.boundary i.castSucc ≤ t.val) (upper : t.val < e.boundary i.succ) :
    ContinuousWithinAt (atomValue σ a) (Set.Ici t) t := by
  have duration : (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc :=
    e.duration_eq i
  let u : Set.Icc (0 : ℝ) (e.duration i) :=
    ⟨t.val - e.boundary i.castSucc, by constructor <;> linarith⟩
  let f := fun z : Set.Icc (0 : ℝ) (e.duration i) =>
    a.function (fun k => e.curve i z (a.arguments k))
  have cont : ContinuousWithinAt f (Set.Ici u) u := hw i a sub u
  have teq : atomValue σ a t = f u := by
    unfold atomValue
    rw [e.signal_eq i t ⟨lower, upper⟩]
    rfl
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, close⟩ := Metric.continuousWithinAt_iff.mp cont ε hε
  refine ⟨min δ (e.boundary i.succ - t.val), lt_min hδ (sub_pos.mpr upper), ?_⟩
  intro s hs hdist
  have distance : |s.val - t.val| < min δ (e.boundary i.succ - t.val) := hdist
  have ts : t.val ≤ s.val := hs
  have su : s.val < e.boundary i.succ := by
    have bound := (lt_min_iff.mp distance).2
    rw [abs_of_nonneg (sub_nonneg.mpr ts)] at bound
    linarith
  have sl : e.boundary i.castSucc ≤ s.val := lower.trans ts
  let v : Set.Icc (0 : ℝ) (e.duration i) :=
    ⟨s.val - e.boundary i.castSucc, by constructor <;> linarith⟩
  have seq : atomValue σ a s = f v := by
    unfold atomValue
    rw [e.signal_eq i s ⟨sl, su⟩]
    rfl
  rw [teq, seq]
  apply close (show v ∈ Set.Ici u from sub_le_sub_right ts _)
  change dist (s.val - e.boundary i.castSucc) (t.val - e.boundary i.castSucc) < δ
  rw [dist_sub_right, Real.dist_eq]
  exact (lt_min_iff.mp distance).1

/-- At an actually observed time, use its containing evolution. -/
theorem WellBehaved.atom_continuousWithinAt (hw : e.WellBehaved φ)
    (a : AtomicProposition Var) (sub : Formula.IsSubformula (.atom a) φ)
    (t : σ.Time)
    (observed : t.val < e.boundary ⟨e.count, by omega⟩) :
    ContinuousWithinAt (atomValue σ a) (Set.Ici t) t := by
  have first : e.boundary 0 = 0 := e.first_zero
  have range : t.val ∈ Set.Ico (e.boundary 0) (e.boundary ⟨e.count, by omega⟩) :=
    ⟨by rw [first]; exact t.property.1, observed⟩
  obtain ⟨i, lower, upper⟩ := IntervalPartition.exists_boundary_piece e.boundary range
  exact atom_continuousWithinAt_of_flow hw a sub i t lower upper

/-- Full coverage discharges the observation bound at all signal times. -/
theorem WellBehaved.atom_continuousWithinAt_of_full (hw : e.WellBehaved φ)
    (full : e.ReachesHorizon) (a : AtomicProposition Var)
    (sub : Formula.IsSubformula (.atom a) φ) (t : σ.Time) :
    ContinuousWithinAt (atomValue σ a) (Set.Ici t) t :=
  hw.atom_continuousWithinAt a sub t (by rw [full]; exact t.property.2)

/-- A full flow-wise well-behaved execution supplies a right-continuous
atomic observation, even if a jump precedes its first flow. -/
theorem WellBehaved.signalAtomRightContinuous (hw : e.WellBehaved φ)
    (full : e.ReachesHorizon) :
    SignalAtomRightContinuous σ φ :=
  fun a sub t => hw.atom_continuousWithinAt_of_full full a sub t

run_elab do
  for n in #[``WellBehaved.atom_continuousWithinAt, ``WellBehaved.atom_continuousWithinAt_of_full,
      ``WellBehaved.signalAtomRightContinuous] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.HybridAutomaton.PrelimExecution
