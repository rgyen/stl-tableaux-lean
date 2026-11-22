import STLTableaux.Automata.Execution.ObservedFlowChain

/-! Construct an execution prefix from observed flows and their discrete
connectors. The prefix ends at the last flow endpoint. -/
namespace STLTableau.HybridAutomaton
variable {Mode Label Var : Type*} {H : HybridAutomaton Mode Label Var}
variable {σ : FiniteSignal Var}

namespace PrelimExecution

theorem appendObservedFlow (e : H.PrelimExecution σ) (f : ObservedFlow H σ)
    (time : e.boundary ⟨e.count, by omega⟩ = f.beginTime)
    (jump : Relation.TransGen H.DiscreteStep e.finalState f.start)
    (horizon : f.endTime ≤ σ.horizon) :
    ∃ out : H.PrelimExecution σ,
      out.initialState = e.initialState ∧
      out.start ⟨0, out.nonempty⟩ = e.start ⟨0, e.nonempty⟩ ∧
      out.finalState = f.finish ∧ out.boundary ⟨out.count, by omega⟩ = f.endTime ∧
      (∀ s, e.VisitsState s → out.VisitsState s) ∧
      (∀ s, f.VisitsState s → out.VisitsState s) ∧
      (∀ s, Relation.ReflTransGen H.DiscreteStep e.finalState s →
        Relation.ReflTransGen H.DiscreteStep s f.start → out.VisitsState s) := by
  let bounds (j : Fin (e.count + 2)) := if hj : j.val ≤ e.count then
    e.boundary ⟨j.val, by omega⟩ else f.endTime
  have b_old (j : Fin (e.count + 2)) (hj : j.val ≤ e.count) :
      bounds j = e.boundary ⟨j.val, by omega⟩ := dif_pos hj
  have b_end (j : Fin (e.count + 2)) (hj : j.val = e.count + 1) :
      bounds j = f.endTime := dif_neg (by omega)
  have later : f.beginTime < f.endTime := by linarith [f.positive, f.duration_eq]
  have increasing : StrictMono bounds := by
    intro i j hij
    have hv : i.val < j.val := hij
    have hi : i.val ≤ e.count := by have := j.isLt; omega
    rw [b_old i hi]
    by_cases h : j.val ≤ e.count
    · rw [b_old j h]
      exact e.increasing hv
    · rw [b_end j (by have := j.isLt; omega)]
      exact (e.increasing.monotone
        (show (⟨i.val, by omega⟩ : Fin (e.count + 1)) ≤
          ⟨e.count, by omega⟩ from hi)).trans_lt
          (time ▸ later)
  let st (i : Fin (e.count + 1)) :=
    if hi : i.val < e.count then e.start ⟨i.val, hi⟩ else f.start
  let en (i : Fin (e.count + 1)) :=
    if hi : i.val < e.count then e.finish ⟨i.val, hi⟩ else f.finish
  let dur (i : Fin (e.count + 1)) :=
    if hi : i.val < e.count then e.duration ⟨i.val, hi⟩ else f.duration
  let curves (i : Fin (e.count + 1)) (t : Set.Icc (0 : ℝ) (dur i)) : Var → ℝ :=
    if hi : i.val < e.count then
      e.curve ⟨i.val, hi⟩ ⟨t.val, t.property.1, by simpa [dur, hi] using t.property.2⟩
    else f.curve ⟨t.val, t.property.1, by simpa [dur, hi] using t.property.2⟩
  have dr (i : Fin (e.count + 1)) : (dur i : ℝ) = bounds i.succ - bounds i.castSucc := by
    by_cases hi : i.val < e.count
    · simpa [dur, bounds, hi, show i.val + 1 ≤ e.count by omega, hi.le] using
        e.duration_eq ⟨i.val, hi⟩
    · have he : i.val = e.count := by have := i.isLt; omega
      rw [b_end _ (show i.val + 1 = e.count + 1 by omega),
        b_old _ (show i.val ≤ e.count by omega)]
      have hh : (⟨i.val, by omega⟩ : Fin (e.count + 1)) = ⟨e.count, by omega⟩ := Fin.ext he
      simpa [dur, hi, hh, time] using f.duration_eq
  have cont (i : Fin (e.count + 1)) : H.ContinuousStep (st i) (en i) (dur i) (curves i) := by
    by_cases hi : i.val < e.count
    · simpa [HybridAutomaton.ContinuousStep, st, en, dur, curves, hi] using
        e.continuousStep ⟨i.val, hi⟩
    · simpa [HybridAutomaton.ContinuousStep, st, en, dur, curves, hi] using f.step
  let out : H.PrelimExecution σ := {
    count := e.count + 1
    nonempty := by omega
    initialState := e.initialState
    initial_mem := e.initial_mem
    start := st
    finish := en
    boundary := bounds
    first_zero := by simpa [bounds] using e.first_zero
    increasing := increasing
    last_le_horizon := by rw [b_end _ rfl]; exact horizon
    duration := dur
    duration_eq := dr
    curve := curves
    continuousStep := cont
    initialSteps := by simpa [st, e.nonempty] using e.initialSteps
    discreteSteps := by
      intro i hn
      have hi : i.val < e.count := by omega
      by_cases hn' : i.val + 1 < e.count
      · simpa [en, st, hi, hn'] using e.discreteSteps ⟨i.val, hi⟩ hn'
      · have he : (⟨i.val, hi⟩ : Fin e.count) = e.lastIndex := by
          apply Fin.ext
          change i.val = e.count - 1
          omega
        simpa [en, st, hi, hn', he, finalState] using jump
    signal_eq := by
      intro i t ht
      by_cases hi : i.val < e.count
      · have hl := b_old i.castSucc (show i.val ≤ e.count by omega)
        have hr := b_old i.succ (show i.val + 1 ≤ e.count by omega)
        rw [e.signal_eq ⟨i.val, hi⟩ t ⟨hl ▸ ht.1, hr ▸ ht.2⟩]
        simp only [curves, dif_pos hi]
        apply congrArg (e.curve _)
        exact Subtype.ext (congrArg (t.val - ·) hl.symm)
      · have he : i.val = e.count := by have := i.isLt; omega
        have hl : bounds i.castSucc = f.beginTime := by
          rw [b_old _ (show i.val ≤ e.count by omega)]
          exact (congrArg e.boundary (Fin.ext he)).trans time
        have hr := b_end i.succ (show i.val + 1 = e.count + 1 by omega)
        rw [f.observe t ⟨hl ▸ ht.1, hr ▸ ht.2⟩]
        simp only [curves, dif_neg hi]
        exact congrArg f.curve (Subtype.ext (congrArg (t.val - ·) hl.symm)) }
  have first : out.start ⟨0, out.nonempty⟩ = e.start ⟨0, e.nonempty⟩ := by
    change st _ = _
    simp [st, e.nonempty]
  have last : out.finalState = f.finish := by
    change en _ = _
    simp [en, lastIndex, out]
  refine ⟨out, rfl, first, last, b_end _ rfl, ?_, ?_, ?_⟩
  · intro s visit
    rcases visit with ⟨i, t, hs⟩ | ⟨before, after⟩ | ⟨i, hi, before, after⟩
    · let j : Fin out.count := ⟨i.val, by change i.val < e.count + 1; omega⟩
      refine Or.inl ⟨j, ⟨t.val, t.property.1, ?_⟩, ?_⟩
      · change t.val ≤ dur j
        simpa [dur, j, i.isLt] using t.property.2
      · change s.val = ((st j).val.1, curves j _)
        simpa [st, curves, j, i.isLt] using hs
    · exact Or.inr (Or.inl ⟨before, first.symm ▸ after⟩)
    · let j : Fin out.count := ⟨i.val, by change i.val < e.count + 1; omega⟩
      refine Or.inr (Or.inr ⟨j, by change i.val + 1 < e.count + 1; omega, ?_, ?_⟩)
      · change Relation.ReflTransGen H.DiscreteStep (en j) s
        simpa [en, j, i.isLt] using before
      · change Relation.ReflTransGen H.DiscreteStep s (st _)
        simpa [st, j, hi] using after
  · intro s visit
    obtain ⟨t, ht⟩ := visit
    let j : Fin out.count := ⟨e.count, by change e.count < e.count + 1; omega⟩
    refine Or.inl ⟨j, ⟨t.val, t.property.1, ?_⟩, ?_⟩
    · change t.val ≤ dur j
      simpa [dur, j] using t.property.2
    · change s.val = ((st j).val.1, curves j _)
      simpa [st, curves, j] using ht
  · intro s before after
    let j : Fin out.count := ⟨e.count - 1, by change e.count - 1 < e.count + 1; omega⟩
    have hj : e.count - 1 < e.count := by have := e.nonempty; omega
    have next : e.count - 1 + 1 = e.count := by have := e.nonempty; omega
    refine Or.inr (Or.inr ⟨j, by change e.count - 1 + 1 < e.count + 1; omega, ?_, ?_⟩)
    · change Relation.ReflTransGen H.DiscreteStep (en j) s
      simpa [en, j, hj, finalState, lastIndex] using before
    · change Relation.ReflTransGen H.DiscreteStep s (st _)
      simpa [st, j, next] using after

end PrelimExecution

namespace ObservedFlowChain
variable {a b : H.State} {t u : ℝ}

theorem toExecution
    (p : ObservedFlowChain H σ (Relation.TransGen H.DiscreteStep) a t b u)
    (initial : H.State) (hi : initial.val ∈ H.initial)
    (zero : t = 0)
    (first : Relation.ReflTransGen H.DiscreteStep initial a) (horizon : u ≤ σ.horizon) :
    ∃ e : H.PrelimExecution σ,
      e.initialState = initial ∧ e.start ⟨0, e.nonempty⟩ = a ∧
      e.finalState = b ∧ e.boundary ⟨e.count, by omega⟩ = u ∧
      ∀ s, p.VisitsState s → e.VisitsState s := by
  induction p with
  | single f =>
    let e : H.PrelimExecution σ := {
      count := 1
      nonempty := by decide
      initialState := initial
      initial_mem := hi
      start := fun _ => f.start
      finish := fun _ => f.finish
      boundary := fun i => if i.val = 0 then f.beginTime else f.endTime
      first_zero := zero
      increasing := by
        intro i j hij
        have later : f.beginTime < f.endTime := by linarith [f.positive, f.duration_eq]
        fin_cases i <;> fin_cases j <;> simp_all
      last_le_horizon := horizon
      duration := fun _ => f.duration
      duration_eq := by intro i; fin_cases i; exact f.duration_eq
      curve := fun _ => f.curve
      continuousStep := fun _ => f.step
      initialSteps := first
      discreteSteps := by intro i hn; exact False.elim (by omega)
      signal_eq := by intro i s hs; fin_cases i; exact f.observe s hs }
    refine ⟨e, rfl, rfl, rfl, rfl, ?_⟩
    intro s visit
    obtain ⟨r, hr⟩ := visit
    exact Or.inl ⟨0, r, hr⟩
  | @snoc a b t u p f time step ih =>
    have oldHorizon : u ≤ σ.horizon := by
      have later : f.beginTime < f.endTime := by linarith [f.positive, f.duration_eq]
      exact (time.trans_le later.le).trans horizon
    obtain ⟨e, ei, ef, el, et, preserve⟩ := ih zero first oldHorizon
    obtain ⟨out, oi, of, ol, ot, old, new, middle⟩ := e.appendObservedFlow f
      (et.trans time) (by simpa only [el] using step) horizon
    refine ⟨out, oi.trans ei, of.trans ef, ol, ot, ?_⟩
    intro s visit
    rcases visit with pre | ⟨before, after⟩ | flow
    · exact old s (preserve s pre)
    · exact middle s (by simpa only [el, ObservedFlowChain.finish] using before) after
    · exact new s flow

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``PrelimExecution.appendObservedFlow, ``toExecution] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end ObservedFlowChain
end STLTableau.HybridAutomaton
