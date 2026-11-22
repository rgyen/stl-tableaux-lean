import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics
import STLTableaux.Automata.Recognition.ExecutionObservedAtoms
import STLTableaux.Automata.Recognition.PathFrameLabels
import STLTableaux.Automata.Recognition.ExecutionObservedEndpoint
import STLTableaux.Semantics.Partitions.PartitionDurationAlignment
import STLTableaux.Automata.Recognition.PrunedExecutionEndpoint
import STLTableaux.Automata.Recognition.ExecutionIntervalAssignment

/-! For ordinary positions of an observed trace, numerical atoms are derived
from the execution. Only positional label compatibility remains to be checked.
No partition existence or marker consistency is assumed implicitly. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var State : Type*}

theorem inputTableau_frame_normalizedReady [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (inputTableau (Clock := Clock) X root))
    (i : Fin (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length)
    (q : Local Clock Var)
    (hq : q ∈ ((p.trace JudgementTableau.labels JudgementTableau.labels_finite).frameAt i).locals) :
    q.NormalizedReady := by
  apply p.frameAt_locals_of_allStates (inputTableau X root)
    JudgementTableau.labels_finite {F | F.NormalizedReady}
    (inputTableau_run_normalizedReady X root p hr) Local.NormalizedReady _ i q hq
  intro s hs q hq
  exact hs.1 q hq.1

theorem observed_frame_labels_hold
    (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    {p l r ds} (hp : T.ObservedPath h τ hτ e p l r ds)
    (hf : ∀ s, (T.label s).Finite)
    {ρ : FiniteSignal Var} (hproj : T.ProjectsTo σ ρ)
    (i : Fin (p.trace T.label hf).length)
    (hready : ∀ q ∈ ((p.trace T.label hf).frameAt i).locals, q.NormalizedReady)
    (P : IntervalPartition ρ.domain) (j : Fin P.size)
    (hsubset : (P.interval j).carrier ⊆ Set.Icc
      (l + Tableau.residenceBoundary ds i.val) (l + Tableau.residenceBoundary ds (i.val + 1)))
    (hn : Local.terminal ∉ ((p.trace T.label hf).frameAt i).locals)
    (hm : ∀ m, Local.marker m ∈ ((p.trace T.label hf).frameAt i).locals →
      (P.interval j).leftBoundary = m) :
    ∀ (α : ClockValuation Clock) q, q ∈ ((p.trace T.label hf).frameAt i).locals →
      q.holds ρ P α ⟨j.val, by have := j.isLt; omega⟩ := by
  intro α q hq
  cases q with
  | terminal => exact (hn hq).elim
  | marker m =>
      simpa only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos j.isLt]
        using hm m hq
  | predicate q =>
      have ha := p.frameAt_locals_keepAtomic T hf i (.predicate q) hq
      rcases normalizedReady_atomic_cases (hready _ hq) ha with he | ⟨a, he⟩
      · subst q
        simp only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos j.isLt,
          Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies, implies_true]
      · subst q
        simp only [Local.holds, Local.toJudgement, Judgement.holds, dif_pos j.isLt,
          Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies]
        intro u hu
        exact hp.frame_atom_on_partition T h τ hτ e hf hproj i P j hsubset a hq u hu

/-- Before the horizon every observed frame is ordinary. This includes
zero-duration frames, using their actual discrete-chain observations. -/
theorem inputTableau_observed_frame_nonterminal
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p l r ds}
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p l r ds)
    (i : Fin (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length)
    (hi : l + Tableau.residenceBoundary ds i.val < σ.horizon) :
    Local.terminal ∉ ((p.trace JudgementTableau.labels
      JudgementTableau.labels_finite).frameAt i).locals := by
  induction hp with
  | @last incoming s l r d ho hd =>
      rcases ho with ho | ⟨hl, _⟩
      · exact pruned_execution_observed_nonterminal X root h e ho
      · simp [Tableau.residenceBoundary, hl] at hi
  | @step incoming s p l r z ds d ho hd hp ih =>
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        exact pruned_execution_observed_nonterminal X root h e ho
      · intro hi
        apply ih j
        simpa [Tableau.residenceBoundary, hd, add_assoc] using hi

/-- A final `*` frame is the horizon position, not a singleton interval to
append to the signal partition. Both its time and its zero dwell follow from
the actual observation evidence, including the exclusion of ordinary terminal
observations. No path state or edge is removed. -/
theorem inputTableau_observed_terminal_last
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p l r ds}
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p l r ds)
    (ht : Local.terminal ∈ (inputTableau X root).label p.lastState) :
    r = σ.horizon ∧ ds.getLast? = some 0 := by
  induction hp with
  | @last incoming s l r d ho hd =>
      rcases ho with ho | ⟨hl, hr, _⟩
      · exact (pruned_execution_observed_nonterminal X root h e ho ht).elim
      · have hd0 : d = 0 := by
          apply Subtype.ext
          change (d : ℝ) = 0
          linarith
        exact ⟨hr, by simp [hd0]⟩
  | @step incoming s p l r z ds d ho hd hp ih =>
      obtain ⟨hr, hlast⟩ := ih ht
      refine ⟨hr, ?_⟩
      rw [List.getLast?_cons, hlast]
      rfl

/-- The last ordinary duration before a terminal frame cannot be zero:
ordinary observations start strictly before the horizon. -/
theorem inputTableau_observed_terminal_prefix_last_ne_zero
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p l r ds}
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p l r ds)
    (ht : Local.terminal ∈ (inputTableau X root).label p.lastState) :
    ∀ i : Fin ds.dropLast.length,
      i.val + 1 = ds.dropLast.length → ds.dropLast[i.val] ≠ 0 := by
  induction hp with
  | last => intro i; exact Fin.elim0 i
  | @step incoming s p l r z ds d ho hd hp ih =>
    cases ds with
    | nil => cases hp
    | cons a rest =>
      cases rest with
      | nil =>
        obtain ⟨hz, ha⟩ := inputTableau_observed_terminal_last X root h e hp ht
        have ha0 : a = 0 := Option.some.inj ha
        have htime := hp.total_duration _ _ _ _ _
        have hr : r = σ.horizon := by simpa [ha0] using htime.symm.trans hz
        have hl := ho.left_lt_horizon _ _ _ _ _
        have hdpos : 0 < (d : ℝ) := by linarith
        intro i _ he
        have hi : i.val = 0 := by have := i.isLt; simp_all
        have hd0 : d = 0 := by simpa [hi] using he
        simp [hd0] at hdpos
      | cons b rest =>
        intro i hi
        rcases i with ⟨i, hil⟩
        cases i with
        | zero => simp at hi
        | succ j =>
          have hj : j < (a :: b :: rest).dropLast.length := by
            simpa only [List.dropLast_cons_cons, List.length_cons, Nat.succ_lt_succ_iff] using hil
          have hlast : j + 1 = (a :: b :: rest).dropLast.length := by
            simpa only [List.dropLast_cons_cons, List.length_cons, Nat.add_left_inj] using hi
          simpa only [List.dropLast_cons_cons, List.getElem_cons_succ] using
            ih ht ⟨j, hj⟩ hlast

/-- Separate only the terminal duration, not the final path state or edge.
The prefix still covers the whole time span; the trace has one more position
than this prefix has entries. This makes no assertion about interior zeros. -/
theorem inputTableau_observed_terminal_prefix
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p r ds}
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p 0 r ds)
    (ht : Local.terminal ∈ (inputTableau X root).label p.lastState) :
    ds = ds.dropLast ++ [0] ∧ (ds.dropLast.sum : ℝ) = σ.horizon ∧
      (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length =
        ds.dropLast.length + 1 := by
  obtain ⟨hr, hlast⟩ := inputTableau_observed_terminal_last X root h e hp ht
  have he : ds.dropLast ++ [0] = ds :=
    List.dropLast_append_getLast? 0 (by rw [hlast]; rfl)
  have hsum := hp.total_duration _ _ _ _ _
  rw [hr, ← he] at hsum
  have hc := hp.frame_count _ _ _ _ _ JudgementTableau.labels JudgementTableau.labels_finite
  refine ⟨he.symm, ?_, ?_⟩
  · simpa using hsum.symm
  · have hlen := congrArg List.length he
    simp only [List.length_append, List.length_singleton] at hlen
    omega

/-- Construct the full-domain partition from the ordinary residence prefix,
leaving the terminal frame at the extra position. Interior singleton geometry
is still explicit; this theorem does not infer label-marker agreement. -/
theorem inputTableau_observed_terminal_partition
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p r ds}
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p 0 r ds)
    (ht : Local.terminal ∈ (inputTableau X root).label p.lastState)
    (hisolated : ∀ (i : Fin ds.dropLast.length) (hi : i.val + 1 < ds.dropLast.length),
      ds.dropLast[i.val] = 0 → ds.dropLast[i.val + 1] ≠ 0) :
    ∃ P : IntervalPartition σ.domain, ∃ hsize : P.size = ds.dropLast.length,
      (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length = P.size + 1 ∧
      (∀ i : Fin ds.dropLast.length,
        (STLTableau.Judgement.duration P ⟨i.val, by omega⟩ : ℝ) =
          (ds.dropLast[i.val] : ℝ)) ∧
      ∀ i : Fin ds.dropLast.length,
        (P.interval ⟨i.val, by omega⟩).leftBoundary =
          IntervalPartition.singletonMarkers
            (fun j : Fin (ds.dropLast.length + 1) =>
              Tableau.residenceBoundary ds.dropLast j.val) ⟨i.val, by omega⟩ := by
  obtain ⟨_, hsum, hlength⟩ := inputTableau_observed_terminal_prefix X root h e hp ht
  have hlast := inputTableau_observed_terminal_prefix_last_ne_zero X root h e hp ht
  obtain ⟨P, hsize, hpieces⟩ :=
    Tableau.exists_assignedExecutionInterval_partition 0 ds.dropLast hisolated hlast
  have hcover : (⋃ i, (P.interval i).carrier) = σ.domain := by
    simpa only [zero_add, hsum, FiniteSignal.domain] using P.covers
  let Q : IntervalPartition σ.domain := { P with covers := hcover }
  refine ⟨Q, hsize, by simpa only [Q, hsize] using hlength, ?_, ?_⟩
  · intro i
    change (P.interval ⟨i.val, by omega⟩).right -
      (P.interval ⟨i.val, by omega⟩).left = _
    rw [hpieces i]
    exact Tableau.assignedExecutionInterval_duration 0 ds.dropLast i _
  · intro i
    change (P.interval ⟨i.val, by omega⟩).leftBoundary = _
    rw [hpieces i]
    simp only [Tableau.assignedExecutionInterval,
      Tableau.executionInterval_leftBoundary, zero_add]

/-- Numerical labels and terminal-position behavior follow from execution
observations. Duration alignment supplies containment for every nonlast frame;
only an early-stopping last ordinary frame's upper bound and marker agreement
remain. At the horizon the upper bound follows from partition coverage. -/
theorem inputTableau_observed_trace_labels
    [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toPrunedAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {p r ds} (hr : p.run (inputTableau X root))
    (hvalid : p.valid (inputTableau X root).pruneTerminal)
    (hp : (inputTableau X root).pruneTerminal.ObservedPath
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e p 0 r ds)
    {ρ : FiniteSignal Var} (hproj : (inputTableau X root).pruneTerminal.ProjectsTo σ ρ)
    (P : IntervalPartition ρ.domain)
    (hlen : (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length ≤ P.size + 1)
    (hd : ∀ (i : Fin ds.length) (hi : i.val + 1 < ds.length),
      (ds[i.val] : ℝ) = STLTableau.Judgement.duration P ⟨i.val, by
        have hc := hp.frame_count _ _ _ _ _ JudgementTableau.labels JudgementTableau.labels_finite
        have := i.isLt
        omega⟩) :
    let t := p.trace JudgementTableau.labels JudgementTableau.labels_finite
    ((ds.sum : ℝ) < ρ.horizon →
      ∀ (i : Fin t.length) (hi : i.val < P.size), i.val + 1 = t.length →
      (P.interval ⟨i.val, hi⟩).right ≤ (ds.sum : ℝ)) →
    (∀ (i : Fin t.length) (hi : i.val < P.size) m,
      Local.marker m ∈ (t.frameAt i).locals → (P.interval ⟨i.val, hi⟩).leftBoundary = m) →
    ∀ (i : Fin t.length) (β : ClockValuation Clock) q, q ∈ (t.frameAt i).locals →
      q.holds ρ P β ⟨i.val, by
        have hil : i.val < (p.trace JudgementTableau.labels JudgementTableau.labels_finite).length := i.isLt
        omega⟩ := by
  intro t hlast hm i β q hq
  have hc := hp.frame_count _ _ _ _ _ JudgementTableau.labels JudgementTableau.labels_finite
  have hsub (j : Fin t.length) (hj : j.val < P.size) :
      (P.interval ⟨j.val, hj⟩).carrier ⊆ Set.Icc
        (Tableau.residenceBoundary ds j.val) (Tableau.residenceBoundary ds (j.val + 1)) := by
    apply P.interval_subset_residenceBounds ρ ds
      (fun k _ hk => hd ⟨k, by omega⟩ hk) j.val hj (by
        have := j.isLt
        change ds.length = t.length at hc
        omega)
    intro he
    by_cases hearly : (ds.sum : ℝ) < ρ.horizon
    · exact hlast hearly j hj (he.trans hc)
    · exact (P.right_le_domain_right ⟨j.val, hj⟩).trans (le_of_not_gt hearly)
  by_cases hi : i.val < P.size
  · have hn : Local.terminal ∉ (t.frameAt i).locals := by
      apply inputTableau_observed_frame_nonterminal X root h e hp i
      obtain ⟨x, hx⟩ := P.nonempty ⟨i.val, hi⟩
      have hxd : x ∈ ρ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.mpr ⟨⟨i.val, hi⟩, hx⟩
      have hb := (hsub i hi hx).1
      have hlt : x < σ.horizon := hxd.2.trans_eq hproj.1.symm
      simpa only [zero_add] using hb.trans_lt hlt
    exact observed_frame_labels_hold (inputTableau X root).pruneTerminal
      ((inputTableau X root).pruneTerminal_translationReady h)
      σ.horizon σ.horizon_pos e hp JudgementTableau.labels_finite hproj i
      (inputTableau_frame_normalizedReady X root p hr i) P ⟨i.val, hi⟩
      (by simpa only [zero_add] using hsub i hi) hn (hm i hi) β q hq
  · have he : i.val = P.size := by
      have hlength : t.length ≤ P.size + 1 := hlen
      have := i.isLt
      omega
    have htime := P.residenceBoundary_eq_horizon ρ ds
      (by have := i.isLt; change i.val < t.length at this; change ds.length = t.length at hc; omega)
      (by
        intro j hj hj'
        exact hd ⟨j, by omega⟩ hj')
    have ht : Local.terminal ∈ (t.frameAt i).locals := by
      apply hp.frame_terminal_of_horizon_le _ _ _ _ _ JudgementTableau.labels_finite i
      simpa only [zero_add, he, htime, hproj.1] using (le_refl ρ.horizon)
    have hshape := p.pruned_frame_terminal_labels (inputTableau X root)
      JudgementTableau.labels_finite hvalid i ht q hq
    rcases hshape with rfl | rfl
    · exact he
    · simp only [Local.holds, Local.toJudgement, Judgement.holds, dif_neg hi]

end STLTableau.Section4.Finiteness
