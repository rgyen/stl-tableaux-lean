import STLTableaux.Automata.Recognition.ForwardHorizon
import STLTableaux.Automata.Recognition.ForwardTableauEntry
import STLTableaux.Automata.Execution.FlowSignalContinuity
import STLTableaux.Semantics.Partitions.PartitionDurationAlignment
import STLTableaux.Automata.Translation.EndPositionTranslation

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

private theorem piece_domain (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) {x : ℝ} (hx : x ∈ P.interval i) : x ∈ σ.domain := by
  rw [← P.covers]
  exact Set.mem_iUnion.mpr ⟨i,hx⟩

/-- The left endpoint is always in signal time, even when the piece excludes it. -/
def pieceEntry (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size) :
    σ.Time := by
  refine ⟨(P.interval i).left,?_⟩
  obtain ⟨x,hx⟩ := P.nonempty i
  have hxD := piece_domain σ P i hx
  refine ⟨?_,(MarkedInterval.left_le_of_mem hx).trans_lt hxD.2⟩
  by_contra! h
  obtain ⟨y,hly,hy⟩ := exists_between h
  have hyr := (hy.trans_le hxD.1).trans_le (MarkedInterval.le_right_of_mem hx)
  exact (not_lt_of_ge (piece_domain σ P i ⟨Or.inl hly,Or.inl hyr⟩).1) hy

private theorem pieceEntry_val (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) : (pieceEntry σ P i).val = (P.interval i).left := rfl

def pieceTime (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (u : Set.Ico (0 : ℝ) (STLTableau.Judgement.duration P i)) : σ.Time := by
  refine ⟨(P.interval i).left + u.val,?_,?_⟩
  · have hl := (pieceEntry σ P i).property.1
    rw [pieceEntry_val] at hl
    linarith [u.property.1]
  · have hright := P.right_le_domain_right i
    have hd : (STLTableau.Judgement.duration P i : ℝ) = (P.interval i).right -
        (P.interval i).left := rfl
    linarith [u.property.2]

/-- The final flow sample: use the true signal endpoint when this
visit owns it; otherwise the already valid entry sample suffices. -/
def flowSample (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size) :
    σ.Time := by
  classical
  exact if hc : (P.interval i).rightBoundary.Includes then
    ⟨(P.interval i).right,piece_domain σ P i ((P.interval i).right_mem (P.nonempty i) hc)⟩
  else pieceEntry σ P i

theorem flowSample_owned (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (hc : (P.interval i).rightBoundary.Includes) : (flowSample σ P i).val = (P.interval i).right := by
  simp [flowSample,hc]

private theorem piece_atom (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val,by omega⟩)
    (a : AtomicProposition Var) (ha : Local.predicate (.plain (.atom a)) ∈ T.label q.val) :
    ∀ t : σ.Time, t.val ∈ P.interval i → a.Holds (σ.value t) := by
  simpa only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos i.isLt,
    Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] using labels _ ha

theorem piece_entry_atoms (σ : FiniteSignal Var) (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (i : Fin P.size) (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val,by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.Holds (σ.value (pieceEntry σ P i)) := by
  intro a ha
  exact signalAtomRightContinuous_partition_entry σ φ hw a (input a ha).1 (input a ha).2 _ (P.nonempty i)
    _ (pieceEntry_val σ P i) (T.piece_atom σ P i q β labels a ha)

/-- A piece that owns its left endpoint needs no regularity assumption
at all. In particular this handles the initial singleton directly. -/
theorem piece_entry_atoms_of_closed (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (i : Fin P.size) (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (closed : (P.interval i).leftBoundary.Includes) :
    ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.Holds (σ.value (pieceEntry σ P i)) := by
  intro a ha
  apply T.piece_atom σ P i q β labels a ha
  rw [pieceEntry_val]
  exact (P.interval i).left_mem (P.nonempty i) closed

/-- Observed entries use the containing flow's regularity, rather
than assuming right continuity of the whole signal. -/
theorem piece_entry_atoms_of_flow {Mode Label : Type*}
    {H : HybridAutomaton Mode Label Var} {σ : FiniteSignal Var}
    (e : H.PrelimExecution σ) (φ : Formula Var) (hw : e.WellBehaved φ)
    (P : IntervalPartition σ.domain) (i : Fin P.size) (q : T.states) (β : ClockValuation Clock)
    (observed : (P.interval i).left < e.boundary ⟨e.count, by omega⟩)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val, by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.Holds (σ.value (pieceEntry σ P i)) := by
  intro a ha
  exact atom_at_partition_entry σ a (input a ha).1 _ (P.nonempty i)
    (pieceEntry σ P i) rfl
    (hw.atom_continuousWithinAt a (input a ha).2 _ observed)
    (T.piece_atom σ P i q β labels a ha)

theorem piece_entry_markers (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val,by omega⟩) :
    ∀ m, Local.marker m ∈ T.label q.val → m = (P.interval i).leftBoundary := by
  intro m hm
  symm
  simpa only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos i.isLt]
    using labels _ hm

/-- The entry valuation satisfies the invariant for any type-labelled piece,
including a singleton. -/
theorem entry_invariant_of_piece (h : T.TranslationReady) (σ : FiniteSignal Var) (φ : Formula Var)
    (hw : SignalAtomRightContinuous σ φ) (P : IntervalPartition σ.domain) (i : Fin P.size) (q : T.states)
    (β α : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val,by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i)) (P.interval i).leftBoundary)
      ∈ (T.typedAutomaton h σ.horizon).invariant := by
  let m := (P.interval i).leftBoundary
  refine ⟨?_,?_,?_,?_⟩
  · cases hm : (P.interval i).leftBoundary
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro _
    change (P.interval i).left ≤ σ.horizon
    exact (pieceEntry σ P i).property.2.le
  · intro a ha
    apply (T.atomHolds_iff a _ (σ.value (pieceEntry σ P i))
      (h.atom_variables _ q.property a ha) (fun _ => rfl)).2
    exact T.piece_entry_atoms σ φ hw P i q β labels input a ha
  · intro n hn
    have hm := T.piece_entry_markers σ P i q β labels n hn
    cases he : (P.interval i).leftBoundary <;> rw [hm,he]
    · change Marker.open = ● ↔ (0:ℝ) = 1
      simp
    · exact iff_of_true rfl rfl

theorem positive_flow_of_piece (h : T.TranslationReady) (σ : FiniteSignal Var) (φ : Formula Var)
    (hw : SignalAtomRightContinuous σ φ) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (q : T.states) (β : ClockValuation Clock)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P β ⟨i.val,by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (hr : 0 < STLTableau.Judgement.duration P i)
    (s : (T.typedAutomaton h σ.horizon).State) (α : ClockValuation Clock)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary)) :
    let r := STLTableau.Judgement.duration P i
    ∃ (s' : (T.typedAutomaton h σ.horizon).State)
      (γ : Set.Icc (0 : ℝ) r → T.TypedVar → ℝ),
      (T.typedAutomaton h σ.horizon).ContinuousStep s s' r γ ∧
      (∀ (u : Set.Icc (0 : ℝ) r) (hu : u.val < (r : ℝ)) (x : T.realVariables),
        γ u (.inl (.inl x)) = σ.value (pieceTime σ P i ⟨u.val,u.property.1,hu⟩) x.val) ∧
      (∀ x : T.realVariables, s'.val.2 (.inl (.inl x)) =
        σ.value (flowSample σ P i) x.val) := by
  let r := STLTableau.Judgement.duration P i
  let x (u : Set.Ico (0 : ℝ) r) (v : T.realVariables) := σ.value (pieceTime σ P i u) v.val
  let w (v : T.realVariables) := σ.value (flowSample σ P i) v.val
  have hr' : (r : ℝ) = (P.interval i).right - (P.interval i).left := rfl
  have entryAtoms := T.piece_entry_atoms σ φ hw P i q β labels input
  apply T.forward_positive_flow h σ.horizon s r hr x w
  · funext v
    rw [entry]
    change σ.value (pieceTime σ P i ⟨0,le_rfl,hr⟩) v.val =
      σ.value (pieceEntry σ P i) v.val
    have he : pieceTime σ P i ⟨0,le_rfl,hr⟩ = pieceEntry σ P i := by
      apply Subtype.ext
      rw [pieceEntry_val]
      exact add_zero _
    rw [he]
  · intro u a ha
    rw [entry] at ha
    apply (T.atomHolds_iff a _ _ (h.atom_variables _ q.property a ha)
      (fun _ => rfl (α := ℝ))).2
    change a.Holds (σ.value (pieceTime σ P i u))
    by_cases he : u.val = 0
    · have heq : pieceTime σ P i u = pieceEntry σ P i := by
        apply Subtype.ext
        rw [pieceEntry_val]
        change (P.interval i).left + u.val = _
        rw [he,add_zero]
      rw [heq]
      exact entryAtoms a ha
    · apply T.piece_atom σ P i q β labels a ha
      change (P.interval i).left + u.val ∈ P.interval i
      exact ⟨Or.inl (by linarith [lt_of_le_of_ne u.property.1 (Ne.symm he)]),
        Or.inl (by linarith [u.property.2])⟩
  · intro a ha
    rw [entry] at ha
    apply (T.atomHolds_iff a _ _ (h.atom_variables _ q.property a ha)
      (fun _ => rfl (α := ℝ))).2
    change a.Holds (σ.value (flowSample σ P i))
    by_cases hc : (P.interval i).rightBoundary.Includes
    · apply T.piece_atom σ P i q β labels a ha
      rw [flowSample_owned σ P i hc]
      exact (P.interval i).right_mem (P.nonempty i) hc
    · simpa [flowSample,hc] using entryAtoms a ha
  · intro _
    rw [entry]
    change (P.interval i).left + (r : ℝ) ≤ σ.horizon
    linarith [P.right_le_domain_right i]

/-- End state equations used by the following jump hold for every
positive residence built by the preceding theorem, regardless of the
chosen real sample at an unowned endpoint. -/
theorem flow_end_registers (h : T.TranslationReady) (τ : ℝ)
    (s b : (T.typedAutomaton h τ).State) (r : NNReal)
    (γ : Set.Icc (0 : ℝ) r → T.TypedVar → ℝ)
    (hc : (T.typedAutomaton h τ).ContinuousStep s b r γ) :
    s.val.1 = b.val.1 ∧
    (∀ c : T.clocks, b.val.2 (.inl (.inr (.inl c))) = s.val.2 (.inl (.inr (.inl c))) + r) ∧
    b.val.2 (.inl T.globalClock) = s.val.2 (.inl T.globalClock) + r ∧
    b.val.2 T.dwell = s.val.2 T.dwell + r ∧ b.val.2 T.bit = s.val.2 T.bit := by
  have he := ((hc.2.2.2 ⟨r,by simp⟩).1)
  rw [hc.2.2.1] at he
  exact ⟨hc.1,he⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in #[``entry_invariant_of_piece,``positive_flow_of_piece,``flow_end_registers] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.Section4.Tableau

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State) (h : T.TranslationReady)

/-- Positive pieces carry an actual curve observing the given signal and
the endpoint sample. A singleton contributes no flow arrow. -/
def PieceEvolution (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (i : Fin P.size)
    (s b : (T.endPositionAutomaton h σ.horizon).State) : Prop :=
  let r := STLTableau.Judgement.duration P i
  (r = 0 ∧ b = s) ∨
  (0 < r ∧ ∃ γ : Set.Icc (0 : ℝ) r → T.TypedVar → ℝ,
    (T.endPositionAutomaton h σ.horizon).ContinuousStep s b r γ ∧
    (∀ (u : Set.Icc (0 : ℝ) r) (hu : u.val < (r : ℝ)) (x : T.realVariables),
      γ u (.inl (.inl x)) = σ.value (pieceTime σ P i ⟨u.val,u.property.1,hu⟩) x.val) ∧
    ∀ x : T.realVariables, b.val.2 (.inl (.inl x)) = σ.value (flowSample σ P i) x.val)

theorem exists_piece_exit (σ : FiniteSignal Var) (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (i : Fin P.size) (q : T.states) (α : ClockValuation Clock)
    (s : (T.endPositionAutomaton h σ.horizon).State)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary))
    (labels : ∀ l ∈ T.label q.val, l.holds σ P α ⟨i.val,by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    ∃ b, T.PieceEvolution h σ P i s b := by
  by_cases he : STLTableau.Judgement.duration P i = 0
  · exact ⟨s,Or.inl ⟨he,rfl⟩⟩
  · have hp : 0 < STLTableau.Judgement.duration P i := pos_iff_ne_zero.mpr he
    obtain ⟨b,γ,hγ,hx,hw⟩ := T.positive_flow_of_piece h σ φ hw P i q α labels input hp s α entry
    exact ⟨b,Or.inr ⟨hp,γ,hγ,hx,hw⟩⟩

theorem PieceEvolution.registers (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) {s b : (T.endPositionAutomaton h σ.horizon).State}
    (move : T.PieceEvolution h σ P i s b) :
    let r := STLTableau.Judgement.duration P i
    s.val.1 = b.val.1 ∧
    (∀ c : T.clocks, b.val.2 (.inl (.inr (.inl c))) = s.val.2 (.inl (.inr (.inl c))) + r) ∧
    b.val.2 (.inl T.globalClock) = s.val.2 (.inl T.globalClock) + r ∧
    b.val.2 T.dwell = s.val.2 T.dwell + r ∧ b.val.2 T.bit = s.val.2 T.bit := by
  rcases move with ⟨hz,rfl⟩ | ⟨_,γ,hγ,_,_⟩
  · simp [hz]
  · exact T.flow_end_registers h σ.horizon s b _ γ hγ

theorem partition_singleton_markers (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) (hz : (STLTableau.Judgement.duration P i : ℝ) = 0) :
    (P.interval i).leftBoundary = ● ∧ (P.interval i).rightBoundary = ● := by
  change (P.interval i).right - (P.interval i).left = 0 at hz
  obtain ⟨x,hx⟩ := P.nonempty i
  have hxl := MarkedInterval.left_le_of_mem hx
  have hxr := MarkedInterval.le_right_of_mem hx
  have hl := hx.1.resolve_left (by linarith)
  have hr := hx.2.resolve_left (by linarith)
  constructor
  · cases hm : (P.interval i).leftBoundary <;> simp_all [Marker.Includes]
  · cases hm : (P.interval i).rightBoundary <;> simp_all [Marker.Includes]

/-- Realize the original edge from one actual partition piece to its
successor, with the same checked guard and reset. Endpoints, type bits,
auxiliary registers, zero-dwell polarity and post-atoms are all derived. -/
theorem jump_after_piece (σ : FiniteSignal Var) (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (i j : Fin P.size) (adj : i.val+1 = j.val)
    (q q' : T.states) (edgeLabel : EdgeLabel Clock) (edge : (q.val,edgeLabel,q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (s b : (T.endPositionAutomaton h σ.horizon).State)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary))
    (move : T.PieceEvolution h σ P i s b)
    (labels : ∀ l ∈ T.label q.val, l.holds σ P α ⟨i.val,by omega⟩)
    (guards : ∀ g ∈ edgeLabel.guards, g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
    (labels' : ∀ l ∈ T.label q'.val, l.holds σ P
      (edgeLabel.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
      ⟨j.val,by omega⟩)
    (input' : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    let β := edgeLabel.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    ∃ s' : (T.endPositionAutomaton h σ.horizon).State,
      s'.val = (q',T.entryValue (P.interval j).left β (σ.value (pieceEntry σ P j))
        (P.interval j).leftBoundary) ∧
      (T.endPositionAutomaton h σ.horizon).DiscreteStep b s' := by
  obtain ⟨hm,hrc,hgc,hd,hbit⟩ := move.registers T h σ P i
  rw [entry] at hm hrc hgc hd hbit
  have hh : i.val+1 < P.size := adj ▸ j.isLt
  have ij : (⟨i.val+1,hh⟩ : Fin P.size) = j := Fin.ext adj
  have hjoint := P.adjacent_right_eq_left i hh
  have hright := P.adjacent_rightBoundary_eq_complement_leftBoundary i hh
  rw [ij] at hjoint hright
  have tb : b.val.2 (.inl T.globalClock) = (P.interval j).left := by
    change b.val.2 (.inl T.globalClock) =
      (P.interval i).left + ((P.interval i).right - (P.interval i).left) at hgc
    linarith
  have hn : q' ∉ T.terminalModes := by
    intro ht
    have eq : j.val = P.size := labels' .terminal ht
    omega
  have hlt : (P.interval j).left < σ.horizon := (pieceEntry σ P j).property.2
  have hedge : (b.val.1.val,edgeLabel,q'.val) ∈ T.edges := hm ▸ edge
  obtain ⟨s',hst,hjump⟩ := T.forward_jump_entry h σ.horizon b q' edgeLabel hedge
    (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    (fun c => hrc c) guards (σ.value (pieceEntry σ P j)) (P.interval j).leftBoundary
    (iff_of_false hn (by rw [tb]; exact not_le_of_gt hlt)) (by
      intro hzero
      have hz : (STLTableau.Judgement.duration P i : ℝ) = 0 := by
        change b.val.2 T.dwell = 0 + _ at hd
        linarith
      obtain ⟨hs,hr⟩ := partition_singleton_markers σ P i hz
      constructor
      · rw [hbit,hs]
        rfl
      · cases hj : (P.interval j).leftBoundary <;> simp_all)
    (T.piece_entry_atoms σ φ hw P j q' _ labels' input') (T.piece_entry_markers σ P j q' _ labels')
    (by
      intro hopen a ha
      rw [← hm] at ha
      have hb : (P.interval i).rightBoundary = ● := by simp [hright,hopen]
      have hold := labels (.predicate (.plain (.atom a))) ha
      simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos i.isLt,
        Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] at hold
      apply hold
      change (P.interval j).left ∈ P.interval i
      rw [← hjoint]
      exact (P.interval i).right_mem (P.nonempty i) (by simp [hb,Marker.Includes]))
  refine ⟨s',by simpa only [tb] using hst,?_⟩
  apply (T.step_before_iff h σ.horizon ?_).2 hjump
  rw [hst]
  change b.val.2 (.inl T.globalClock) < _
  rw [tb]
  exact hlt

/-- Combined flow/jump step with the precise valuation expected as the
input of the following visit. β from the guard is not guessed anew. -/
theorem ordinary_piece_transition (σ : FiniteSignal Var) (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (P : IntervalPartition σ.domain) (i j : Fin P.size) (adj : i.val+1 = j.val)
    (q q' : T.states) (l : EdgeLabel Clock) (edge : (q.val,l,q'.val) ∈ T.edges)
    (α : ClockValuation Clock) (s : (T.endPositionAutomaton h σ.horizon).State)
    (entry : s.val = (q,T.entryValue (P.interval i).left α (σ.value (pieceEntry σ P i))
      (P.interval i).leftBoundary))
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ P α ⟨i.val,by omega⟩)
    (input : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (guards : ∀ g ∈ l.guards, g.holds (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
    (labels' : ∀ loc ∈ T.label q'.val, loc.holds σ P
      (l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)))
      ⟨j.val,by omega⟩)
    (input' : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q'.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ) :
    let β := l.resets.apply (ClockResetSet.elapse α (STLTableau.Judgement.duration P i))
    ∃ b s' : (T.endPositionAutomaton h σ.horizon).State, T.PieceEvolution h σ P i s b ∧
      (T.endPositionAutomaton h σ.horizon).DiscreteStep b s' ∧
      s'.val = (q',T.entryValue (P.interval j).left β (σ.value (pieceEntry σ P j))
        (P.interval j).leftBoundary) := by
  obtain ⟨b,move⟩ := T.exists_piece_exit h σ φ hw P i q α s entry labels input
  obtain ⟨s',hv,hj⟩ := T.jump_after_piece h σ φ hw P i j adj q q' l edge α s b
    entry move labels guards labels' input'
  exact ⟨b,s',move,hj,hv⟩

/-- Initialization on the first partition interval supplies the first
entry state used by ordinary_piece_transition; the first marker is forced
closed by the partition, not supplied by a separate hypothesis. -/
theorem initial_piece (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hsize : 0 < P.size)
    (q : T.states) (l : EdgeLabel Clock) (init : (l,q.val) ∈ T.initial)
    (α : ClockValuation Clock) (guards : ∀ g ∈ l.guards, g.holds α)
    (labels : ∀ loc ∈ T.label q.val, loc.holds σ P (l.resets.apply α) ⟨0,by omega⟩) :
    let i : Fin P.size := ⟨0,hsize⟩
    ∃ s : (T.endPositionAutomaton h σ.horizon).State,
      s.val ∈ (T.endPositionAutomaton h σ.horizon).initial ∧
      s.val = (q,T.entryValue (P.interval i).left (l.resets.apply α)
        (σ.value (pieceEntry σ P i)) (P.interval i).leftBoundary) := by
  let i : Fin P.size := ⟨0,hsize⟩
  have hmk := T.piece_entry_markers σ P i q _ labels
  have hclosed := P.first_leftBoundary_closed hsize σ.horizon_pos
  have hat := T.piece_entry_atoms_of_closed σ P i q _ labels (by rw [hclosed]; trivial)
  obtain ⟨s,hi,hs⟩ := T.forward_initial_entry h σ.horizon σ.horizon_pos q l init
    α (σ.value (pieceEntry σ P i)) guards hat (fun m hm => (hmk m hm).trans hclosed)
  exact ⟨s,hi,by simpa only [P.first_left_eq_domain_left hsize σ.horizon_pos,hclosed] using hs⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in #[``piece_entry_atoms_of_closed, ``piece_entry_atoms_of_flow,
      ``partition_singleton_markers, ``initial_piece, ``ordinary_piece_transition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.Section4.Tableau
