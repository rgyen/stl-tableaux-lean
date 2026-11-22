import STLTableaux.Automata.Recognition.NormalizedInputFinalLabelSemantics
import STLTableaux.Finiteness.Correctness.RootTraceClockIndependence

/-! A complete execution-to-recognition bridge for one positive flow and one
final jump. Marker and direct initial-entry conditions are explicit;
this is not yet the unrestricted translation-correctness theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

theorem inputTableau_recognizes_one_flow
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hcount : e.count = 1)
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hj : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨0, e.nonempty⟩) e.finalState)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hfinal : Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial) :
    ∃ P : IntervalPartition ρ.domain,
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  let T := inputTableau (Clock := Clock) X root
  let i : Fin e.count := ⟨0, e.nonempty⟩
  obtain ⟨l₀, hi, v, _, hr⟩ := hinit
  obtain ⟨l₁, hedge, hreal, _, _⟩ := (T.discreteStep_iff h _ _).mp hj
  have hmode := congrArg Subtype.val (e.continuousStep i).1
  have hedge' : ((e.start i).val.1.val, l₁, e.finalState.val.1.val) ∈ T.edges := by
    rw [hmode]
    exact hedge
  let p := Path.step l₀ (e.start i).val.1.val (Path.last l₁ e.finalState.val.1.val)
  have hvalid : p.valid T := ⟨(e.start i).val.1.property, e.finalState.val.1.property, hedge'⟩
  have hclosed := finiteRootTableau_trace_closed X root.val p ⟨hvalid, hi⟩
  let α : ClockValuation Clock := fun _ => 0
  have hg₀ : ∀ g ∈ l₀.guards, g.holds α := by
    intro g hg
    have hfree : g.clock ∈ (p.trace JudgementTableau.labels
        JudgementTableau.labels_finite).freeClocks := Or.inl ⟨g, hg, rfl⟩
    rw [hclosed] at hfree
    exact hfree.elim
  have hbound : ∀ g ∈ l₁.guards, g.clock ∈ l₀.resets.clocks := by
    intro g hg
    by_contra hn
    have hfree : g.clock ∈ (p.trace JudgementTableau.labels
        JudgementTableau.labels_finite).freeClocks :=
      Or.inr ⟨Or.inr (Or.inl ⟨g, hg, rfl⟩), hn⟩
    rw [hclosed] at hfree
    exact hfree.elim
  have hg₁ : ∀ g ∈ l₁.guards,
      g.holds (ClockResetSet.elapse (l₀.resets.apply α) (e.duration i)) := by
    intro g hg
    obtain ⟨a, ha⟩ := hbound g hg
    obtain ⟨hc, hcmp⟩ := hreal g hg
    have hf := ((e.continuousStep i).2.2.2 ⟨e.duration i, by simp⟩).1.1 ⟨g.clock, hc⟩
    rw [(e.continuousStep i).2.2.1] at hf
    have hs : (e.start i).val.2 (.inr (.inl ⟨g.clock, hc⟩)) = (a : ℝ) := by
      rw [hr]
      change (match l₀.resets.value g.clock with | some b => (b : ℝ) | none => _) = _
      rw [ha]
    have hv : (e.finish i).val.2 (.inr (.inl ⟨g.clock, hc⟩)) =
        ((ClockResetSet.elapse (l₀.resets.apply α) (e.duration i)) g.clock : ℝ) := by
      rw [hf, hs]
      simp [ClockResetSet.elapse, ClockResetSet.apply, ha]
      rfl
    rw [hv] at hcmp
    exact (Tableau.realComparison_coe _ _ _).mp hcmp
  let m : Fin (e.count + 1) → Marker := fun _ => ●
  let P : IntervalPartition ρ.domain :=
    { e.completedMarkedPointFlowPartition hearly m rfl rfl with
      covers := by
        rw [(e.completedMarkedPointFlowPartition hearly m rfl rfl).covers]
        change Set.Ico 0 σ.horizon = Set.Ico 0 ρ.horizon
        rw [hp.1] }
  have hsize : P.size = e.count + 2 := rfl
  have hzero : 0 < P.size := by omega
  have hone : 1 < P.size := by omega
  have hflow : ∀ β : ClockValuation Clock,
      ∀ l ∈ T.label (e.start i).val.1.val,
        l.holds ρ P β ⟨0, by omega⟩ := by
    intro β
    apply (inputTableau_flow_labels_iff_markers X root h e hp m rfl rfl i P
      ⟨0, by omega⟩ hzero
      (e.completedMarkedPointFlowPartition_old_piece hearly m rfl rfl i) β).mpr
    intro b hb
    cases b with
    | «open» => exact (hfirst hb).elim
    | closed => rfl
  have hpoint : P.interval ⟨1, hone⟩ =
      ⟨e.boundary ⟨e.count, by omega⟩, e.boundary ⟨e.count, by omega⟩, ●, ●⟩ := by
    have heidx : (⟨e.count, by omega⟩ : Fin P.size) = ⟨1, hone⟩ := Fin.ext hcount
    rw [← heidx]
    exact e.completedMarkedPointFlowPartition_stop hearly m rfl rfl
  have hlast : ∀ β : ClockValuation Clock,
      ∀ l ∈ T.label e.finalState.val.1.val, l.holds ρ P β ⟨1, by omega⟩ := by
    intro β
    exact (inputTableau_final_singleton_labels_iff X root h e hp hearly P
      ⟨1, by omega⟩ hone hpoint β).mpr hfinal
  have hd : STLTableau.Judgement.duration P ⟨0, hzero⟩ = e.duration i := by
    apply Subtype.ext
    exact e.completedMarkedPointFlowPartition_duration hearly m rfl rfl i
  refine ⟨P, finiteRootTableau_recognizes_of_one_trace X root.val p
    ⟨hvalid, hi⟩ ⟨hvalid, hgoal⟩ ρ P α ?_⟩
  refine ⟨⟨hg₀, hflow _⟩, ?_⟩
  simp only [dif_pos hzero]
  rw [hd]
  exact ⟨hg₁, hlast _⟩

end STLTableau.Section4.Finiteness
