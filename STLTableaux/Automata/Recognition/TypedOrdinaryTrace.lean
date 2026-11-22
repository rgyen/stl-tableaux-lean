import STLTableaux.Automata.Recognition.TypedGuardTiming
import STLTableaux.Automata.Recognition.TypedVisitAtoms
import STLTableaux.Automata.Recognition.VisitCutSuffix
import STLTableaux.Automata.Recognition.NormalizedInputLabelSemantics

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)
local notation "V" => TimedVisit T h τ

/-- Identify only original signal coordinates; jumps need not preserve them. -/
def TypedProjectsTo (σ : FiniteSignal T.TypedVar) (ρ : FiniteSignal Var) : Prop :=
  σ.horizon = ρ.horizon ∧ ∀ (t : σ.Time) (u : ρ.Time), t.val = u.val →
    ∀ x : T.realVariables, σ.value t (.inl (.inl x)) = ρ.value u x.val

/-- Projection needed by an ordinary cut: the augmented and original signals
agree on [0,cut). Even their horizons can differ after this cut. -/
def TypedProjectsThrough (σ : FiniteSignal T.TypedVar) (ρ : FiniteSignal Var) (cut : ℝ) : Prop :=
  cut ≤ ρ.horizon ∧ ∀ (t : σ.Time) (u : ρ.Time), t.val = u.val → u.val < cut →
    ∀ x : T.realVariables, σ.value t (.inl (.inl x)) = ρ.value u x.val

theorem TypedProjectsTo.through {σ : FiniteSignal T.TypedVar} {ρ : FiniteSignal Var}
    (hp : T.TypedProjectsTo σ ρ) {cut : ℝ} (hc : cut ≤ σ.horizon) :
    T.TypedProjectsThrough σ ρ cut :=
  ⟨hc.trans_eq hp.1,fun t u he _ => hp.2 t u he⟩

private theorem frame_modes (p : Path Clock State) (hf : ∀ s, (T.label s).Finite)
    (j : Fin (p.trace T.label hf).length) :
    ∃ hj : j.val < (visitModes p).length,
      ((p.trace T.label hf).frameAt j).locals = T.label (visitModes p)[j.val] := by
  induction p with
  | last =>
    have hz : j.val = 0 := by have := j.isLt; simp [Path.trace,Trace.length] at *
    refine ⟨by change j.val < 1; omega,?_⟩
    simp [Path.trace,Trace.frameAt,visitModes]
  | step l s p ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ⟨by simp [visitModes],rfl⟩
    · obtain ⟨hk,he⟩ := ih k
      exact ⟨Nat.succ_lt_succ hk,he⟩

private theorem visits_end_le {vs : List V} {t : ℝ} (ht : VisitTimes T h τ vs t) :
    ∀ v ∈ vs, v.right ≤ t := by
  induction ht with
  | nil => simp
  | snoc pre s hab ih =>
    intro v hv
    rcases List.mem_append.mp hv with old | new
    · exact (ih v old).trans hab
    · simp only [List.mem_singleton] at new
      subst v
      exact le_rfl

/-- Extend the partition of the observed prefix by appending the suffix
from the cut to the horizon when the cut is early. -/
private theorem complete_prefix (ρ : FiniteSignal Var) {cut : ℝ}
    (hl : 0 ≤ cut) (hc : cut ≤ ρ.horizon) (Q : IntervalPartition (Set.Ico 0 cut))
    (hend : ∀ j, (Q.interval j).right ≤ cut) :
    ∃ (P : IntervalPartition ρ.domain) (hn : Q.size ≤ P.size),
      (∀ j : Fin Q.size, P.interval ⟨j.val,j.isLt.trans_le hn⟩ = Q.interval j) ∧
      (cut < ρ.horizon → ∃ hj : Q.size < P.size, P.size = Q.size+1 ∧
        P.interval ⟨Q.size,hj⟩ = ⟨cut,ρ.horizon,●,○⟩) := by
  rcases lt_or_eq_of_le hc with he | rfl
  · exact ⟨Q.appendCutSuffix hl he hend,Nat.le_succ _,fun j =>
      Q.appendCutSuffix_old hl he hend j,fun _ =>
      ⟨Nat.lt_succ_self _,rfl,Q.appendCutSuffix_last hl he hend⟩⟩
  · exact ⟨Q,le_rfl,fun _ => rfl,fun he => (he.false).elim⟩

/-- The geometric part of the induced-partition definition for an
ordinary cut. Complementary right markers follow from being a partition
of a half-open interval. No trace, labels or guards occur in this predicate. -/
structure CutLayout (ρ : FiniteSignal Var) (vs : List V) (cut : ℝ)
    (P : IntervalPartition ρ.domain) : Prop where
  count : vs.length ≤ P.size
  pieces : ∀ j : Fin vs.length, let J := P.interval ⟨j.val,j.isLt.trans_le count⟩
    J.left = vs[j.val].left ∧ J.right = vs[j.val].right ∧
    J.leftBoundary = T.visitMarker h τ vs[j.val].state
  full : cut = ρ.horizon → P.size = vs.length
  suffix : cut < ρ.horizon → ∃ hj : vs.length < P.size, P.size = vs.length+1 ∧
    P.interval ⟨vs.length,hj⟩ = ⟨cut,ρ.horizon,●,○⟩

private theorem partition_eq {D : Set ℝ} (P Q : IntervalPartition D)
    (hn : P.size = Q.size)
    (hp : ∀ i : Fin P.size, P.interval i = Q.interval ⟨i.val,hn ▸ i.isLt⟩) : P = Q := by
  cases P; cases Q
  cases hn
  congr
  exact funext hp

theorem CutLayout.unique {ρ : FiniteSignal Var} {vs : List V} {cut : ℝ}
    {P Q : IntervalPartition ρ.domain} (hp : T.CutLayout h τ ρ vs cut P)
    (hq : T.CutLayout h τ ρ vs cut Q) (hc : cut ≤ ρ.horizon) : P = Q := by
  have hn : P.size = Q.size := by
    rcases lt_or_eq_of_le hc with he | he
    · exact (hp.suffix he).choose_spec.1.trans (hq.suffix he).choose_spec.1.symm
    · exact (hp.full he).trans (hq.full he).symm
  have eq3 (i : Fin P.size) :
      let A := P.interval i
      let B := Q.interval ⟨i.val,hn ▸ i.isLt⟩
      A.left = B.left ∧ A.right = B.right ∧ A.leftBoundary = B.leftBoundary := by
    by_cases hi : i.val < vs.length
    · have p := hp.pieces ⟨i.val,hi⟩
      have q := hq.pieces ⟨i.val,hi⟩
      exact ⟨p.1.trans q.1.symm,p.2.1.trans q.2.1.symm,p.2.2.trans q.2.2.symm⟩
    · have he : cut < ρ.horizon := lt_of_le_of_ne hc (fun eq => by
        have := hp.full eq; have := i.isLt; omega)
      obtain ⟨_,pn,ps⟩ := hp.suffix he
      obtain ⟨_,_,qs⟩ := hq.suffix he
      have k : i.val = vs.length := by have := i.isLt; omega
      have ip : i = ⟨vs.length,by omega⟩ := Fin.ext k
      have iq : (⟨i.val,hn ▸ i.isLt⟩ : Fin Q.size) = ⟨vs.length,by omega⟩ := Fin.ext k
      change (P.interval i).left = _ ∧ _
      have eq := (congrArg P.interval ip).trans (ps.trans
        (qs.symm.trans (congrArg Q.interval iq.symm)))
      exact ⟨congrArg MarkedInterval.left eq,congrArg MarkedInterval.right eq,
        congrArg MarkedInterval.leftBoundary eq⟩
  apply partition_eq P Q hn
  intro i
  obtain ⟨hl,hr,hm⟩ := eq3 i
  have hb : (P.interval i).rightBoundary = (Q.interval ⟨i.val,hn ▸ i.isLt⟩).rightBoundary := by
    by_cases hi : i.val+1 < P.size
    · rw [P.adjacent_rightBoundary_eq_complement_leftBoundary i hi,
          Q.adjacent_rightBoundary_eq_complement_leftBoundary _ (show i.val+1 < Q.size by omega)]
      exact congrArg Marker.complement (eq3 ⟨i.val+1,hi⟩).2.2
    · have k : i.val+1 = P.size := by have := i.isLt; omega
      rw [P.rightBoundary_last i k,Q.rightBoundary_last _ (k.trans hn)]
  have ext (a b : MarkedInterval) (h₁ : a.left = b.left) (h₂ : a.right = b.right)
      (h₃ : a.leftBoundary = b.leftBoundary) (h₄ : a.rightBoundary = b.rightBoundary) :
      a = b := by cases a; cases b; simp_all
  exact ext _ _ hl hr hm hb

/-- The closed-trace and normalized input facts are tableau facts, not assumptions
about clock values, endpoint ownership or atom satisfaction in the execution. -/
theorem ordinary_cut_layout_trace_through {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) {cut : ℝ} (proj : T.TypedProjectsThrough σ ρ cut)
    {i xs} (hp : BeforeFlow T h τ e i xs)
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (ordinary : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ T.terminalModes) :
    ∃ P : IntervalPartition ρ.domain,
      T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P ∧
      T.recognizes hf ρ P := by
  let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]
  have times : VisitTimes T h τ vs cut := .snoc (T.beforeFlow_times h τ e hp) _ hl.le
  obtain ⟨Q,qn,qa⟩ := T.cut_partition_atoms h τ e hp hl hr
  obtain ⟨p,run,acc,hm,u,w,hg0,hv0,timed⟩ := T.ordinary_cut_timed_run h τ e hp hl hr hg
  change visitModes p = vs.map _ at hm
  change Q.size = vs.length at qn
  have hc : cut ≤ ρ.horizon := proj.1
  have h0 : 0 ≤ cut := (e.start_time_mem_domain i).1.trans hl.le
  have hend : ∀ j : Fin Q.size, (Q.interval j).right ≤ cut := by
    intro j
    let k : Fin vs.length := ⟨j.val,qn ▸ j.isLt⟩
    exact ((qa k).2.1).le.trans (T.visits_end_le h τ times _ (List.getElem_mem k.isLt))
  have completion : ∃ (P : IntervalPartition ρ.domain) (hn : Q.size ≤ P.size),
      (∀ j : Fin Q.size, P.interval ⟨j.val,j.isLt.trans_le hn⟩ = Q.interval j) ∧
      (cut = ρ.horizon → P.size = Q.size) ∧
      (cut < ρ.horizon → ∃ hj : Q.size < P.size, P.size = Q.size+1 ∧
        P.interval ⟨Q.size,hj⟩ = ⟨cut,ρ.horizon,●,○⟩) := by
    rcases lt_or_eq_of_le hc with he | he
    · obtain ⟨P,hn,ho,hs⟩ := complete_prefix ρ h0 hc Q hend
      exact ⟨P,hn,ho,fun hh => (he.ne hh).elim,hs⟩
    · subst cut
      exact ⟨Q,le_rfl,fun _ => rfl,fun _ => rfl,fun hh => hh.false.elim⟩
  obtain ⟨P,hle,old,full,suffix⟩ := completion
  have hn : vs.length ≤ P.size := qn ▸ hle
  have aligned (j : Fin vs.length) :
      let J := P.interval ⟨j.val,j.isLt.trans_le hn⟩
      J.left = vs[j.val].left ∧ J.right = vs[j.val].right ∧
      J.leftBoundary = T.visitMarker h τ vs[j.val].state ∧
      ∀ t : σ.Time, t.val ∈ J → T.atomsAt vs[j.val].state.val.1 (σ.value t) := by
    change (P.interval _).left = _ ∧ _
    rw [old (⟨j.val,qn.symm ▸ j.isLt⟩ : Fin Q.size)]
    exact qa j
  refine ⟨P,⟨hn,fun j => ⟨(aligned j).1,(aligned j).2.1,(aligned j).2.2.1⟩,
    fun he => (full he).trans qn,?_⟩,p,run,acc,?_⟩
  · intro he
    obtain ⟨hj,hsize,hpiece⟩ := suffix he
    refine ⟨qn ▸ hj, hsize.trans (congrArg (·+1) qn),?_⟩
    exact (congrArg P.interval (Fin.ext qn.symm)).trans hpiece
  refine timed.forall_trace_holds_of_initialReset T T.label hf ρ P ?_ ?_ u hg0 hv0 (closed p run) ?_
  · simpa only [List.length_map] using hn.trans (Nat.le_succ P.size)
  · intro j hj
    let k : Fin vs.length := ⟨j.val,by simpa only [List.length_map] using j.isLt⟩
    have ha := aligned k
    rw [List.getElem_map]
    have he := (STLTableau.Judgement.duration P ⟨k.val,k.isLt.trans_le hn⟩).coe_nonneg
    change 0 ≤ (P.interval _).right - (P.interval _).left at he
    rw [ha.1,ha.2.1] at he
    change ((vs[k.val].right - vs[k.val].left).toNNReal : ℝ) = (P.interval _).right - _
    rw [Real.coe_toNNReal _ he,ha.1,ha.2.1]
  · intro j β l hmemb
    obtain ⟨hj,eq⟩ := T.frame_modes p hf j
    have hj' : j.val < vs.length := by simpa [hm] using hj
    let k : Fin vs.length := ⟨j.val,hj'⟩
    rw [eq] at hmemb
    simp only [hm,List.getElem_map] at hmemb
    have ha := aligned k
    have hmem := List.getElem_mem (l := vs) hj'
    apply (Finiteness.normalizedReady_labels_hold_iff T _ (ready _ hmem) ρ P β _
      (hj'.trans_le hn)).2 _ l hmemb
    refine ⟨ordinary _ hmem,fun m hm => ha.2.2.1.trans
      (T.label_eq_visitMarker h τ _ m hm),?_⟩
    intro a hat t ht
    let jQ : Fin Q.size := ⟨k.val,qn.symm ▸ k.isLt⟩
    have htQ : t.val ∈ (Q.interval jQ).carrier := by
      rw [← old jQ]
      exact ht
    have htI : t.val ∈ Set.Ico (0 : ℝ) cut := by
      rw [← Q.covers]
      exact Set.mem_iUnion.mpr ⟨jQ,htQ⟩
    let t' : σ.Time := ⟨t.val,t.property.1,htI.2.trans_le
      (hr.trans ((e.increasing.monotone (Fin.le_last i.succ)).trans e.last_le_horizon))⟩
    exact (T.atomHolds_iff a _ _ (h.atom_variables _ vs[k.val].state.val.1.property a hat)
      (proj.2 t' t rfl htI.2)).mp (ha.2.2.2 t' ht a hat)

/-- The closed-trace and normalized input facts are tableau facts, not assumptions
about clock values, endpoint ownership or atom satisfaction in the execution. -/
theorem ordinary_cut_layout_trace {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (ordinary : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ T.terminalModes) :
    ∃ P : IntervalPartition ρ.domain,
      T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P ∧
      T.recognizes hf ρ P := by
  have hc := hr.trans ((e.increasing.monotone (Fin.le_last i.succ)).trans e.last_le_horizon)
  exact T.ordinary_cut_layout_trace_through h τ e ρ (proj.through T hc) hp hl hr hg hf
    closed ready ordinary

private theorem jump_nonterminal {a b : (𝓗).State}
    (hj : (𝓗).DiscreteStep a b) (ht : b.val.2 (.inl T.globalClock) < τ) :
    b.val.1 ∉ T.terminalModes := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hterm,_⟩ := hj
  exact fun hs => (not_le_of_gt ht) (hterm.mp hs)

theorem ordinary_visits_of_initial {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    {i xs} (hp : BeforeFlow T h τ e i xs) :
    (∀ v ∈ xs, v.state.val.1 ∉ T.terminalModes) ∧ (e.start i).val.1 ∉ T.terminalModes := by
  have early (j : Fin e.count) : (e.start j).val.2 (.inl T.globalClock) < τ :=
    (T.typed_entry_time h τ e j).trans_lt ((e.start_time_mem_domain j).2.trans_eq hh)
  induction hp with
  | initial he => exact ⟨by simp, he ▸ hi⟩
  | initialJump step =>
    exact ⟨by simpa using hi,T.jump_nonterminal h τ step (early _)⟩
  | direct _ _ step ih =>
    refine ⟨?_,T.jump_nonterminal h τ step (early _)⟩
    intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with old | rfl
    · exact ih.1 v old
    · exact ih.2
  | viaPoint _ _ s enter leave ih =>
    have hs := T.jump_nonterminal h τ enter
      ((T.typed_jump_global h τ leave).symm.trans_lt (early _))
    refine ⟨?_,T.jump_nonterminal h τ leave (early _)⟩
    intro v hv
    simp at hv
    rcases hv with old | rfl | rfl
    · exact ih.1 v old
    · exact ih.2
    · exact hs

theorem ordinary_cut_trace {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (ordinary : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ T.terminalModes) :
    ∃ P : IntervalPartition ρ.domain, T.recognizes hf ρ P := by
  obtain ⟨P,_,hp'⟩ := T.ordinary_cut_layout_trace h τ e ρ proj hp hl hr hg hf closed ready ordinary
  exact ⟨P,hp'⟩

theorem recognizes_on_induced_ordinary_cut_through {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) {cut : ℝ} (proj : T.TypedProjectsThrough σ ρ cut)
    {i xs} (hp : BeforeFlow T h τ e i xs)
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    (P : IntervalPartition ρ.domain)
    (induced : T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P) :
    T.recognizes hf ρ P := by
  obtain ⟨pre,last⟩ := T.ordinary_visits_of_initial h τ e hh hi hp
  have ordinary : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      v.state.val.1 ∉ T.terminalModes := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact pre v hv
    · obtain rfl := List.mem_singleton.mp hv
      exact last
  obtain ⟨Q,hQ,hrQ⟩ := T.ordinary_cut_layout_trace_through h τ e ρ proj hp hl hr hg hf closed ready ordinary
  exact (hQ.unique T h τ induced proj.1) ▸ hrQ

theorem recognizes_on_induced_ordinary_cut {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs) {cut : ℝ}
    (hl : e.boundary i.castSucc < cut) (hr : cut ≤ e.boundary i.succ)
    (hg : (e.start i).val.1 ∈ T.goalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    (P : IntervalPartition ρ.domain)
    (induced : T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,cut⟩]) cut P) :
    T.recognizes hf ρ P := by
  have hc := hr.trans ((e.increasing.monotone (Fin.le_last i.succ)).trans e.last_le_horizon)
  exact T.recognizes_on_induced_ordinary_cut_through h τ e ρ (proj.through T hc) hp hl hr hg
    hf closed ready hh hi P induced

/-- Terminal cut with its actual incoming edge. The final frame is evaluated
at P.size; neither its predicates nor the signal are read at τ. -/
theorem run_on_terminal_cut {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs) (jump : (𝓗).DiscreteStep (e.finish i) e.finalState)
    (term : e.finalState.val.1 ∈ T.terminalModes) (goal : e.finalState.val.1 ∈ T.goalModes)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (finalLabels : ∀ l ∈ T.label e.finalState.val.1.val, l = .terminal ∨ l = .marker ●)
    :
    ∃ (P : IntervalPartition ρ.domain) (p : Path Clock State),
      T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P ∧
      p.run T ∧ p.accepting T ∧ p.lastState = e.finalState.val.1.val ∧
      ∀ α, (p.trace T.label hf).holds ρ P α ⟨0,by omega⟩ := by
  let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
  have hρ : τ = ρ.horizon := hh.symm.trans proj.1
  have cut := T.typed_terminal_cut h τ e hh jump term
  have hb : e.boundary i.succ = τ := by
    have hf := T.typed_flow_global h τ e i
    have he := T.typed_entry_time h τ e i
    have hj := T.typed_jump_global h τ jump
    have ht := T.typed_final_time h τ e
    have hd : (e.duration i : ℝ) = e.boundary i.succ - e.boundary i.castSucc := e.duration_eq i
    linarith
  obtain ⟨Q,qn,qa⟩ := T.cut_partition_atoms h τ e hp
    ((e.increasing Fin.castSucc_lt_succ).trans_eq hb) hb.ge
  change Q.size = vs.length at qn
  let R : IntervalPartition ρ.domain := { Q with covers := Q.covers.trans (congrArg (Set.Ico 0) hρ) }
  have rlayout : T.CutLayout h τ ρ vs τ R :=
    ⟨qn.ge, fun j => ⟨(qa j).1,(qa j).2.1,(qa j).2.2.1⟩,fun _ => qn,
      fun h => (h.ne hρ).elim⟩
  obtain ⟨p,run,acc,hm,u,hg,hv,timed⟩ := T.terminal_cut_timed_run h τ e hp jump term goal hh
  change visitModes p = vs.map _ ++ [_] at hm
  have ord := T.ordinary_visits_of_initial h τ e hh hi hp
  have ordAll : ∀ v ∈ vs, v.state.val.1 ∉ T.terminalModes := by
    intro v hmem
    rcases List.mem_append.mp hmem with old | last
    · exact ord.1 v old
    · obtain rfl := List.mem_singleton.mp last
      exact ord.2
  have mode_last (s : Path Clock State) : (visitModes s).getLast? = some s.lastState := by
    induction s with
    | last => rfl
    | step l q s ih => simp [visitModes,List.getLast?_cons,ih,Path.lastState]
  have hlast := mode_last p
  rw [hm] at hlast
  refine ⟨R,p,rlayout,run,acc,by simpa using hlast.symm,?_⟩
  refine timed.forall_trace_holds_of_initialReset T T.label hf ρ R ?_ ?_ u hg hv (closed p run) ?_
  · change (vs.map (T.visitDuration h τ) ++ [0]).length ≤ Q.size+1
    simp [qn]
  · intro j hj
    change j.val+1 < (vs.map (T.visitDuration h τ) ++ [0]).length at hj
    simp only [List.length_append,List.length_map,List.length_singleton] at hj
    let k : Fin vs.length := ⟨j.val,by omega⟩
    have hl := (qa k).1
    have hr := (qa k).2.1
    have hnon := (STLTableau.Judgement.duration Q ⟨k.val,qn.symm ▸ k.isLt⟩).coe_nonneg
    change 0 ≤ (Q.interval _).right - (Q.interval _).left at hnon
    rw [hl,hr] at hnon
    rw [List.getElem_append_left (by simpa only [List.length_map] using k.isLt),List.getElem_map]
    change ((vs[k.val].right - vs[k.val].left).toNNReal : ℝ) = (Q.interval _).right - _
    rw [Real.coe_toNNReal _ hnon,hl,hr]
  · intro j β l hmem
    obtain ⟨hj,he⟩ := T.frame_modes p hf j
    rw [he] at hmem
    simp only [hm] at hj hmem
    by_cases hk : j.val < vs.length
    · let k : Fin vs.length := ⟨j.val,hk⟩
      rw [List.getElem_append_left (by simpa only [List.length_map] using hk),List.getElem_map] at hmem
      have hvs := List.getElem_mem (l := vs) hk
      have ha := qa k
      apply (Finiteness.normalizedReady_labels_hold_iff T _ (ready _ hvs) ρ R β _
        (show j.val < R.size from qn.symm ▸ hk)).2 _ l hmem
      refine ⟨ordAll _ hvs,fun m hm => ha.2.2.1.trans (T.label_eq_visitMarker h τ _ m hm),?_⟩
      intro a hat t ht
      let t' : σ.Time := ⟨t.val,t.property.1,t.property.2.trans_eq proj.1.symm⟩
      exact (T.atomHolds_iff a _ _ (h.atom_variables _ vs[k.val].state.val.1.property a hat)
        (proj.2 t' t rfl)).mp (ha.2.2.2 t' ht a hat)
    · have hlast : j.val = vs.length := by simp at hj; omega
      have hpos : j.val = R.size := hlast.trans qn.symm
      rw [List.getElem_append_right (by simpa only [List.length_map] using le_of_not_gt hk)] at hmem
      simp [hlast] at hmem
      rcases finalLabels l hmem with rfl | rfl
      · exact hpos
      · simp [Local.holds,Local.toJudgement,Section3.Judgement.holds,hpos]

/-- Terminal cut with its actual incoming edge. The final frame is evaluated
at P.size; neither its predicates nor the signal are read at τ. -/
theorem recognizes_on_induced_terminal_cut {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
    (ρ : FiniteSignal Var) (proj : T.TypedProjectsTo σ ρ)
    {i xs} (hp : BeforeFlow T h τ e i xs) (jump : (𝓗).DiscreteStep (e.finish i) e.finalState)
    (term : e.finalState.val.1 ∈ T.terminalModes) (goal : e.finalState.val.1 ∈ T.goalModes)
    (hh : σ.horizon = τ) (hi : e.initialState.val.1 ∉ T.terminalModes)
    (hf : ∀ s, (T.label s).Finite)
    (closed : ∀ p : Path Clock State, p.run T → (p.trace T.label hf).freeClocks = ∅)
    (ready : ∀ v ∈ xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩],
      ∀ l ∈ T.label v.state.val.1.val, l.NormalizedReady)
    (finalLabels : ∀ l ∈ T.label e.finalState.val.1.val, l = .terminal ∨ l = .marker ●)
    (P : IntervalPartition ρ.domain)
    (induced : T.CutLayout h τ ρ (xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]) τ P) :
    T.recognizes hf ρ P := by
  obtain ⟨Q,p,hQ,run,acc,_,hs⟩ := T.run_on_terminal_cut h τ e ρ proj hp jump term goal
    hh hi hf closed ready finalLabels
  have hρ : τ = ρ.horizon := hh.symm.trans proj.1
  exact (hQ.unique T h τ induced hρ.le) ▸ (show T.recognizes hf ρ Q from ⟨p,run,acc,hs⟩)

/-- In the normalized-input tableau, a terminal state's only possible successor is
empty, not another terminal state. Consequently a nonempty terminal tail
of the translated execution is already the single incoming tableau edge. -/
theorem direct_terminal_tail_of_edges {σ : FiniteSignal T.TypedVar}
    (e : (𝓗).Execution σ) (hh : σ.horizon = τ)
    {a : (𝓗).State} (tail : Relation.TransGen (𝓗).DiscreteStep a e.finalState)
    (ht : e.finalState.val.1 ∈ T.terminalModes)
    (hedge : ∀ (s t : T.states) l, (s.val,l,t.val) ∈ T.edges →
      s ∈ T.terminalModes → t ∉ T.terminalModes) :
    (𝓗).DiscreteStep a e.finalState := by
  rcases T.typed_boundary_block h τ tail with hj | ⟨s,enter,_,leave⟩
  · exact hj
  · have he := T.typed_terminal_cut h τ e hh leave ht
    have hs : s.val.2 (.inl T.globalClock) = τ :=
      (T.typed_jump_global h τ leave).symm.trans ((T.typed_final_time h τ e).trans he)
    have ha := (T.typed_jump_global h τ enter).symm.trans hs
    have hst := T.typed_horizon_jump_target h τ enter ha
    obtain ⟨l,hl,_,_⟩ := T.typed_edge_clock_reset h τ leave
    exact (hedge _ _ l hl hst ht).elim

end STLTableau.Section4.Tableau
