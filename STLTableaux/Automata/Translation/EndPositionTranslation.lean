import STLTableaux.Automata.Recognition.ForwardTableauEntry

/-! Proposed horizon policy. The published translation is preserved separately
as typedAutomaton, so counterexample checks for that definition remain valid. -/
namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- Exactly the final modes whose entire label can be read at the end position. -/
def EndGoal (q : T.states) : Prop :=
  q ∈ T.goalModes ∧ ∀ l ∈ T.label q.val, l = Local.terminal ∨ l = Local.marker ●

theorem endGoal_iff (q : T.states) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) :
    T.EndGoal q ↔ q ∈ T.goalModes ∧
      ∀ l ∈ T.label q.val, l.holds σ P α ⟨P.size,by omega⟩ := by
  constructor
  · rintro ⟨hq,hl⟩
    refine ⟨hq,fun l hm => ?_⟩
    rcases hl l hm with rfl | rfl <;>
      simp [Local.holds,Local.toJudgement,Section3.Judgement.holds]
  · rintro ⟨hq,hl⟩
    refine ⟨hq,fun l hm => ?_⟩
    have hh := hl l hm
    cases l with
    | terminal => exact Or.inl rfl
    | predicate p => simp [Local.holds,Local.toJudgement,Section3.Judgement.holds] at hh
    | marker m =>
      exact Or.inr (congrArg Local.marker (by simpa [Local.holds,Local.toJudgement,
        Section3.Judgement.holds] using hh))

def EntryAllowed (τ t dwellTime : ℝ) (q : T.states) : Prop :=
  (t < τ ∧ q ∉ T.terminalModes) ∨ (t = τ ∧ 0 < dwellTime ∧ T.EndGoal q)

def endPositionAutomaton (h : T.TranslationReady) (τ : ℝ) :
    HybridAutomaton T.states (EdgeLabel Clock) T.TypedVar :=
  { T.typedAutomaton h τ with
    jump := fun e s s' =>
      s.1 = e.val.1 ∧ s'.1 = e.val.2.2 ∧ T.guardsHold e.val.2.1 (T.old s.2) ∧
      (∀ c : T.clocks, s'.2 (.inl (.inr (.inl c))) =
        T.reset e.val.2.1.resets (T.old s.2) (.inr (.inl c))) ∧
      s'.2 (.inl T.globalClock) = s.2 (.inl T.globalClock) ∧ s'.2 T.dwell = 0 ∧
      T.EntryAllowed τ (s'.2 (.inl T.globalClock)) (s.2 T.dwell) s'.1 ∧
      (s.2 T.dwell = 0 → s.2 T.bit = 1 ∧ s'.2 T.bit = 0) ∧
      (s'.2 T.bit = 0 → T.atomsAt s.1 s'.2) }

/-- Below the horizon no edge, atomic check, reset or marker test changes. -/
theorem step_before_iff (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.endPositionAutomaton h τ).State} (ht : b.val.2 (.inl T.globalClock) < τ) :
    (T.endPositionAutomaton h τ).DiscreteStep a b ↔ (T.typedAutomaton h τ).DiscreteStep a b := by
  constructor <;> rintro ⟨e,hs,hd,h₁,h₂,hg,hr,hc,hz,hh,hm,ha⟩
  · refine ⟨e,hs,hd,h₁,h₂,hg,hr,hc,hz,?_,hm,ha⟩
    rcases hh with ⟨_,hn⟩ | ⟨he,_⟩
    · exact iff_of_false hn (not_le_of_gt ht)
    · exact (ht.ne he).elim
  · exact ⟨e,hs,hd,h₁,h₂,hg,hr,hc,hz,Or.inl ⟨ht,fun h => ht.not_ge (hh.mp h)⟩,hm,ha⟩

/-- A horizon bookkeeping jump advances to a final end-position label
and cannot be followed by another instantaneous jump. -/
theorem horizon_step_last (h : T.TranslationReady) (τ : ℝ)
    {a b : (T.endPositionAutomaton h τ).State}
    (step : (T.endPositionAutomaton h τ).DiscreteStep a b)
    (ht : a.val.2 (.inl T.globalClock) = τ) :
    T.EndGoal b.val.1 ∧ 0 < a.val.2 T.dwell ∧
      ∀ c, ¬ (T.endPositionAutomaton h τ).DiscreteStep b c := by
  obtain ⟨_,_,_,_,_,_,_,hc,hz,hh,_,_⟩ := step
  have hb := hc.trans ht
  rcases hh with ⟨hlt,_⟩ | ⟨_,hpos,hend⟩
  · exact (hlt.ne hb).elim
  · refine ⟨hend,hpos,?_⟩
    rintro c ⟨_,_,_,_,_,_,_,hc',_,hh',_,_⟩
    rcases hh' with ⟨hlt,_⟩ | ⟨_,hpos',_⟩
    · exact hlt.ne (hc'.trans hb)
    · exact hpos'.ne' hz

/-- Realize the last edge directly from the source flow endpoint.
The target bit is closed; X can be arbitrary since the target has no
atomic condition. No assumption about the signal value at τ appears. -/
theorem end_entry (h : T.TranslationReady) (τ : ℝ)
    (a : (T.endPositionAutomaton h τ).State) (q : T.states) (l : EdgeLabel Clock)
    (edge : (a.val.1.val,l,q.val) ∈ T.edges) (hq : T.EndGoal q)
    (ht : a.val.2 (.inl T.globalClock) = τ) (hd : 0 < a.val.2 T.dwell)
    (α : ClockValuation Clock)
    (hv : ∀ c : T.clocks, a.val.2 (.inl (.inr (.inl c))) = (α c.val : ℝ))
    (guards : ∀ g ∈ l.guards, g.holds α) (x : Var → ℝ) :
    ∃ b : (T.endPositionAutomaton h τ).State,
      b.val = (q,T.entryValue τ (l.resets.apply α) x ●) ∧
      (T.endPositionAutomaton h τ).DiscreteStep a b := by
  let v := T.entryValue τ (l.resets.apply α) x ●
  have inv : (q,v) ∈ (T.endPositionAutomaton h τ).invariant := by
    refine ⟨Or.inr rfl,fun _ => le_rfl,?_,?_⟩
    · intro p hp
      rcases hq.2 _ hp with hh | hh <;> cases hh
    · intro m hm
      rcases hq.2 _ hm with hh | hh
      · cases hh
      · cases hh; exact iff_of_true rfl rfl
  let b : (T.endPositionAutomaton h τ).State := ⟨(q,v),inv⟩
  let e := (a.val.1,l,q)
  have he : e ∈ (T.endPositionAutomaton h τ).edge := edge
  refine ⟨b,rfl,⟨⟨e,he⟩,rfl,rfl,rfl,rfl,
    (T.guardsHold_iff l _ α (h.edge_guards _ edge) hv).2 guards,
    fun c => (T.reset_clock_agrees l.resets _ α hv c).symm,ht.symm,rfl,
    Or.inr ⟨rfl,hd,hq⟩,fun hz => (hd.ne' hz).elim,?_⟩⟩
  intro hz
  exact (one_ne_zero (show (1 : ℝ) = 0 from hz)).elim

/-- A terminal-position trace supplies the new eligibility test from
its own final frame; it need not contain a star. -/
theorem endGoal_of_trace (p : Path Clock State) (hp : p.valid T)
    (hf : p.lastState ∈ T.final) (finite : ∀ q, (T.label q).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hlen : k.val + (p.trace T.label finite).length = P.size + 1)
    (hs : (p.trace T.label finite).holds σ P α k) :
    ∀ q : T.states, q.val = p.lastState → T.EndGoal q := by
  induction p generalizing k α with
  | last l q =>
    intro s he
    change s.val = q at he
    have hend : k.val = P.size := by
      simp only [Path.trace,Trace.length] at hlen
      omega
    apply (T.endGoal_iff s σ P (l.resets.apply α)).2
    refine ⟨show s.val ∈ T.final by rw [he]; exact hf,?_⟩
    intro x hx
    have hk : k = ⟨P.size,by omega⟩ := Fin.ext hend
    rw [he] at hx
    exact hk ▸ hs.2 x hx
  | step l q p ih =>
    by_cases hk : k.val < P.size
    · apply ih hp.2.1 hf _ ⟨k.val+1,by omega⟩
      · change k.val+1+(p.trace T.label finite).length = P.size+1
        simp only [Path.trace,Trace.length] at hlen
        omega
      · simpa only [Trace.holds,dif_pos hk] using hs.2
    · have ht := hs.2
      simp only [dif_neg hk] at ht

theorem last_piece_positive (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (i : Fin P.size) (hi : i.val+1 = P.size) :
    0 < (STLTableau.Judgement.duration P i : ℝ) := by
  obtain ⟨x,hx⟩ := P.nonempty i
  exact sub_pos.mpr ((MarkedInterval.left_le_of_mem hx).trans_lt (P.lt_right_of_mem_last i hi hx))

end STLTableau.Section4.Tableau
