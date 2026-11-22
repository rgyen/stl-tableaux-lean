import STLTableaux.Automata.Translation.NormalizedInputReachability
import STLTableaux.Automata.Translation.InitialTerminalSupport
import STLTableaux.Automata.Recognition.ExecutionFlowPartition

/-! Exact local-label obligations after checking the normalized input grammar.
These results isolate marker/terminal alignment; they do not assume that such
an alignment exists for every raw execution path. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var State : Type*}

theorem normalizedReady_atomic_cases {p : Predicate Clock Var}
    (hp : predicateNormalizedReady p) (ha : p.IsAtomic) :
    p = .plain .truth ∨ ∃ a, p = .plain (.atom a) := by
  cases p with
  | upper => exact ha.elim
  | bounded => exact ha.elim
  | plain φ =>
    cases φ with
    | truth => exact Or.inl rfl
    | atom a => exact Or.inr ⟨a, rfl⟩
    | neg φ =>
      cases φ <;> simp only [Predicate.IsAtomic] at ha
      exact (Formula.not_normalizedReady_falsity hp).elim
    | and => exact ha.elim
    | «until» => exact ha.elim

/-- On a nonterminal partition position, all labels reduce exactly to marker
agreement and pointwise numerical atoms. True contributes no condition. -/
theorem normalizedReady_labels_hold_iff (T : Tableau Clock Var State) (s : State)
    (hs : ∀ l ∈ T.label s, l.NormalizedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hk : k.val < P.size) :
    (∀ l ∈ T.label s, l.holds σ P α k) ↔
      Local.terminal ∉ T.label s ∧
      (∀ m, Local.marker m ∈ T.label s → (P.interval ⟨k.val, hk⟩).leftBoundary = m) ∧
      (∀ a, Local.predicate (.plain (.atom a)) ∈ T.label s →
        ∀ t : σ.Time, t.val ∈ (P.interval ⟨k.val, hk⟩).carrier → a.Holds (σ.value t)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro ht
      have he : k.val = P.size := h .terminal ht
      omega
    · intro m hm
      simpa only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hk]
        using h (.marker m) hm
    · intro a ha
      simpa only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hk,
        Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies, MarkedInterval.mem_carrier]
        using h (.predicate (.plain (.atom a))) ha
  · rintro ⟨hn, hm, ha⟩ l hl
    cases l with
    | terminal => exact (hn hl).elim
    | marker m =>
      simpa only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hk]
        using hm m hl
    | predicate p =>
      rcases normalizedReady_atomic_cases (hs _ hl) (T.label_atomic _ _ hl) with he | ⟨a, he⟩
      · subst p
        simp only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hk,
          Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies, implies_true]
      · subst p
        simpa only [Local.holds, Local.toJudgement, Section3.Judgement.holds, dif_pos hk,
          Predicate.holds, predicateSatisfies, FiniteSignal.Satisfies, MarkedInterval.mem_carrier]
          using ha a hl

/-- Once a full-domain partition piece agrees with a marked positive-flow
piece, numerical atoms are discharged by the actual execution. Only terminal
exclusion and marker agreement remain. No suffix invariant is assumed. -/
theorem markedFlow_labels_hold_iff (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal T.HAVar} (e : (T.toAutomaton h τ hτ).Execution σ)
    {ρ : FiniteSignal Var} (hp : T.ProjectsTo σ ρ)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) (P : IntervalPartition ρ.domain)
    (k : STLTableau.Judgement.Position P) (hk : k.val < P.size)
    (he : P.interval ⟨k.val, hk⟩ = (e.markedFlowPartition m hfirst hlast).interval i)
    (hs : ∀ l ∈ T.label (e.start i).val.1.val, l.NormalizedReady)
    (α : ClockValuation Clock) :
    (∀ l ∈ T.label (e.start i).val.1.val, l.holds ρ P α k) ↔
      Local.terminal ∉ T.label (e.start i).val.1.val ∧
      (∀ b, Local.marker b ∈ T.label (e.start i).val.1.val → m ⟨i.val, by omega⟩ = b) := by
  rw [normalizedReady_labels_hold_iff T _ hs ρ P α k hk]
  have hatom : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label (e.start i).val.1.val →
      ∀ u : ρ.Time, u.val ∈ (P.interval ⟨k.val, hk⟩).carrier → a.Holds (ρ.value u) := by
    intro a ha u hu
    let t : σ.Time := ⟨u.val, u.property.1, hp.1.symm ▸ u.property.2⟩
    exact T.markedFlowPartition_projected_atom h τ hτ e hp m hfirst hlast i t u rfl
      (he ▸ hu) a ha
  rw [and_iff_left hatom, he, e.markedFlowPartition_leftMarker m hfirst hlast i]

theorem inputTableau_execution_flow_normalizedReady [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h τ hτ).Execution σ) (i : Fin e.count) :
    (e.start i).val.1.val.NormalizedReady := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  exact inputTableau_modeSteps_normalizedReady X root
    (Tableau.execution_start_modeSteps _ h τ hτ e i)
    (inputTableau_initial_normalizedReady X root hl)

/-- For a real execution of a checked normalized-input tableau, syntax, atom satisfaction
and nonterminality of each positive-flow mode are derived. On a corresponding
partition piece, its whole label holds exactly when its markers agree.
This does not assert existence of that piece/marker assignment for all jumps. -/
theorem inputTableau_flow_labels_iff_markers [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (m : Fin (e.count + 1) → Marker)
    (hfirst : m ⟨0, by omega⟩ = ●) (hlast : m ⟨e.count, by omega⟩ = ●)
    (i : Fin e.count) (P : IntervalPartition ρ.domain)
    (k : STLTableau.Judgement.Position P) (hk : k.val < P.size)
    (he : P.interval ⟨k.val, hk⟩ = (e.markedFlowPartition m hfirst hlast).interval i)
    (α : ClockValuation Clock) :
    (∀ l ∈ (inputTableau X root).label (e.start i).val.1.val, l.holds ρ P α k) ↔
      ∀ b, Local.marker b ∈ (inputTableau X root).label (e.start i).val.1.val →
        m ⟨i.val, by omega⟩ = b := by
  have hs := inputTableau_execution_flow_normalizedReady X root h _ _ e i
  have hn := Tableau.execution_flow_nonterminal (inputTableau X root) h _ _ e rfl
    (finiteRootTableau_execution_initial_nonterminal X root.val h _ _ e) i
  exact (markedFlow_labels_hold_iff (inputTableau X root) h _ _ e hp m hfirst hlast
    i P k hk he (fun l hl => hs.1 l hl.1) α).trans (and_iff_right hn)

end STLTableau.Section4.Finiteness
