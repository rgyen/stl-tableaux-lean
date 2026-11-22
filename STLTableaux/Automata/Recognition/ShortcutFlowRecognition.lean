import STLTableaux.Automata.Recognition.DirectFlowRecognition
import STLTableaux.Automata.Execution.ZeroTimeShortcut

/-! Compose certified zero-time shortcuts with execution-to-recognition.
Certificates are checked premises, not an assertion that every block admits
such a shortcut. The original flows and final state are unchanged. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- A concrete last-jump decomposition with the clock agreements required
to bypass its prefix. Nonstationary prefixes are allowed. -/
def ShortcutBlock (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    (s t : ((finiteRootTableau X root).toAutomaton h τ hτ).State) : Prop :=
  ∃ m, Relation.ReflTransGen ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s m ∧
    ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep m t ∧
    s.val.1.val.nextPart = m.val.1.val.nextPart ∧
    (∀ l, (m.val.1.val, l, t.val.1.val) ∈ (finiteRootTableau X root).edges →
      ∀ g ∈ l.guards, ∀ hc : g.clock ∈ (finiteRootTableau (Clock := Clock) X root).clocks,
        s.val.2 (.inr (.inl ⟨g.clock, hc⟩)) = m.val.2 (.inr (.inl ⟨g.clock, hc⟩))) ∧
    (∀ l, (m.val.1.val, l, t.val.1.val) ∈ (finiteRootTableau X root).edges →
      ∀ c : (finiteRootTableau (Clock := Clock) X root).clocks, l.resets.value c.val = none →
        s.val.2 (.inr (.inl c)) = m.val.2 (.inr (.inl c)))

theorem ShortcutBlock.direct {X : Set Var} {root : Formula Var}
    {h : (finiteRootTableau (Clock := Clock) X root).TranslationReady}
    {τ : ℝ} {hτ : 0 < τ}
    {s t : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hc : ShortcutBlock X root h τ hτ s t) :
    ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t := by
  obtain ⟨m, hp, hj, hn, hg, hk⟩ := hc
  exact finiteRootTableau_shortcut_overwritten_block X root h τ hτ hp hj hn hg hk

/-- Direct jumps are included by choosing an empty prefix. -/
theorem ShortcutBlock.of_direct {X : Set Var} {root : Formula Var}
    {h : (finiteRootTableau (Clock := Clock) X root).TranslationReady}
    {τ : ℝ} {hτ : 0 < τ}
    {s t : ((finiteRootTableau X root).toAutomaton h τ hτ).State}
    (hj : ((finiteRootTableau X root).toAutomaton h τ hτ).DiscreteStep s t) :
    ShortcutBlock X root h τ hτ s t :=
  ⟨s, .refl, hj, rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- All interflow blocks and the final tail have certified shortcuts. This
does not impose any new observations on skipped intermediate states. -/
def ExecutionShortcutBlocks (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ) : Prop :=
  (∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
    ShortcutBlock X root.val h σ.horizon σ.horizon_pos
      (e.finish i) (e.start ⟨i.val + 1, hi⟩)) ∧
  ShortcutBlock X root.val h σ.horizon σ.horizon_pos
    (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState

/-- A direct transition between consecutive flows is a special case of a jump block. -/
theorem ExecutionShortcutBlocks.of_direct
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    (hj : ∀ (i : Fin e.count) (hi : i.val + 1 < e.count),
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
        (e.finish i) (e.start ⟨i.val + 1, hi⟩))
    (hlast : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).DiscreteStep
      (e.finish ⟨e.count - 1, by have := e.nonempty; omega⟩) e.finalState) :
    ExecutionShortcutBlocks X root h e :=
  ⟨fun i hi => ShortcutBlock.of_direct (hj i hi), ShortcutBlock.of_direct hlast⟩

/-- Recognition from certified blocks, for either early or horizon stopping.
The endpoint-dependent label condition is explicit; no universal shortcut
selection theorem is smuggled into the execution definition. -/
theorem inputTableau_recognizes_shortcut_flows
    (X : Set Var) (root : Formula.NormalizedInput Var)
    (h : (inputTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (inputTableau (Clock := Clock) X root).HAVar}
    (e : ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).Execution σ)
    {ρ : FiniteSignal Var} (hp : (inputTableau X root).ProjectsTo σ ρ)
    (hgoal : e.finalState.val.1.val ∈ (inputTableau X root).final)
    (hinit : (e.start ⟨0, e.nonempty⟩).val ∈
      ((inputTableau X root).toAutomaton h σ.horizon σ.horizon_pos).initial)
    (hblocks : ExecutionShortcutBlocks X root h e)
    (hfirst : Local.marker ○ ∉
      (inputTableau X root).label (e.start ⟨0, e.nonempty⟩).val.1.val)
    (hconsistent : ∀ i : Fin e.count, ¬ (
      Local.marker ○ ∈ (inputTableau X root).label (e.start i).val.1.val ∧
      Local.marker ● ∈ (inputTableau X root).label (e.start i).val.1.val))
    (hearly : e.boundary ⟨e.count, by omega⟩ < σ.horizon →
      Local.marker ○ ∉ (inputTableau X root).label e.finalState.val.1.val)
    (horizon : e.boundary ⟨e.count, by omega⟩ = σ.horizon →
      ∀ l ∈ (inputTableau X root).label e.finalState.val.1.val,
        l = .terminal ∨ l = .marker ●) :
    ∃ P : IntervalPartition ρ.domain,
      (inputTableau (Clock := Clock) X root).recognizes JudgementTableau.labels_finite ρ P := by
  have hj := fun i hi => (hblocks.1 i hi).direct
  have hlast := hblocks.2.direct
  by_cases he : e.boundary ⟨e.count, by omega⟩ = σ.horizon
  · obtain ⟨P, _, hr⟩ := inputTableau_recognizes_direct_flows_at_horizon X root h e hp
      he hgoal hinit hj hlast hfirst hconsistent (horizon he)
    exact ⟨P, hr⟩
  · have hlt : e.boundary ⟨e.count, by omega⟩ < σ.horizon :=
      lt_of_le_of_ne e.last_le_horizon he
    exact inputTableau_recognizes_direct_flows X root h e hp hlt hgoal hinit
      hj hlast hfirst hconsistent (hearly hlt)

end STLTableau.Section4.Finiteness
