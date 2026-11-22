import STLTableaux.Automata.Translation.TableauAutomata

/-! Exact local jump correspondence and structural paths for zero-time tails.
Path validity here does not assert trace satisfaction. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)

/-- Both directions retain the same incoming label, guard and reset. The
endpoints are semantic states, so their invariants are already required. -/
theorem discreteStep_iff {s s' : (T.toAutomaton h τ hτ).State} :
    (T.toAutomaton h τ hτ).DiscreteStep s s' ↔
      ∃ l : EdgeLabel Clock,
        (s.val.1.val, l, s'.val.1.val) ∈ T.edges ∧
        T.guardsHold l s.val.2 ∧ s'.val.2 = T.reset l.resets s.val.2 ∧
        (s'.val.1 ∈ T.terminalModes → τ ≤ s'.val.2 T.globalClock) ∧
        (s'.val.1 ∉ T.terminalModes → s'.val.2 T.globalClock < τ) := by
  constructor
  · rintro ⟨e, hs, ht, hj⟩
    refine ⟨e.val.2.1, ?_, hj.1.2.2.1, hj.1.2.2.2, hj.2⟩
    have he := e.property
    change (e.val.1.val, e.val.2.1, e.val.2.2.val) ∈ T.edges at he
    simpa only [hs, ht] using he
  · rintro ⟨l, he, hg, hr, hb⟩
    exact ⟨⟨(s.val.1, l, s'.val.1), he⟩, rfl, rfl, ⟨rfl, rfl, hg, hr⟩, hb⟩

/-- An entire zero-time tail has an actual tableau path with every traversed
edge retained. The arbitrary first incoming label is supplied by its caller. -/
theorem discreteSteps_path {s s' : (T.toAutomaton h τ hτ).State}
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (incoming : EdgeLabel Clock) :
    ∃ p : Path Clock State, p.valid T ∧
      p.firstState = s.val.1.val ∧ p.firstIncoming = incoming ∧
      p.lastState = s'.val.1.val := by
  induction hj using Relation.ReflTransGen.head_induction_on generalizing incoming with
  | refl => exact ⟨.last incoming _, s'.val.1.property, rfl, rfl, rfl⟩
  | @head a b hab _ ih =>
    obtain ⟨l, he, _⟩ := (T.discreteStep_iff h τ hτ).mp hab
    obtain ⟨p, hp, hfirst, hincoming, hlast⟩ := ih l
    refine ⟨.step incoming a.val.1.val p, ⟨a.val.1.property, hp, ?_⟩,
      rfl, rfl, hlast⟩
    simpa only [hfirst, hincoming] using he

/-- Starting from an initial semantic state upgrades that structural path
to a tableau run. This is not a recognition theorem. -/
theorem initial_discreteSteps_run {s s' : (T.toAutomaton h τ hτ).State}
    (hs : s.val ∈ (T.toAutomaton h τ hτ).initial)
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s') :
    ∃ p : Path Clock State, p.run T ∧ p.lastState = s'.val.1.val := by
  obtain ⟨l, hl, _⟩ := hs
  obtain ⟨p, hp, hfirst, hincoming, hlast⟩ := T.discreteSteps_path h τ hτ hj l
  refine ⟨p, ⟨hp, ?_⟩, hlast⟩
  simpa only [hfirst, hincoming] using hl

theorem initial_discreteSteps_accepting_run
    {s s' : (T.toAutomaton h τ hτ).State}
    (hs : s.val ∈ (T.toAutomaton h τ hτ).initial)
    (hj : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s s')
    (hg : s'.val.1 ∈ T.goalModes) :
    ∃ p : Path Clock State, p.run T ∧ p.accepting T := by
  obtain ⟨p, hp, hlast⟩ := T.initial_discreteSteps_run h τ hτ hs hj
  exact ⟨p, hp, hp.1, hlast ▸ hg⟩

end STLTableau.Section4.Tableau
