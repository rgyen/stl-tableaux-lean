import STLTableaux.Automata.Translation.TypedTableauAutomata

namespace STLTableau.Section4.Tableau
open Section3
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

private def markValue : Marker → ℝ
  | .closed => 1
  | .open => 0

/-- The entry valuation after the incoming reset. -/
def entryValue (t : ℝ) (α : ClockValuation Clock) (x : Var → ℝ) (m : Marker) :
    T.TypedVar → ℝ
  | .inl (.inl i) => x i.val
  | .inl (.inr (.inl c)) => α c.val
  | .inl (.inr (.inr _)) => t
  | .inr false => 0
  | .inr true => markValue m

private theorem entryInvariant (h : T.TranslationReady) (τ t : ℝ) (q : T.states)
    (α : ClockValuation Clock) (x : Var → ℝ) (m : Marker)
    (hh : q ∉ T.terminalModes → t ≤ τ)
    (atoms : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → a.Holds x)
    (marks : ∀ b, Local.marker b ∈ T.label q.val → b = m) :
    (q,T.entryValue t α x m) ∈ (T.typedAutomaton h τ).invariant := by
  refine ⟨?_,hh,?_,?_⟩
  · cases m <;> simp [entryValue,bit,markValue]
  · intro a ha
    exact (T.atomHolds_iff _ _ _ (h.atom_variables _ q.property a ha) (fun _ => rfl)).2
      (atoms a ha)
  · intro b hb
    rw [marks b hb]
    cases m <;> simp [entryValue,bit,markValue]

theorem forward_initial_entry (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    (q : T.states) (l : EdgeLabel Clock) (hin : (l,q.val) ∈ T.initial)
    (α : ClockValuation Clock) (x : Var → ℝ)
    (guards : ∀ g ∈ l.guards, g.holds α)
    (atoms : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → a.Holds x)
    (marks : ∀ b, Local.marker b ∈ T.label q.val → b = ●) :
    ∃ s : (T.typedAutomaton h τ).State, s.val ∈ (T.typedAutomaton h τ).initial ∧
      s.val = (q,T.entryValue 0 (l.resets.apply α) x ●) := by
  let v := T.old (T.entryValue 0 α x ●)
  refine ⟨⟨_,T.entryInvariant h τ 0 q _ x ● (fun _ => hτ.le) atoms marks⟩,?_,rfl⟩
  refine ⟨l,hin,v,(T.guardsHold_iff l v α (h.initial_guards _ hin) (fun _ => rfl)).2 guards,
    ?_,rfl,rfl⟩
  funext y
  rcases y with i | c
  · rfl
  · rcases c with c | u
    · exact (T.reset_clock_agrees l.resets v α (fun _ => rfl) c).symm
    · cases u; rfl

/-- Realize an edge at an ordinary entry before τ, or at a terminal
entry at τ. A source atom is tested on the POST-value precisely for
an open successor. No preservation of all real variables is assumed. -/
theorem forward_jump_entry (h : T.TranslationReady) (τ : ℝ)
    (s : (T.typedAutomaton h τ).State) (q : T.states) (l : EdgeLabel Clock)
    (edge : (s.val.1.val,l,q.val) ∈ T.edges) (α : ClockValuation Clock)
    (clockEq : ∀ c : T.clocks, s.val.2 (.inl (.inr (.inl c))) = (α c.val : ℝ))
    (guards : ∀ g ∈ l.guards, g.holds α)
    (x : Var → ℝ) (m : Marker)
    (horizon : q ∈ T.terminalModes ↔ τ ≤ s.val.2 (.inl T.globalClock))
    (zero : s.val.2 T.dwell = 0 → s.val.2 T.bit = 1 ∧ m = ○)
    (atoms : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → a.Holds x)
    (marks : ∀ b, Local.marker b ∈ T.label q.val → b = m)
    (post : m = ○ → ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label s.val.1.val →
      a.Holds x) :
    ∃ s' : (T.typedAutomaton h τ).State,
      s'.val = (q,T.entryValue (s.val.2 (.inl T.globalClock)) (l.resets.apply α) x m) ∧
      (T.typedAutomaton h τ).DiscreteStep s s' := by
  let t := s.val.2 (.inl T.globalClock)
  let v := T.entryValue t (l.resets.apply α) x m
  let s' : (T.typedAutomaton h τ).State := ⟨(q,v),T.entryInvariant h τ t q _ x m
    (fun hn => (lt_of_not_ge (fun hg => hn (horizon.mpr hg))).le) atoms marks⟩
  let e := (s.val.1,l,q)
  have he : e ∈ (T.typedAutomaton h τ).edge := edge
  refine ⟨s',rfl,⟨⟨e,he⟩,rfl,rfl,rfl,rfl,
    (T.guardsHold_iff l _ α (h.edge_guards _ edge) clockEq).2 guards,
    fun c => (T.reset_clock_agrees l.resets _ α clockEq c).symm,rfl,rfl,horizon,?_,?_⟩⟩
  · intro hz
    obtain ⟨hs,hm⟩ := zero hz
    exact ⟨hs,by change markValue m = 0; rw [hm]; rfl⟩
  · intro hm a ha
    have ho : m = ○ := by
      change markValue m = 0 at hm
      cases m <;> simp_all [markValue]
    exact (T.atomHolds_iff _ _ _ (h.atom_variables _ s.val.1.property a ha)
      (fun _ => rfl)).2 (post ho _ ha)

end STLTableau.Section4.Tableau
