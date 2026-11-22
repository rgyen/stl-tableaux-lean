import STLTableaux.Automata.Recognition.TypedExecutionCuts

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)

structure TimedVisit where
  state : (𝓗).State
  left : ℝ
  right : ℝ

variable {σ : FiniteSignal T.TypedVar} (e : (𝓗).Execution σ)
local notation "V" => TimedVisit T h τ

/-- Exactly the visits before positive flow i. A boundary with two jumps
retains its intermediate state and both step witnesses. -/
inductive BeforeFlow (T : Tableau Clock Var State) (h : T.TranslationReady) (τ : ℝ)
    {σ : FiniteSignal T.TypedVar} (e : (T.typedAutomaton h τ).Execution σ) :
    Fin e.count → List (TimedVisit T h τ) → Prop where
  | initial (same : e.initialState = e.start ⟨0,e.nonempty⟩) :
      BeforeFlow T h τ e ⟨0,e.nonempty⟩ []
  | initialJump (step : (T.typedAutomaton h τ).DiscreteStep e.initialState (e.start ⟨0,e.nonempty⟩)) :
      BeforeFlow T h τ e ⟨0,e.nonempty⟩ [⟨e.initialState,0,0⟩]
  | direct {i j : Fin e.count} {xs : List (TimedVisit T h τ)} (next : i.val + 1 = j.val) (pre : BeforeFlow T h τ e i xs)
      (step : (T.typedAutomaton h τ).DiscreteStep (e.finish i) (e.start j)) :
      BeforeFlow T h τ e j (xs ++ [⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩])
  | viaPoint {i j : Fin e.count} {xs : List (TimedVisit T h τ)} (next : i.val + 1 = j.val) (pre : BeforeFlow T h τ e i xs)
      (s : (T.typedAutomaton h τ).State) (enter : (T.typedAutomaton h τ).DiscreteStep (e.finish i) s)
      (leave : (T.typedAutomaton h τ).DiscreteStep s (e.start j)) :
      BeforeFlow T h τ e j (xs ++ [⟨e.start i,e.boundary i.castSucc,e.boundary i.succ⟩,
        ⟨s,e.boundary i.succ,e.boundary i.succ⟩])

theorem exists_beforeFlow (e : (T.typedAutomaton h τ).Execution σ) (i : Fin e.count) :
    ∃ xs, BeforeFlow T h τ e i xs := by
  obtain ⟨k,hk⟩ := i
  induction k with
  | zero =>
    rcases T.typed_initial_visits h τ e with hs | hj
    · exact ⟨_, .initial hs⟩
    · exact ⟨_, .initialJump hj⟩
  | succ k ih =>
    let j : Fin e.count := ⟨k,by omega⟩
    obtain ⟨xs, hp⟩ := ih j.isLt
    rcases T.typed_execution_boundary h τ e j hk with hj | ⟨s, hi, _, ho⟩
    · exact ⟨_, .direct rfl hp hj⟩
    · exact ⟨_, .viaPoint rfl hp s hi ho⟩

/-- Contiguity concerns numerical boundaries only; endpoint ownership is
assigned later from the state bit. -/
inductive VisitTimes : List V → ℝ → Prop where
  | nil : VisitTimes [] 0
  | snoc {xs a b} (pre : VisitTimes xs a) (s : (𝓗).State) (hab : a ≤ b) :
      VisitTimes (xs ++ [⟨s,a,b⟩]) b

theorem beforeFlow_times (e : (T.typedAutomaton h τ).Execution σ) {i : Fin e.count}
    {xs : List V} (hp : BeforeFlow T h τ e i xs) :
    VisitTimes T h τ xs (e.boundary i.castSucc) := by
  induction hp with
  | initial =>
    change VisitTimes T h τ [] (e.boundary ⟨0,by omega⟩)
    rw [e.first_zero]; exact .nil
  | initialJump =>
    change VisitTimes T h τ [_] (e.boundary ⟨0,by omega⟩)
    rw [e.first_zero]; exact .snoc .nil _ le_rfl
  | @direct i j xs hn _ _ ih =>
    have hb : i.succ = j.castSucc := Fin.ext hn
    rw [← hb]
    exact .snoc ih _ (e.increasing Fin.castSucc_lt_succ).le
  | @viaPoint i j xs hn _ s _ _ ih =>
    have hb : i.succ = j.castSucc := Fin.ext hn
    rw [← hb]
    simpa only [List.append_assoc, List.singleton_append] using
      (VisitTimes.snoc (.snoc ih (e.start i) (e.increasing Fin.castSucc_lt_succ).le) s le_rfl)

/-- Cut inside an ordinary positive flow: no fabricated jump or extra mode
is used for its last (possibly shortened) visit. -/
theorem exists_ordinary_cut_visits (e : (T.typedAutomaton h τ).Execution σ)
    (i : Fin e.count) (t : ℝ)
    (ht : e.boundary i.castSucc < t) (_hend : t ≤ e.boundary i.succ)
    (_goal : (e.start i).val.1 ∈ T.goalModes) (_ordinary : (e.start i).val.1 ∉ T.terminalModes) :
    ∃ xs, BeforeFlow T h τ e i xs ∧
      VisitTimes T h τ (xs ++ [⟨e.start i,e.boundary i.castSucc,t⟩]) t := by
  obtain ⟨xs,hp⟩ := T.exists_beforeFlow h τ e i
  exact ⟨xs,hp,.snoc (T.beforeFlow_times h τ e hp) _ ht.le⟩

end STLTableau.Section4.Tableau
