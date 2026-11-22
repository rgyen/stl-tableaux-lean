import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! Construct a closed extension by well-founded iteration of decreasing steps. -/
namespace STLTableau.Section3.ClosureCatalogue
variable {Clock Var : Type*}

/-- This version permits alpha-renaming between steps: the current form
need not literally subsume its chosen representative at the next step. -/
theorem closed_form_of_decreasing_step
    (E : ClosureCatalogue Clock Var) (rank : TransitionForm Clock Var → ℕ)
    (Q : TransitionForm Clock Var → Prop)
    (step : ∀ U, Q U → ¬ E.IsClosed U → ∃ V, Q V ∧ rank V < rank U)
    (Φ : TransitionForm Clock Var) (hq : Q Φ) :
    ∃ U, Q U ∧ E.IsClosed U := by
  classical
  have main : ∀ n : ℕ, ∀ U : TransitionForm Clock Var, rank U = n → Q U →
      ∃ V, Q V ∧ E.IsClosed V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hn hU
      by_cases hc : E.IsClosed U
      · exact ⟨U, hU, hc⟩
      · obtain ⟨V, hV, hlt⟩ := step U hU hc
        exact ih (rank V) (by omega) V rfl hV
  exact main (rank Φ) Φ rfl hq

/-- An invariant anchor can survive representative changes even when literal
inclusion between consecutive working forms is unavailable. -/
theorem anchored_closed_extension_of_decreasing_step
    (E : ClosureCatalogue Clock Var) (rank : TransitionForm Clock Var → ℕ)
    (Q : TransitionForm Clock Var → Prop)
    (anchor : TransitionForm Clock Var)
    (hanchor : ∀ U, Q U → SyntacticallySubsumed anchor U)
    (step : ∀ U, Q U → ¬ E.IsClosed U → ∃ V, Q V ∧ rank V < rank U)
    (Φ : TransitionForm Clock Var) (hq : Q Φ) :
    ∃ U, SyntacticallySubsumed anchor U ∧ Q U ∧ E.IsClosed U := by
  obtain ⟨U, hU, hcU⟩ := E.closed_form_of_decreasing_step rank Q step Φ hq
  exact ⟨U, hanchor U hU, hU, hcU⟩

theorem anchored_minimal_closure_of_decreasing_step
    (E : ClosureCatalogue Clock Var) (rank : TransitionForm Clock Var → ℕ)
    (Q : TransitionForm Clock Var → Prop)
    (anchor : TransitionForm Clock Var)
    (hanchor : ∀ U, Q U → SyntacticallySubsumed anchor U)
    (step : ∀ U, Q U → ¬ E.IsClosed U → ∃ V, Q V ∧ rank V < rank U)
    (Φ : TransitionForm Clock Var) (hq : Q Φ)
    (down : ∀ U V, SyntacticallySubsumed anchor V → SyntacticallySubsumed V U → Q U → Q V) :
    ∃ V, E.IsClosure anchor V ∧ Q V := by
  obtain ⟨U, hAU, hU, hcU⟩ :=
    E.anchored_closed_extension_of_decreasing_step rank Q anchor hanchor step Φ hq
  obtain ⟨V, hV, hVU⟩ := E.exists_minimal_closed_extension_below hAU hcU
  exact ⟨V, hV, down U V hV.extension hVU hU⟩

theorem closed_extension_of_decreasing_step
    (E : ClosureCatalogue Clock Var) (rank : TransitionForm Clock Var → ℕ)
    (Q : TransitionForm Clock Var → Prop)
    (step : ∀ U, Q U → ¬ E.IsClosed U →
      ∃ V, SyntacticallySubsumed U V ∧ Q V ∧ rank V < rank U)
    (Φ : TransitionForm Clock Var) (hq : Q Φ) :
    ∃ U, SyntacticallySubsumed Φ U ∧ Q U ∧ E.IsClosed U := by
  classical
  have main : ∀ n : ℕ, ∀ U : TransitionForm Clock Var, rank U = n → Q U →
      ∃ V, SyntacticallySubsumed U V ∧ Q V ∧ E.IsClosed V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hn hU
      by_cases hc : E.IsClosed U
      · exact ⟨U, SyntacticallySubsumed.refl U, hU, hc⟩
      · obtain ⟨V, huv, hV, hlt⟩ := step U hU hc
        obtain ⟨W, hvw, hW, hcW⟩ := ih (rank V) (by omega) V rfl hV
        exact ⟨W, huv.trans hvw, hW, hcW⟩
  exact main (rank Φ) Φ rfl hq

/-- The bounded minimalization theorem yields a literal minimal closure.
The downward property premise is separate from the local decreasing step;
neither premise assumes that a closure already exists. -/
theorem minimal_closure_of_decreasing_step
    (E : ClosureCatalogue Clock Var) (rank : TransitionForm Clock Var → ℕ)
    (Q : TransitionForm Clock Var → Prop)
    (step : ∀ U, Q U → ¬ E.IsClosed U →
      ∃ V, SyntacticallySubsumed U V ∧ Q V ∧ rank V < rank U)
    (Φ : TransitionForm Clock Var) (hq : Q Φ)
    (down : ∀ U V, SyntacticallySubsumed Φ V → SyntacticallySubsumed V U → Q U → Q V) :
    ∃ V, E.IsClosure Φ V ∧ Q V := by
  obtain ⟨U, hΦU, hU, hcU⟩ := E.closed_extension_of_decreasing_step rank Q step Φ hq
  obtain ⟨V, hV, hVU⟩ := E.exists_minimal_closed_extension_below hΦU hcU
  exact ⟨V, hV, down U V hV.extension hVU hU⟩

end STLTableau.Section3.ClosureCatalogue
