import STLTableaux.Automata.Recognition.ResetAgreement

open STLTableau STLTableau.Section4

/-- With one old clock, resetting it erases arbitrary differences in that
coordinate; non-clock coordinates still have to agree. -/
theorem single_clock_reset_erases_difference {Var State : Type*}
    (T : Tableau Unit Var State) (v w : T.HAVar → ℝ)
    (hx : ∀ x : T.realVariables, v (.inl x) = w (.inl x))
    (hg : v T.globalClock = w T.globalClock) :
    T.reset (ClockResetSet.singleton () 0) v = T.reset (ClockResetSet.singleton () 0) w := by
  apply T.reset_eq_of_agree_off_resets _ v w hx hg
  intro c hc
  have he : (ClockResetSet.singleton () 0).value c.val = some 0 := by
    cases c.val
    simp [ClockResetSet.singleton]
  rw [he] at hc
  cases hc

/-- Equal post-reset values do not justify moving a guard across that reset.
The last incoming guard must still be checked at the shortcut source. -/
theorem reset_equality_does_not_preserve_guard :
    Tableau.realComparison .ge (1 : ℝ) 1 ∧
    ¬ Tableau.realComparison .ge (0 : ℝ) 1 := by
  norm_num [Tableau.realComparison]

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tableau.reset_eq_of_agree_off_resets, ``Tableau.guardsHold_of_agree,
      ``single_clock_reset_erases_difference, ``reset_equality_does_not_preserve_guard] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
