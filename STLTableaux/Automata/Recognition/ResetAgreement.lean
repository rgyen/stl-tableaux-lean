import STLTableaux.Automata.Recognition.TableauSignalProjection

/-! A final reset can erase earlier clock differences, but never excuses a
guard mismatch: guards are evaluated BEFORE that reset. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

theorem reset_eq_of_agree_off_resets (Λ : ClockResetSet Clock)
    (v w : T.HAVar → ℝ)
    (hx : ∀ x : T.realVariables, v (.inl x) = w (.inl x))
    (hg : v T.globalClock = w T.globalClock)
    (hc : ∀ c : T.clocks, Λ.value c.val = none →
      v (.inr (.inl c)) = w (.inr (.inl c))) : T.reset Λ v = T.reset Λ w := by
  funext x
  cases x with
  | inl x => exact hx x
  | inr x =>
    cases x with
    | inl c =>
      cases he : Λ.value c.val with
      | none => simpa only [reset, he] using hc c he
      | some a => simp only [reset, he]
    | inr u => cases u; exact hg

theorem guardsHold_of_agree (l : EdgeLabel Clock) (v w : T.HAVar → ℝ)
    (hw : T.guardsHold l w)
    (ha : ∀ g ∈ l.guards, ∀ hc : g.clock ∈ T.clocks,
      v (.inr (.inl ⟨g.clock, hc⟩)) = w (.inr (.inl ⟨g.clock, hc⟩))) :
    T.guardsHold l v := by
  intro g hg
  obtain ⟨hc, hcmp⟩ := hw g hg
  exact ⟨hc, by rw [ha g hg hc]; exact hcmp⟩

end STLTableau.Section4.Tableau
