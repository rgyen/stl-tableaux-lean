import STLTableaux.Automata.Translation.PrelimTableauAutomata

/-! Continuous transitions of `prelimAutomaton` can be restricted and
concatenated. Its clocks advance at rate one and its endpoint marker
stays fixed during each transition. -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)

theorem prelim_flow_add (q : T.states) (v v₁ v₂ : T.TypedVar → ℝ) (r s : NNReal)
    (first : (T.prelimAutomaton h τ).flow (q, v) r v₁)
    (second : (T.prelimAutomaton h τ).flow (q, v₁) s v₂) :
    (T.prelimAutomaton h τ).flow (q, v) (r + s) v₂ := by
  rcases first with ⟨fc, fg, fd, fb⟩
  rcases second with ⟨sc, sg, sd, sb⟩
  dsimp only [Prod.snd] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only [Prod.snd]
    rw [sc c, fc c]
    push_cast
    ring
  · dsimp only [Prod.snd]
    rw [sg, fg]
    push_cast
    ring
  · dsimp only [Prod.snd]
    rw [sd, fd]
    push_cast
    ring
  · exact sb.trans fb

theorem prelim_flow_rebase (q : T.states) (v v₁ v₂ : T.TypedVar → ℝ) (r s : NNReal)
    (first : (T.prelimAutomaton h τ).flow (q, v) r v₁)
    (total : (T.prelimAutomaton h τ).flow (q, v) (r + s) v₂) :
    (T.prelimAutomaton h τ).flow (q, v₁) s v₂ := by
  rcases first with ⟨fc, fg, fd, fb⟩
  rcases total with ⟨tc, tg, td, tb⟩
  dsimp only [Prod.snd] at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    dsimp only [Prod.snd]
    rw [tc c, fc c]
    push_cast
    ring
  · dsimp only [Prod.snd]
    rw [tg, fg]
    push_cast
    ring
  · dsimp only [Prod.snd]
    rw [td, fd]
    push_cast
    ring
  · exact tb.trans fb.symm

theorem prelim_flow_zero (q : T.states) (v : T.TypedVar → ℝ) :
    (T.prelimAutomaton h τ).flow (q, v) 0 v := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro c
    simp
  · simp
  · simp

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``prelim_flow_add, ``prelim_flow_rebase, ``prelim_flow_zero] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Tableau
