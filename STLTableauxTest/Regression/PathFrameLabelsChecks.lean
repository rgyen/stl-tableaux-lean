import STLTableaux.Automata.Recognition.PathFrameLabels

open STLTableau STLTableau.Section4

#check Path.frameAt_locals_property
#check Path.frameAt_locals_keepAtomic
#check Path.frameAt_locals_of_allStates

-- Atomicity is inherited even for a path not supplied with validity evidence.
example {Clock Var State : Type*} (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) (incoming : EdgeLabel Clock) (s : State)
    (l : STLTableau.Section3.Local Clock Var) (hl : l ∈ T.label s) :
    STLTableau.Section3.TransitionForm.KeepAtomic l := by
  exact Path.frameAt_locals_keepAtomic T hf (.last incoming s)
    ⟨0, by simp [Path.trace, Trace.length]⟩ l hl

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Path.frameAt_locals_property, ``Path.frameAt_locals_keepAtomic,
      ``Path.frameAt_locals_of_allStates] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
