import STLTableaux.Automata.Execution.ZeroTimeShortcut

open STLTableau STLTableau.Section4
open STLTableau.Section4.Finiteness

-- Empty intervening resets suffice, without any equality of the two modes.
example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (incoming middle : EdgeLabel Clock) (F M : Section3.TransitionForm Clock Var)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (α β : ClockValuation Clock)
    (hr : (Path.step incoming F (.step middle M p)).run (finiteRootTableau X root))
    (ha : (Path.step incoming F (.step middle M p)).accepting (finiteRootTableau X root))
    (hn : F.nextPart = M.nextPart) (hempty : middle.resets = ClockResetSet.empty)
    (hg : (Path.step incoming F (.step middle M p)).JumpGuardsHold α β) :
    (Path.step incoming F p).run (finiteRootTableau X root) ∧
    (Path.step incoming F p).accepting (finiteRootTableau X root) ∧
    (Path.step incoming F p).JumpGuardsHold α β := by
  exact finiteRootTableau_drop_middle_guarded X root incoming middle F M p α β
    hr ha hn (by rw [hempty, ClockResetSet.apply_empty]) hg

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``finiteRootTableau_same_next_edge,
      ``finiteRootTableau_shortcut_jump, ``finiteRootTableau_shortcut_stationary_block,
      ``finiteRootTableau_shortcut_overwritten_block,
      ``finiteRootTableau_drop_middle_guarded] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
