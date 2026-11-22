import STLTableaux
import STLTableaux.Compatibility
import STLTableauxTest.Axioms.FinitenessStoryChecks

/-! Audit every declaration loaded from the production library, independently
of the physical directory of its source module. -/
run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some mod := env.getModuleFor? name then
      if mod.toString == "STLTableaux" || "STLTableaux.".isPrefixOf mod.toString then
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do
            throwError "{name} depends on an unapproved axiom: {ax}"
        checked := checked + 1
  unless checked > 0 do
    throwError "No production declarations were audited"
  Lean.logInfo m!"Audited {checked} production declarations; only standard Lean axioms."
