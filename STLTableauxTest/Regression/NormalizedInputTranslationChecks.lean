import STLTableaux.Automata.Translation.NormalizedInputTranslation
import STLTableaux.ModelChecking.Preprocessing.NormalizedInputBranches

open STLTableau STLTableau.Section4.Finiteness

example : (Formula.truth : Formula Unit).NormalizedReady := .truth
example : ¬ (Formula.falsity : Formula Unit).NormalizedReady := Formula.not_normalizedReady_falsity

-- Derived encodings may contain negations internally and remain legal input.
example : (Formula.always (.unbounded 0) (.truth : Formula Unit)).NormalizedReady :=
  .always _ .truth
example : (Formula.or (.truth : Formula Unit) .truth).NormalizedReady := .or .truth .truth
example : (Formula.release (.unbounded 0) (.truth : Formula Unit) .truth).NormalizedReady :=
  .release .truth .truth

-- General preprocessing is deliberately not certified as the manuscript contract.
example : (Formula.falsity : Formula Unit).normalizeForTableau = Formula.falsity := rfl
example : ¬ (Formula.falsity : Formula Unit).normalizeForTableau.NormalizedReady :=
  Formula.not_normalizedReady_falsity

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Formula.NormalizedReady.mixedReady, ``Formula.not_normalizedReady_falsity,
      ``Formula.mixedReady_not_sufficient_for_normalizedReady,
      ``Formula.normalizedReady_and, ``Formula.normalizedReady_or, ``Formula.normalizedReady_until,
      ``Formula.normalizedReady_release, ``Formula.normalizedReady_eventually,
      ``Formula.normalizedReady_always,
      ``inputTableau, ``inputTableau_recognizes_iff, ``inputAutomaton,
      ``finite_branch_normalizedReady, ``infinite_branch_normalizedReady,
      ``RawBranch.normalizedReady,
      ``ACIdem.normalizedReady_iff, ``withBoundaryGuard_normalizedReady, ``Resolve.normalizedReady,
      ``normalizedReady_plain_not_false] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
