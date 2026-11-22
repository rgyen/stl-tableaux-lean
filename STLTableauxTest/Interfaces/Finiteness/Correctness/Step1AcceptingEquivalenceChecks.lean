import STLTableaux.Finiteness.Correctness.Step1AcceptingEquivalence

/-! Checks the accepting-path correspondence for the auxiliary derivation
tableau, including the use of the original generator-path result (Lemma
4.33) to construct a satisfied run. -/
open STLTableau.Section4.Finiteness
#check formula_of_satisfied_derives_run
#check original_satisfied_run_of_formula
#check step1_satisfied_accepting_iff
#print axioms formula_of_satisfied_derives_run
#print axioms original_satisfied_run_of_formula
#print axioms step1_satisfied_accepting_iff

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``formula_of_satisfied_derives_run, ``original_satisfied_run_of_formula,
      ``step1_satisfied_accepting_iff] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
