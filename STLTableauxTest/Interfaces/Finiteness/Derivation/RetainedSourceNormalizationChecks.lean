import STLTableaux.Finiteness.Derivation.RetainedSourceNormalization

open STLTableau.Section4.Finiteness
#check retainedSource_compatible
#check SafeNormalization.retain_source
#check retainedSource_projection
#check retainedSource_invariant
#check retainedSource_holds
#check assemble_expandCtx
#check assemble_expandSolo
#print axioms retainedSource_compatible
#print axioms retainedSource_invariant
#print axioms assemble_expandCtx
#print axioms assemble_expandSolo

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``retainedSource_compatible, ``SafeNormalization.retain_source,
      ``retainedSource_projection, ``retainedSource_invariant, ``retainedSource_holds,
      ``assemble_expandCtx, ``assemble_expandSolo] do
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
