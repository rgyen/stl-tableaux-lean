import STLTableaux.Automata.Composition.ParallelComposition

namespace ParallelCompositionChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton Bool Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {(false, (), true)}
  initial := Set.univ
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.constant _
  jump := fun _ _ _ => True

def s (a b : Bool) : (H.parallel H).State :=
  ⟨((a, b), fun _ => 0), Set.mem_univ _, Set.mem_univ _⟩

theorem left_only : (H.parallel H).DiscreteStep (s false false) (s true false) := by
  let e : (Bool × Bool) × (Option Unit × Option Unit) × (Bool × Bool) :=
    ((false, false), (some (), none), (true, false))
  have he : e ∈ (H.parallel H).edge := ⟨by decide, rfl, rfl⟩
  let old : {e // e ∈ H.edge} := ⟨(false, (), true), rfl⟩
  exact ⟨⟨e, he⟩, rfl, rfl, ⟨old, rfl, trivial⟩, rfl⟩

theorem simultaneous : (H.parallel H).DiscreteStep (s false false) (s true true) := by
  let e : (Bool × Bool) × (Option Unit × Option Unit) × (Bool × Bool) :=
    ((false, false), (some (), some ()), (true, true))
  have he : e ∈ (H.parallel H).edge := ⟨by decide, rfl, rfl⟩
  let old : {e // e ∈ H.edge} := ⟨(false, (), true), rfl⟩
  exact ⟨⟨e, he⟩, rfl, rfl, ⟨old, rfl, trivial⟩, ⟨old, rfl, trivial⟩⟩

example : H.rightState H (s false false) = H.rightState H (s true false) := rfl

example : ¬ ((false, false), (none, none), (false, false)) ∈ (H.parallel H).edge := by
  rintro ⟨hn, _⟩
  exact hn rfl

example : ¬ ((false, false), (some (), none), (true, true)) ∈ (H.parallel H).edge := by
  rintro ⟨_, _, idle⟩
  cases idle

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``left_only, ``simultaneous] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"
end ParallelCompositionChecks
