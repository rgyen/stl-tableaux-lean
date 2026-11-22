import STLTableaux.Finiteness.Correctness.FiniteTableau

open STLTableau STLTableau.Section3 STLTableau.Section4.Finiteness
open STLTableau.Section4 (ClosureState)
open ResetTrimming
open STLTableau.Section4.Finiteness.LocalResetSupport
open scoped STL

namespace SimplifiedTableauChecks

private def nextGuard : STLTableau.Section3.StateForm Nat Unit :=
  STLTableau.Section3.StateForm.ofGuard ⟨0, .gt, 0⟩

private def currentResets : ClockResetSet Nat :=
  (ClockResetSet.singleton 0 2).union (ClockResetSet.singleton 1 3)

private def twoFrames : STLTableau.Section3.TransitionForm Nat Unit :=
  ⟨{ STLTableau.Section3.StateForm.empty with resets := currentResets }, some nextGuard⟩

-- Clock 0 is not used by any current local; only the successor guard needs it.
-- Clock 1 is genuinely dead across the two scopes.
example : (trim twoFrames).current.resets.value 0 = some 2 ∧
    (trim twoFrames).current.resets.value 1 = none := by
  classical
  have h0 : (0 : Nat) ∈ twoFrames.bodyFreeClocks := by
    exact Or.inr (Or.inl ⟨⟨0, .gt, 0⟩, rfl, rfl⟩)
  have h1 : (1 : Nat) ∉ twoFrames.bodyFreeClocks := by
    simp [twoFrames, nextGuard, STLTableau.Section3.TransitionForm.bodyFreeClocks,
      STLTableau.Section3.StateForm.empty, STLTableau.Section3.StateForm.ofGuard,
      STLTableau.Section3.StateForm.localClocks, STLTableau.Section3.StateForm.freeClocks,
      STLTableau.Section3.StateForm.guardClocks]
  change _ ∧ (restrictResets currentResets twoFrames.bodyFreeClocks).value 1 = none
  constructor
  · change (restrictResets currentResets twoFrames.bodyFreeClocks).value 0 = some 2
    simp only [restrictResets, if_pos h0]
    rfl
  · simp only [restrictResets, if_neg h1]

-- State guards are pre-reset reads and do not by themselves keep a same-frame reset.
example : (trimState
    { nextGuard with resets := ClockResetSet.singleton 0 2 }).resets.value 0 = none := by
  classical
  simp only [trimState, state, restrictResets]
  rw [if_neg]
  simp [nextGuard, STLTableau.Section3.StateForm.ofGuard, STLTableau.Section3.StateForm.localClocks]

example : (trim twoFrames).nextPart = some (trimState nextGuard) := by
  rw [trim_next]
  rfl

private def context : MixedJ Nat Unit := .marker .closed

example (ℓ : Marker) : Marker.disj (¬ₘ ℓ) ℓ = .closed := by
  cases ℓ <;> rfl

example : Marker.disj .open .open ≠ .closed := by decide

-- Both complementary boundary-marker orientations permit a weak comparison
-- when the left markers match.
example : CompletedDerivation.MergeGuard (ClockResetSet.singleton (0 : Nat) 0) 0
    (Marker.imp .open .open) context context ∧
    CompletedDerivation.MergeGuard (ClockResetSet.singleton (0 : Nat) 0) 0
      (Marker.imp .closed .closed) context context := by
  exact ⟨.closed context, .closed context⟩

-- The open comparison at a free clock becomes an actual strict guard.
example : CompletedDerivation.MergeGuard (ClockResetSet.empty (Clock := Nat)) 0
    (Marker.imp .closed .open) context (withBoundaryGuard 0 .open context) :=
  .free context rfl

-- The same open comparison on a reset clock is statically checked.
example : CompletedDerivation.MergeGuard (ClockResetSet.singleton (0 : Nat) 1) 0
    .open context context :=
  .fixed context 1 rfl (by norm_num)

example (K : MixedJ Nat Unit) :
    ¬ CompletedDerivation.MergeGuard (ClockResetSet.singleton (0 : Nat) 0) 0 .open context K := by
  intro h
  cases h with
  | fixed Γ v hv hpos =>
    have hzero : (0 : NNReal) = v := Option.some.inj hv
    subst v
    exact (lt_irrefl 0) hpos
  | free Γ hv => cases hv

-- Edges use the actual next input, not the stored generator of the target.
example {s t : ClosureState Nat Unit} {M root : STLTableau.Section3.StateForm Nat Unit}
    (hs : s ∈ (PairedTableau.tableau ∅ ∅ root CompletedDerivation.Admitted).states)
    (ht : t ∈ (PairedTableau.tableau ∅ ∅ root CompletedDerivation.Admitted).states)
    (hn : s.form.nextPart = some M) (hM : CompletedDerivation.Admitted M t.form)
    (hDifferent : t.generator ≠ M) :
    (s,t.incoming,t) ∈ (PairedTableau.tableau ∅ ∅ root CompletedDerivation.Admitted).edges ∧
      t.generator ≠ M :=
  ⟨⟨hs,ht,M,hn,hM,rfl⟩,hDifferent⟩

end SimplifiedTableauChecks

#check finiteTableau_bounded_accepting_path
#check finiteTableau_recognizes_normalized_input
#check finiteTableau_clock_card_le
#check finiteTableau_state_card_le

set_option maxHeartbeats 0 in
-- Traverse the imported proof bodies as well as the public declarations.
run_elab do
  let env := (← Lean.getEnv).checked.get
  let roots := #[``finiteTableau_bounded_accepting_path,
    ``simplified_satisfied_accepting_iff, ``simplified_fullTrace_and_formula_of_atomic,
    ``finiteTableau_recognizes_normalized_input,
    ``finiteTableau_clock_card_le,
    ``finiteTableau_state_card_le, ``finiteTableau_edges_finite]
  let forbidden : Lean.Name := ``STLTableau.Section4.Finiteness.Derives
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
    for ax in ← Lean.collectAxioms root do
      unless allowed.contains ax do
        throwError "{root} uses unapproved axiom {ax}"
  let mut seen : Lean.NameSet := {}
  let mut todo := roots
  while let some n := todo.back? do
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden.isPrefixOf n then
      throwError "C(M) public results depend on the older admission relation: {n}"
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet do
        todo := todo.push d
  unless seen.contains ``CompletedDerivation.Admitted do
    throwError
      "The Section 4 audit did not reach the actual completed-derivation admission relation"
