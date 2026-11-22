import STLTableaux.ModelChecking.Reduction.CanonicalModelChecking

/-! Construction and projection of a synchronized goal on a system with one
positive flow. The tableau input is
an atom satisfied at time zero. -/
namespace CanonicalModelCheckingChecks
open STLTableau STLTableau.HybridAutomaton
open STLTableau.Section4 STLTableau.Section4.Finiteness

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := {s | s.2 () = 1}
  invariant := Set.univ
  flow := fun s _ v => v = s.2
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total; exact total.trans first.symm)
    (by intro q v a b r s first next; exact next.trans first)
  jump := fun _ _ _ => False

def σ : FiniteSignal Unit := ⟨1,by norm_num,fun _ _ => 1⟩
def point : H.State := ⟨((),fun _ => 1),Set.mem_univ _⟩

def execution : H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := point
  initial_mem := rfl
  start := fun _ => point
  finish := fun _ => point
  boundary := fun i => i.val
  first_zero := by norm_num
  increasing := by
    intro i j h
    change i.val < j.val at h
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast h
  last_le_horizon := by norm_num [σ]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ _ _ => 1
  continuousStep := fun _ => ⟨rfl,rfl,rfl,fun _ => ⟨rfl,Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  signal_eq := fun _ _ _ => rfl

def atom : AtomicProposition Unit := ⟨1,fun _ => (),fun v => v 0,.ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom atom,.atom atom⟩

theorem covers_horizon : execution.ReachesHorizon := by
  change ((1 : ℕ) : ℝ) = 1
  norm_num

theorem only_atom (a : AtomicProposition Unit)
    (ha : Formula.IsSubformula (.atom a) root.val) : a = atom := by
  change Formula.IsSubformula (.atom a) (.atom atom) at ha
  cases ha
  rfl

theorem finite_variability : σ.HasFiniteVariability root.val := by
  refine ⟨execution.fullFlowPartition covers_horizon,?_⟩
  intro i ψ sub
  change Formula.IsSubformula ψ (.atom atom) at sub
  cases sub
  intro u v hu hv
  rfl

private def window : TimeInterval := .bounded ⟨0, 1, le_rfl, zero_lt_one⟩
private def strictAtom : AtomicProposition Unit := { atom with relation := .lt }
private def raw : Formula Unit := Formula.eventually window (.atom strictAtom)

private theorem raw_finite_variability : σ.HasFiniteVariability raw := by
  have false_at (t : σ.Time) : ¬ σ.Satisfies raw t := by
    intro truth
    obtain ⟨_, _, bad⟩ := (σ.satisfies_eventually_iff window (.atom strictAtom) t).1 truth
    change (1 : ℝ) < 0 at bad
    norm_num at bad
  refine ⟨execution.fullFlowPartition covers_horizon, ?_⟩
  intro i ψ sub
  change Formula.IsSubformula ψ (.until window .truth (.atom strictAtom)) at sub
  cases sub with
  | refl =>
    intro u v _ _
    exact iff_of_false (false_at u) (false_at v)
  | until_left sub => cases sub; intro u v _ _; rfl
  | until_right sub => cases sub; intro u v _ _; rfl

private theorem normalized_counter_eq :
    (Formula.neg raw).normalizeForTableau = Formula.always window (.atom atom) := rfl

/-- The normalized negation of `◇[I] φ` with bounded `I` and a strict atom
is an always formula with a non-strict atom. Finite variability is
assumed for the original formula. -/
theorem normalized_counter_finite_variability :
    σ.HasFiniteVariability (Formula.neg raw).normalizeForTableau := by
  apply raw_finite_variability.normalizeViolation
  · rw [normalized_counter_eq]
    exact .always window (.atom atom)
  · intro a sub
    rw [normalized_counter_eq] at sub
    change Formula.IsSubformula (.atom a) (.neg (.until window .truth (.neg (.atom atom)))) at sub
    cases sub with
    | neg h =>
      cases h with
      | until_left h => cases h
      | until_right h =>
        cases h with
        | neg h => cases h; rfl

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ hg
  have same : γ = fun _ => γ ⟨0,by simp⟩ :=
    funext fun t => (hg t).1
  rw [same]
  exact continuous_const

local notation "X" => (Set.univ : Set Unit)
local notation "T" => finiteTableau (Clock := Nat) X root.val
local notation "h" => canonicalReady (Clock := Nat) X root Set.finite_univ (by simp)

open IntervalPartition in
private noncomputable def rightClosedPartition : IntervalPartition σ.domain := by
  let times : Fin 3 → ℝ := ![0, 1 / 2, 1]
  let markers : Fin 3 → Marker := ![●, ○, ●]
  have monotone : Monotone times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [times, Fin.le_iff_val_le_val] at *
  have compatible : SingletonCompatible times markers := by
    intro i hi
    fin_cases i <;> norm_num [times] at hi
  exact ofSingletonBoundaries times monotone markers compatible rfl rfl

/-- The pieces are [0, 1/2] and (1/2, 1), so the open left endpoint of
    the second piece does not follow a singleton. -/
theorem rightClosedPartition_not_canonical :
    ¬ Tableau.CanonicalBoundaryForms σ rightClosedPartition := by
  intro form
  have bad := form ⟨0, by decide⟩
  change Marker.open = (if (0 : ℝ) = 1 / 2 then Marker.open else Marker.closed) at bad
  norm_num at bad
  cases bad

theorem rightClosedPartition_recognizes :
    (T).recognizes Generated.labels_finite σ rightClosedPartition := by
  have stable : σ.StablePartition root.val rightClosedPartition := by
    intro i ψ sub
    change Formula.IsSubformula ψ (.atom atom) at sub
    cases sub
    intro u v hu hv
    rfl
  apply (finiteTableau_recognizes_normalized_input X root σ rightClosedPartition stable).2
  change (1 : ℝ) ≥ 0
  norm_num

theorem forward_from_rightClosedPartition :
    ∃ aug : FiniteSignal (T).HAVar,
      aug.reindex (Sum.inl : (T).realVariables → (T).HAVar) = σ.reindex Subtype.val ∧
      ((T).canonicalAutomaton h σ.horizon).PrelimReachesStateOrFinalJump aug
        ((T).canonicalGoal h σ.horizon) := by
  have continuous : SignalAtomRightContinuous σ root.val := by
    intro a ha t
    rw [only_atom a ha]
    change ContinuousWithinAt (fun _ : σ.Time => (1 : ℝ)) (Set.Ici t) t
    exact continuousWithinAt_const
  exact (canonical_translation_correctness (Clock := Nat) X root Set.finite_univ
    (by simp) (by intro a ha; rw [only_atom a ha]; rfl) σ).1
    continuous rightClosedPartition rightClosedPartition_recognizes

def singletonSignal : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => -(t : ℝ)⟩

open IntervalPartition in
private noncomputable def singletonPartition : IntervalPartition singletonSignal.domain := by
  let times : Fin 3 → ℝ := ![0, 0, 1]
  let markers : Fin 3 → Marker := ![●, ○, ●]
  have monotone : Monotone times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [times, Fin.le_iff_val_le_val] at *
  have compatible : SingletonCompatible times markers := by
    intro i hi
    fin_cases i <;> norm_num [times, markers] at *
  exact ofSingletonBoundaries times monotone markers compatible rfl rfl

private theorem singletonAtom_iff (t : singletonSignal.Time) :
    singletonSignal.Satisfies root.val t ↔ t.val = 0 := by
  change -(t : ℝ) ≥ 0 ↔ t.val = 0
  have nonneg := t.property.1
  constructor <;> intro hh <;> linarith

/-- The atom is true only at the first singleton. The translated run can
reach that goal and then flow in the empty continuation mode. -/
theorem goal_reached_from_singleton :
    ∃ aug : FiniteSignal (T).HAVar,
      aug.reindex (Sum.inl : (T).realVariables → (T).HAVar) = singletonSignal.reindex Subtype.val ∧
      ((T).canonicalAutomaton h singletonSignal.horizon).PrelimReachesStateOrFinalJump aug
        ((T).canonicalGoal h singletonSignal.horizon) := by
  have stable : singletonSignal.StablePartition root.val singletonPartition := by
    intro i ψ sub
    change Formula.IsSubformula ψ (.atom atom) at sub
    cases sub
    intro u v hu hv
    change singletonSignal.Satisfies root.val u ↔ singletonSignal.Satisfies root.val v
    rw [singletonAtom_iff, singletonAtom_iff]
    fin_cases i
    · have u0 : u.val ≤ 0 := (markedLT_closed _ _).1 (MarkedInterval.mem_iff.mp hu).2
      have v0 : v.val ≤ 0 := (markedLT_closed _ _).1 (MarkedInterval.mem_iff.mp hv).2
      exact iff_of_true (le_antisymm u0 u.property.1) (le_antisymm v0 v.property.1)
    · have u0 : 0 < u.val := (markedLT_open _ _).1 (MarkedInterval.mem_iff.mp hu).1
      have v0 : 0 < v.val := (markedLT_open _ _).1 (MarkedInterval.mem_iff.mp hv).1
      exact iff_of_false (ne_of_gt u0) (ne_of_gt v0)
  have recognized : (T).recognizes Generated.labels_finite singletonSignal singletonPartition :=
    (finiteTableau_recognizes_normalized_input X root singletonSignal singletonPartition stable).2
      ((singletonAtom_iff _).2 rfl)
  have cont : SignalAtomRightContinuous singletonSignal root.val := by
    intro a ha t
    rw [only_atom a ha]
    change ContinuousWithinAt (fun u : singletonSignal.Time => -(u : ℝ)) (Set.Ici t) t
    exact continuous_subtype_val.neg.continuousWithinAt
  exact (canonical_translation_correctness (Clock := Nat) X root Set.finite_univ
    (by simp) (by intro a ha; rw [only_atom a ha]; rfl) singletonSignal).1
    cont singletonPartition recognized

theorem goal_reached : (T).CanonicalReaches (H.boundedZeroTimeExtension 1) h σ := by
  apply canonical_goal_of_formula (Clock := Nat) X root H Set.finite_univ (by simp)
    (by intro a ha; rw [only_atom a ha]; rfl)
    (by intro a ha; rw [only_atom a ha]; exact continuous_apply (0 : Fin 1))
    σ execution covers_horizon rfl 1
    (by intro i hi; have := i.isLt; change i.val < 1 at this; change i.val+1 < 1 at hi; omega)
    continuous_flows finite_variability
  change (1 : ℝ) ≥ 0
  norm_num

theorem actual_product_prefix :
    ∃ aug : FiniteSignal (T).CanonicalCompositionVar,
      aug.reindex (T).canonicalSystemCoordinate = σ ∧
      ((T).canonicalProduct (H.boundedZeroTimeExtension 1) h σ.horizon).PrelimReachesStateOrFinalJump aug
        ((T).canonicalProductGoal (H.boundedZeroTimeExtension 1) h σ.horizon) :=
  Tableau.CanonicalReaches.existsProductPrefix goal_reached

theorem goal_gives_original_trajectory : H.IsPrelimTrajectory σ :=
  (canonical_bounded_goal_formula (Clock := Nat) X root H 1 Set.finite_univ (by simp)
    (by intro a ha; rw [only_atom a ha]; rfl) σ goal_reached).1

run_elab do
  for decl in #[``rightClosedPartition_not_canonical, ``rightClosedPartition_recognizes,
      ``forward_from_rightClosedPartition, ``goal_reached_from_singleton, ``goal_reached,
      ``actual_product_prefix,
      ``goal_gives_original_trajectory, ``normalized_counter_finite_variability] do
    for ax in ← Lean.collectAxioms decl do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{decl} uses unexpected axiom {ax}"

set_option maxHeartbeats 0 in
run_elab do
  let env := (← Lean.getEnv).checked.get
  let old : Lean.Name := ``STLTableau.Section4.Finiteness.Derives
  for root in #[``canonical_translation_correctness, ``canonical_model_checking,
      ``canonical_robust_model_checking] do
    let mut seen : Lean.NameSet := {}
    let mut todo := #[root]
    while let some n := todo.back? do
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if old.isPrefixOf n then
        throwError "{root} depends on the former tableau: {n}"
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          todo := todo.push d
    unless seen.contains ``CompletedDerivation.Admitted do
      throwError "{root} no longer uses the Section 4 tableau"

end CanonicalModelCheckingChecks
