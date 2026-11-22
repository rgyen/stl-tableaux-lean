import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness
import STLTableaux.Automata.Recognition.TableauSignalProjection

/-! A counterexample when falsity is allowed as an input to the translation.
The false-root tableau has an initial final mode with a vacuous numerical
invariant and admits a positive flow. The normalized input grammar excludes
falsity. -/
namespace STLTableau.Section4.Finiteness.FalseLabelDiagnostic
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

def source : Section3.StateForm Clock Var := .ofLocal (.predicate (.plain Formula.falsity))
def form : Section3.TransitionForm Clock Var := .ofState source

omit [Infinite Clock] in
theorem derives : Derives (source (Clock := Clock) (Var := Var)) form := by
  have hp : (form (Clock := Clock) (Var := Var)).atomicProjection = form := by
    apply DerivationNormalization.projection_eq_self
    intro l hl
    have he : l = .predicate (.plain Formula.falsity) := hl
    subst l
    trivial
  exact .resolved (.leaf (.atomic (.plain Formula.falsity) trivial))
    (.predicate _) (.predicate _) (hp.symm ▸ SafeNormalization.predicate _)

theorem within (X : Set Var) :
    form (Clock := Clock) ∈ (finiteRootTableau X (Formula.falsity : Formula Var)).states := by
  classical
  refine ⟨⟨source, derives⟩, ?_⟩
  constructor
  · refine ⟨?_, Set.empty_subset _, ?_⟩
    · intro l hl
      have he : l = .predicate (.plain Formula.falsity) := hl
      subst l
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨Formula.falsity,
        Finiteness.root_mem_rootPlainFormulas _, rfl⟩
    · intro c a he
      change (none : Option NNReal) = some a at he
      cases he
  · intro N he
    change (none : Option (Section3.StateForm Clock Var)) = some N at he
    cases he

theorem initial (X : Set Var) :
    (JudgementTableau.incoming (form (Var := Var)), form (Clock := Clock)) ∈
      (finiteRootTableau X (Formula.falsity : Formula Var)).initial :=
  ⟨⟨derives, rfl⟩, within X⟩

theorem final (X : Set Var) :
    form (Clock := Clock) ∈ (finiteRootTableau X (Formula.falsity : Formula Var)).final :=
  ⟨rfl, within X⟩

theorem labelled_false (X : Set Var) :
    Local.predicate (.plain Formula.falsity) ∈
      (finiteRootTableau X (Formula.falsity : Formula Var)).label (form (Clock := Clock)) :=
  ⟨rfl, trivial⟩

theorem base_invariant (X : Set Var)
    (h : (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).TranslationReady)
    (v : (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).HAVar → ℝ) :
    (⟨form, within X⟩, v) ∈
      ((finiteRootTableau X (Formula.falsity : Formula Var)).baseAutomaton h).invariant := by
  intro a ha
  have he : Local.predicate (.plain (.atom a)) =
      (Local.predicate (.plain Formula.falsity) : Local Clock Var) := ha.1
  cases he

def signal (X : Set Var) :
    FiniteSignal (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).HAVar :=
  ⟨1, by norm_num, fun t _ => t.val⟩

def state (X : Set Var)
    (h : (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).TranslationReady)
    (t : ℝ) (ht : t ≤ 1) :
    ((finiteRootTableau X (Formula.falsity : Formula Var)).toAutomaton h 1
      (by norm_num)).State :=
  ⟨(⟨form, within X⟩, fun _ => t), base_invariant X h _, fun _ => ht⟩

def execution (X : Set Var)
    (h : (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).TranslationReady) :
    ((finiteRootTableau X (Formula.falsity : Formula Var)).toAutomaton h 1
      (by norm_num)).Execution (signal X) where
  count := 1
  nonempty := by decide
  initialState := state X h 0 (by norm_num)
  initial_signal_eq := rfl
  initial_mem := by
    refine ⟨JudgementTableau.incoming (form (Var := Var)), initial X, (fun _ => 0), ?_, ?_⟩
    · intro g hg
      exact hg.elim
    · funext x
      cases x with
      | inl => rfl
      | inr x => cases x <;> rfl
  start := fun _ => state X h 0 (by norm_num)
  finish := fun _ => state X h 1 le_rfl
  boundary := fun i => (i.val : ℝ)
  first_zero := by norm_num
  increasing := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 1
  duration_eq := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    norm_num
  curve := fun _ t _ => t.val
  continuousStep := by
    intro i
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro t
    exact ⟨⟨fun _ => (zero_add _).symm, (zero_add _).symm⟩,
      base_invariant X h _, fun _ => t.property.2⟩
  initialSteps := .refl
  discreteSteps := by intro i hi; have := i.isLt; omega
  finalState := state X h 1 le_rfl
  finalSteps := .refl
  final_signal_eq := by
    intro t ht
    have hlt := t.property.2
    change t.val < 1 at hlt
    change t.val = ((1 : ℕ) : ℝ) at ht
    norm_num at ht
    linarith
  signal_eq := by
    intro i t ht _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    funext x
    simp [signal]

theorem reaches_false_goal (X : Set Var)
    (h : (finiteRootTableau (Clock := Clock) X (Formula.falsity : Formula Var)).TranslationReady) :
    ((finiteRootTableau X (Formula.falsity : Formula Var)).toAutomaton h 1
      (by norm_num)).Reaches (signal X)
      (finiteRootTableau X (Formula.falsity : Formula Var)).goalModes := by
  refine ⟨execution X h, ?_⟩
  exact final (Clock := Clock) X

def originalSignal : FiniteSignal Var := ⟨1, by norm_num, fun t _ => t.val⟩

theorem canonical_reaches_false :
    (finiteRootTableau (Clock := Clock) (rootVariables (Formula.falsity : Formula Var))
      Formula.falsity).ReachesSignal
      (finiteRootTableau_translationReady _ (Finset.finite_toSet _) _ (fun _ hx => hx))
      (originalSignal (Var := Var)) := by
  refine ⟨signal _, ⟨rfl, ?_⟩, reaches_false_goal _ _⟩
  intro t u he x
  exact he

theorem original_false_not_satisfied :
    ¬ (originalSignal (Var := Var)).Satisfies Formula.falsity ⟨0, by norm_num [originalSignal]⟩ :=
  FiniteSignal.not_satisfies_falsity _ _

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``derives, ``within, ``initial, ``final, ``labelled_false, ``base_invariant,
      ``execution, ``reaches_false_goal, ``canonical_reaches_false,
      ``original_false_not_satisfied] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

end STLTableau.Section4.Finiteness.FalseLabelDiagnostic
