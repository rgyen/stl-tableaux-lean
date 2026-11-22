import STLTableaux.Automata.Composition.SystemTableauJumpLift
import STLTableaux.Automata.Recognition.EmptyContinuationRecognition
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition

/-! A positive-time SYSTEM reset synchronizes with an actual finite-tableau
edge. The source closed-flow endpoint differs from the boundary observation;
this is one actual boundary jump, not a whole-run or goal theorem. -/
namespace SystemTableauBoundaryJumpChecks
open STLTableau STLTableau.HybridAutomaton
open STLTableau.Section4 STLTableau.Section4.Finiteness
open Section3

def p : AtomicProposition Unit := ⟨1, fun _ => (), fun v => v 0, .ge⟩
def root : Formula.NormalizedInput Unit := ⟨.atom p, .atom p⟩
noncomputable def T := withEmptyContinuation (Clock := Nat) Set.univ root
theorem ready : T.TranslationReady :=
  withEmptyContinuation_ready _ _
    (finiteRootTableau_translationReady Set.univ Set.finite_univ root.val (by simp))
def S : Section3.StateForm Nat Unit := .ofLocal (.predicate (.plain (.atom p)))
def Q : Section3.TransitionForm Nat Unit := .ofState S
def l0 : EdgeLabel Nat := JudgementTableau.incoming Q

theorem derives : Derives S Q := by
  have norm : SafeNormalization (.predicate (.plain (.atom p))) Q := .predicate _
  have proj : Q.atomicProjection = Q := by
    have locals : {l ∈ S.locals | Section3.TransitionForm.KeepAtomic l} = S.locals := by
      ext l
      constructor
      · exact And.left
      · intro h
        refine ⟨h, ?_⟩
        have same : l = Local.predicate (.plain (.atom p)) := h
        subst l
        trivial
    unfold Section3.TransitionForm.atomicProjection Section3.TransitionForm.restrictCurrent Q
    simp only [Section3.TransitionForm.ofState, locals]
  apply Derives.resolved (Resolve.leaf (ResolutionLeaf.atomic (.plain (.atom p)) trivial)) norm norm
  rw [proj]
  exact norm

theorem inventory : FiniteInventory.TransitionWithin
    (FiniteInventory.locals (Finiteness.rootPlainFormulas root.val)
      (rootSlotTriples (Clock := Nat) root.val))
    (FiniteInventory.guards (rootSlotTriples (Clock := Nat) root.val))
    (FiniteInventory.resets (rootSlotTriples (Clock := Nat) root.val)) Q := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro l hl
      change l = .predicate (.plain (.atom p)) at hl
      subst l
      classical
      simp [FiniteInventory.locals, Finiteness.rootPlainFormulas, root]
    · intro g hg; exact hg.elim
    · intro c a h; cases h
  · intro N h; cases h

theorem original_initial : (l0, Q) ∈ T.initial :=
  ⟨⟨derives, rfl⟩, ⟨⟨S, derives⟩, inventory⟩⟩
def q0 : T.states := ⟨Q, ready.initial_states _ original_initial⟩
def q1 : T.states := ⟨emptyMode, Or.inl rfl⟩
theorem source_has_atom : Local.predicate (.plain (.atom p)) ∈ T.label q0.val :=
  ⟨rfl, trivial⟩

theorem original_final : Q ∈ (inputTableau (Clock := Nat) Set.univ root).final :=
  ⟨rfl, ⟨⟨S, derives⟩, inventory⟩⟩

theorem original_edge : (q0.val, emptyIncoming, q1.val) ∈ T.edges := by
  apply final_empty_edge Set.univ root Q original_final
  intro h
  have := congrArg (fun F : Section3.TransitionForm Nat Unit => F.current.locals) h
  have atom : Local.predicate (.plain (.atom p)) ∈ Q.current.locals := rfl
  rw [this] at atom
  exact atom.elim

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := {((), (), ())}
  initial := {s | s.2 () = 0}
  invariant := Set.univ
  flow := fun s t v => ∀ x, v x = s.2 x + t
  trajectory_closed := HybridFlow.Closed.of_rebase_add _ _
    (by intro q v a b r s first total x
        dsimp only [Prod.snd] at *
        rw [total x, first x]; push_cast; ring)
    (by intro q v a b r s first second x
        dsimp only [Prod.snd] at *
        rw [second x, first x]; push_cast; ring)
  jump := fun _ s s' => s.2 () = 1 ∧ s'.2 () = 2

def state (n : ℝ) : H.State := ⟨((), fun _ => n), Set.mem_univ _⟩
noncomputable def σ : FiniteSignal Unit :=
  ⟨2, by norm_num, fun t _ => if t.val < 1 then t.val else t.val + 1⟩

noncomputable def f : ObservedFlow H σ where
  start := state 0
  finish := state 1
  beginTime := 0
  endTime := 1
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t _ => t.val
  step := ⟨rfl, rfl, rfl, fun _ => ⟨fun _ => by simp [state]; rfl, Set.mem_univ _⟩⟩
  observe := by
    intro t ht
    funext x
    simp [σ, if_pos ht.2]

noncomputable def g : ObservedFlow H σ where
  start := state 2
  finish := state 3
  beginTime := 1
  endTime := 2
  duration := 1
  positive := by norm_num
  duration_eq := by norm_num
  curve := fun t _ => 2 + t.val
  step := ⟨rfl, by funext x; simp [state], by funext x; norm_num [state],
    fun t => ⟨fun _ => rfl, Set.mem_univ _⟩⟩
  observe := by
    intro t ht
    funext x
    change (if t.val < 1 then t.val else t.val + 1) = 2 + (t.val - 1)
    rw [if_neg (not_lt_of_ge ht.1)]
    ring

theorem continuous_flows : H.ContinuousFlows := by
  intro q r γ evolves
  apply continuous_pi
  intro x
  have same : (fun t => γ t x) = fun t => γ ⟨0, by simp⟩ x + t.val := by
    funext t
    exact (evolves t).1 x
  rw [same]
  exact continuous_const.add continuous_subtype_val

def bs : Fin 3 → ℝ := ![0, 1, 2]
def ms : Fin 3 → Marker := ![●, ●, ●]
def P : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; change i.val ≤ j.val at hij
        fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i <;> norm_num [ms, bs] at *) rfl rfl

theorem source_labels (β : ClockValuation Nat) : ∀ loc ∈ T.label q0.val,
    loc.holds σ P β ⟨0, by decide⟩ := by
  intro loc hl
  change loc ∈ JudgementTableau.labels Q at hl
  have same : loc = Local.predicate (.plain (.atom p)) := hl.1
  subst loc
  change ∀ t : σ.Time, t.val ∈ P.interval ⟨0, by decide⟩ →
    (if t.val < 1 then t.val else t.val + 1) ≥ 0
  intro t _
  split_ifs <;> linarith [t.property.1]

theorem empty_labels : T.label q1.val = ∅ := empty_label Set.univ root

/-- The actual reset occurs at positive time: the closed source endpoint is
1 although the boundary observation and following flow start are both 2. -/
theorem actual_positive_boundary_reset :
    ∃ b c : (T.systemTableauAutomaton H ready σ.horizon).State,
      (T.systemTableauAutomaton H ready σ.horizon).DiscreteStep b c ∧
      (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b).val.2 () = 1 ∧
      (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName c).val.2 () = 2 ∧
      σ.value (Section4.Tableau.pieceEntry σ P ⟨1, by decide⟩) () = 2 ∧
      (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b).val.2 () ≠
        σ.value (Section4.Tableau.pieceEntry σ P ⟨1, by decide⟩) () := by
  obtain ⟨a, b, left, right, entry, exit, flow⟩ :=
    T.systemTableau_flow_over_cell H ready f continuous_flows P ⟨0, by decide⟩
      rfl rfl q0 (fun _ => 0) (fun _ => 0) (source_labels _)
      (by intro a ha; have same : a = p := by
            have hp : Local.predicate (.plain (.atom a)) =
              Local.predicate (.plain (.atom p)) := ha.1
            cases hp; rfl
          subst a; rfl)
      (by intro a ha; have same : a = p := by
            have hp : Local.predicate (.plain (.atom a)) =
              Local.predicate (.plain (.atom p)) := ha.1
            cases hp; rfl
          subst a; exact continuous_apply (0 : Fin 1))
  have reset : H.DiscreteStep
      (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
        T.systemVarName T.tableauVarName b) g.start := by
    rw [right]
    exact ⟨⟨((), (), ()), rfl⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨c, lc, rc, jump⟩ := T.systemTableau_jump_after_cell H ready σ P
    ⟨0, by decide⟩ ⟨1, by decide⟩ rfl q0 q1 emptyIncoming original_edge
    (fun _ => 0) (f.curve ⟨0, by simp⟩)
    (fun x => f.curve ⟨f.duration, by simp⟩ x.val) b
    (by
      rw [exit]
      congr 1
      have duration : (STLTableau.Judgement.duration P ⟨0, by decide⟩ : ℝ) = 1 := by
        change (1 : ℝ) - 0 = 1
        norm_num
      rw [duration]
      rfl)
    (source_labels _) (by intro g hg; exact hg.elim)
    (by intro loc hl; rw [empty_labels] at hl; exact hl.elim)
    (by intro a ha; rw [empty_labels] at ha; exact ha.elim)
    g rfl (Or.inr reset)
  have pre : (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
      T.systemVarName T.tableauVarName b).val.2 () = 1 := by rw [right]; rfl
  have post : (H.leftStateOn (T.prelimAutomaton ready σ.horizon)
      T.systemVarName T.tableauVarName c).val.2 () = 2 := by rw [lc]; rfl
  have observed : σ.value (Section4.Tableau.pieceEntry σ P ⟨1, by decide⟩) () = 2 := by
    change (if (1 : ℝ) < 1 then 1 else 1 + 1) = 2
    norm_num
  exact ⟨b, c, jump, pre, post, observed, by rw [pre, observed]; norm_num⟩

run_elab do
  for name in #[``derives, ``inventory, ``original_initial, ``original_edge,
      ``continuous_flows, ``source_labels, ``actual_positive_boundary_reset] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end SystemTableauBoundaryJumpChecks
