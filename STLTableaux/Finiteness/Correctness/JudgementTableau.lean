import STLTableaux.Tableau.Construction.GeneratorPath
import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue

/-! A structural judgement-state tableau combinator and the forward original
path projection. Its graph definition has no semantic soundness field. The
relation R will be instantiated by the extended derivation relation separately.
No inverse path translation or Step 1 correctness theorem is asserted here. -/
namespace STLTableau.Section4.Finiteness.JudgementTableau
open Section3
variable {Clock Var : Type*}

def incoming (F : Section3.TransitionForm Clock Var) : EdgeLabel Clock :=
  ⟨F.current.guards,F.current.guards_finite,F.current.resets⟩

def labels (F : Section3.TransitionForm Clock Var) : Set (Local Clock Var) :=
  {l ∈ F.current.locals | Section3.TransitionForm.KeepAtomic l}

theorem labels_finite (F : Section3.TransitionForm Clock Var) : (labels F).Finite :=
  F.current.locals_finite.subset (fun _ h => h.1)

/-- R is purely a relation on actual input state forms and output judgements.
The initial relation starts at root; ordinary edges start at the literal next
state form. No generator is stored in a judgement state. -/
def tableau (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop) :
    Tableau Clock Var (Section3.TransitionForm Clock Var) where
  realVariables := X
  clocks := Q
  states := {F | ∃ N, R N F}
  edges := {e | (∃ M, R M e.1) ∧ (∃ M, R M e.2.2) ∧
    ∃ N, e.1.nextPart = some N ∧ R N e.2.2 ∧ e.2.1 = incoming e.2.2}
  initial := {e | R root e.2 ∧ e.1 = incoming e.2}
  final := {F | F.nextPart = none}
  label := labels
  label_atomic := fun _ _ h => h.2

/-- Forget only the stored generator; preserve each actual incoming edge label. -/
def forgetGenerator : Path Clock (ClosureState Clock Var) →
    Path Clock (Section3.TransitionForm Clock Var)
  | .last e s => .last e s.form
  | .step e s t => .step e s.form (forgetGenerator t)

theorem first_state (p : Path Clock (ClosureState Clock Var)) :
    (forgetGenerator p).firstState = p.firstState.form := by cases p <;> rfl

theorem first_incoming (p : Path Clock (ClosureState Clock Var)) :
    (forgetGenerator p).firstIncoming = p.firstIncoming := by cases p <;> rfl

theorem last_state (p : Path Clock (ClosureState Clock Var)) :
    (forgetGenerator p).lastState = p.lastState.form := by
  induction p with
  | last => rfl
  | step e s t ih => exact ih

/-- Original edges are retained from a syntactic inclusion of closure relations,
not from any assumed implication between recognition semantics. -/
theorem edge_forward (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (C R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, C N F → R N F) (s t : ClosureState Clock Var) (e : EdgeLabel Clock)
    (h : (s,e,t) ∈ (Generated.tableau X Q root C).edges) :
    (s.form,e,t.form) ∈ (tableau X Q root R).edges :=
  ⟨⟨s.generator,hinc _ _ h.1⟩,⟨t.generator,hinc _ _ h.2.1⟩,
    t.generator,h.2.2.1,hinc _ _ h.2.1,h.2.2.2⟩

theorem valid_forward (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (C R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, C N F → R N F) (p : Path Clock (ClosureState Clock Var))
    (hp : p.valid (Generated.tableau X Q root C)) :
    (forgetGenerator p).valid (tableau X Q root R) := by
  induction p with
  | last e s => exact ⟨s.generator,hinc _ _ hp⟩
  | step e s t ih =>
    refine ⟨⟨s.generator,hinc _ _ hp.1⟩,ih hp.2.1,?_⟩
    rw [first_state,first_incoming]
    exact edge_forward X Q root C R hinc s t.firstState t.firstIncoming hp.2.2

theorem run_forward (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (C R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, C N F → R N F) (p : Path Clock (ClosureState Clock Var))
    (hp : p.run (Generated.tableau X Q root C)) :
    (forgetGenerator p).run (tableau X Q root R) := by
  refine ⟨valid_forward X Q root C R hinc p hp.1,?_⟩
  rw [first_state,first_incoming]
  have hr := hinc _ _ hp.2.1
  rw [hp.2.2.1] at hr
  exact ⟨hr,hp.2.2.2⟩

theorem accepting_forward (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (C R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, C N F → R N F) (p : Path Clock (ClosureState Clock Var))
    (hp : p.accepting (Generated.tableau X Q root C)) :
    (forgetGenerator p).accepting (tableau X Q root R) := by
  refine ⟨valid_forward X Q root C R hinc p hp.1,?_⟩
  change (forgetGenerator p).lastState.nextPart = none
  rw [last_state]
  exact hp.2

/-- Exact trace equality, including all guards and every incoming reset scope. -/
theorem ordinary_trace_forward (p : Path Clock (ClosureState Clock Var)) :
    (forgetGenerator p).trace labels labels_finite = p.trace Generated.labels Generated.labels_finite := by
  induction p with
  | last e s => rfl
  | step e s t ih => exact congrArg (Trace.step _) ih

/-- Full trace on actual judgement states, retaining the same incoming labels. -/
def fullTrace (p : Path Clock (Section3.TransitionForm Clock Var)) : Trace Clock Var :=
  p.trace (fun F => F.current.locals) (fun F => F.current.locals_finite)

theorem full_trace_forward (p : Path Clock (ClosureState Clock Var)) :
    fullTrace (forgetGenerator p) = p.fullTrace := by
  induction p with
  | last e s => rfl
  | step e s t ih => exact congrArg (Trace.step _) ih

/-- The same single mapped accepting run works for every initial valuation. -/
theorem recognizes_forward (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (C R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, C N F → R N F) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) :
    (Generated.tableau X Q root C).recognizes Generated.labels_finite σ P →
      (tableau X Q root R).recognizes labels_finite σ P := by
  rintro ⟨p,hr,ha,hs⟩
  refine ⟨forgetGenerator p,run_forward X Q root C R hinc p hr,
    accepting_forward X Q root C R hinc p ha,?_⟩
  intro α
  change ((forgetGenerator p).trace labels labels_finite).holds σ P α ⟨0,by omega⟩
  rw [ordinary_trace_forward]
  exact hs α

/-- Specialization to the original literal minimal-closure definition.
This inclusion is to be discharged by an original-closure constructor of R. -/
theorem original_recognizes_forward (E : ClosureCatalogue Clock Var)
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, E.IsClosure (Section3.TransitionForm.ofState N) F → R N F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (Generated.closureTableau E X Q root).recognizes Generated.labels_finite σ P →
      (tableau X Q root R).recognizes labels_finite σ P :=
  recognizes_forward X Q root _ R hinc σ P

/-- The concrete original mixed catalogue, still requiring only structural
closure inclusion; no Step 1 reverse or soundness hypothesis is hidden here. -/
theorem concrete_original_recognizes_forward [DecidableEq Clock]
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (hinc : ∀ N F, ConcreteContextual.catalogue.IsClosure
      (Section3.TransitionForm.ofState N) F → R N F)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (Generated.closureTableau ConcreteContextual.catalogue X Q root).recognizes Generated.labels_finite σ P →
      (tableau X Q root R).recognizes labels_finite σ P :=
  original_recognizes_forward _ X Q root R hinc σ P

end STLTableau.Section4.Finiteness.JudgementTableau
