import STLTableaux.Tableau.Correctness.TableauSoundness
import STLTableaux.Finiteness.Inventory.FiniteInventory

/-! Restriction of the actual Section 4 tableau tuple. Paths retain all incoming
labels, including their guards and reset scopes. Completeness below explicitly
requires an inventory-member representative; no such path is constructed here. -/
namespace STLTableau.Section4.Finiteness.Subgraph
open Section3
variable {Clock Var State : Type*}

/-- Induced restriction, without identification of equally labelled states. -/
def restrict (T : Tableau Clock Var State) (A : Set State) : Tableau Clock Var State where
  realVariables := T.realVariables
  clocks := T.clocks
  states := T.states ∩ A
  edges := {e | e ∈ T.edges ∧ e.1 ∈ T.states ∩ A ∧ e.2.2 ∈ T.states ∩ A}
  initial := {e | e ∈ T.initial ∧ e.2 ∈ T.states ∩ A}
  final := T.final ∩ (T.states ∩ A)
  label := T.label
  label_atomic := T.label_atomic

/-- Membership of every actual state in a nonempty finite Section 4 path. -/
def AllStates (A : Set State) : Path Clock State → Prop
  | .last _ s => s ∈ A
  | .step _ s t => s ∈ A ∧ AllStates A t

theorem first_mem {A : Set State} {p : Path Clock State}
    (h : AllStates A p) : p.firstState ∈ A := by
  cases p with
  | last => exact h
  | step => exact h.1

theorem last_mem {A : Set State} {p : Path Clock State}
    (h : AllStates A p) : p.lastState ∈ A := by
  induction p with
  | last => exact h
  | step e s t ih => exact ih h.2

theorem first_state_of_valid (T : Tableau Clock Var State) (p : Path Clock State)
    (h : p.valid T) : p.firstState ∈ T.states := by
  cases p with
  | last => exact h
  | step => exact h.1

theorem last_state_of_valid (T : Tableau Clock Var State) (p : Path Clock State)
    (h : p.valid T) : p.lastState ∈ T.states := by
  induction p with
  | last => exact h
  | step e s t ih => exact ih h.2.1

theorem valid_lift (T : Tableau Clock Var State) (A : Set State)
    (p : Path Clock State) (h : p.valid (restrict T A)) : p.valid T := by
  induction p with
  | last e s => exact h.1
  | step e s t ih => exact ⟨h.1.1,ih h.2.1,h.2.2.1⟩

theorem allStates_of_valid (T : Tableau Clock Var State) (A : Set State)
    (p : Path Clock State) (h : p.valid (restrict T A)) : AllStates A p := by
  induction p with
  | last e s => exact h.2
  | step e s t ih => exact ⟨h.1.2,ih h.2.1⟩

theorem valid_restrict (T : Tableau Clock Var State) (A : Set State)
    (p : Path Clock State) (h : p.valid T) (hm : AllStates A p) :
    p.valid (restrict T A) := by
  induction p with
  | last e s => exact ⟨h,hm⟩
  | step e s t ih =>
    exact ⟨⟨h.1,hm.1⟩,ih h.2.1 hm.2,⟨h.2.2,⟨h.1,hm.1⟩,⟨first_state_of_valid T t h.2.1,first_mem hm.2⟩⟩⟩

theorem valid_iff (T : Tableau Clock Var State) (A : Set State) (p : Path Clock State) :
    p.valid (restrict T A) ↔ p.valid T ∧ AllStates A p :=
  ⟨fun h => ⟨valid_lift T A p h,allStates_of_valid T A p h⟩,
    fun h => valid_restrict T A p h.1 h.2⟩

theorem run_iff (T : Tableau Clock Var State) (A : Set State) (p : Path Clock State) :
    p.run (restrict T A) ↔ p.run T ∧ AllStates A p := by
  constructor
  · intro h
    exact ⟨⟨valid_lift T A p h.1,h.2.1⟩,allStates_of_valid T A p h.1⟩
  · rintro ⟨h,hm⟩
    exact ⟨valid_restrict T A p h.1 hm,⟨h.2,⟨first_state_of_valid T p h.1,first_mem hm⟩⟩⟩

theorem accepting_iff (T : Tableau Clock Var State) (A : Set State)
    (p : Path Clock State) :
    p.accepting (restrict T A) ↔ p.accepting T ∧ AllStates A p := by
  constructor
  · intro h
    exact ⟨⟨valid_lift T A p h.1,h.2.1⟩,allStates_of_valid T A p h.1⟩
  · rintro ⟨h,hm⟩
    exact ⟨valid_restrict T A p h.1 hm,⟨h.2,⟨last_state_of_valid T p h.1,last_mem hm⟩⟩⟩

/-- Literal equality of ordinary traces: inherited guards and reset maps are
unchanged, not merely semantically simulated. -/
theorem ordinary_trace_eq (T : Tableau Clock Var State) (A : Set State)
    (hf : ∀ s, (T.label s).Finite) (p : Path Clock State) :
    p.trace (restrict T A).label hf = p.trace T.label hf := rfl

/-- The existing full trace of a closure-state path is likewise the same trace
on either side of its lifting, since the lifting uses the identical path. -/
theorem full_trace_preserved (T : Tableau Clock Var (ClosureState Clock Var))
    (A : Set (ClosureState Clock Var)) (p : Path Clock (ClosureState Clock Var))
    (hr : p.run (restrict T A)) (ha : p.accepting (restrict T A)) :
    p.run T ∧ p.accepting T ∧
      p.trace (fun s => s.form.current.locals) (fun s => s.form.current.locals_finite) =
        p.fullTrace :=
  ⟨((run_iff T A p).1 hr).1,((accepting_iff T A p).1 ha).1,rfl⟩

/-- Full traces for the proposed judgement-state version use those actual
judgements' current locals, retaining the path's actual incoming reset labels. -/
def judgementFullTrace (p : Path Clock (Section3.TransitionForm Clock Var)) : Trace Clock Var :=
  p.trace (fun s => s.current.locals) (fun s => s.current.locals_finite)

/-- No full-trace reconstruction is needed when a judgement path is retained. -/
theorem judgement_full_trace_preserved
    (T : Tableau Clock Var (Section3.TransitionForm Clock Var))
    (A : Set (Section3.TransitionForm Clock Var))
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (restrict T A)) (ha : p.accepting (restrict T A)) :
    p.run T ∧ p.accepting T ∧
      p.trace (fun s => s.current.locals) (fun s => s.current.locals_finite) =
        judgementFullTrace p :=
  ⟨((run_iff T A p).1 hr).1,((accepting_iff T A p).1 ha).1,rfl⟩

/-- Recognition by the restricted tableau implies recognition by the full tableau. -/
theorem recognizes_lift (T : Tableau Clock Var State) (A : Set State)
    (hf : ∀ s, (T.label s).Finite) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) :
    (restrict T A).recognizes hf σ P → T.recognizes hf σ P := by
  rintro ⟨p,hr,ha,hs⟩
  exact ⟨p,((run_iff T A p).1 hr).1,((accepting_iff T A p).1 ha).1,hs⟩

/-- Soundness reduction for any actual judgement-state tableau whose ordinary
trace soundness has been proved. This does not supply that Step 1 proof. -/
theorem soundness_transfer (T : Tableau Clock Var State) (A : Set State)
    (hf : ∀ s, (T.label s).Finite) (φ : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (hsound : T.recognizes hf σ P → σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩) :
    (restrict T A).recognizes hf σ P → σ.Satisfies φ ⟨0,le_rfl,σ.horizon_pos⟩ :=
  fun h => hsound (recognizes_lift T A hf σ P h)

/-- Conditional completeness: the premise is one actual initial accepting
representative in A, on this signal and partition, working for all valuations.
The representative's existence is deliberately not proved by this lemma. -/
theorem recognizes_of_member_representative (T : Tableau Clock Var State) (A : Set State)
    (hf : ∀ s, (T.label s).Finite) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (p : Path Clock State)
    (hr : p.run T) (ha : p.accepting T) (hm : AllStates A p)
    (hs : ∀ α : ClockValuation Clock,
      (p.trace T.label hf).holds σ P α ⟨0,by omega⟩) :
    (restrict T A).recognizes hf σ P :=
  ⟨p,(run_iff T A p).2 ⟨hr,hm⟩,(accepting_iff T A p).2 ⟨ha,hm⟩,hs⟩

/-- This restriction applies to any actual tableau on judgement states; its
state set is finite independently of any representative-path existence. -/
theorem sparse_restriction_states_finite {Slot : Type*} [Fintype Slot]
    (T : Tableau Clock Var (Section3.TransitionForm Clock Var))
    (P : Finset (Formula Var)) (t : Slot → FiniteInventory.Triple Clock Var) :
    (restrict T {S | FiniteInventory.TransitionWithin
      (FiniteInventory.locals P t) (FiniteInventory.guards t) (FiniteInventory.resets t) S}).states.Finite :=
  (FiniteInventory.sparse_transition_finite P t).subset (fun _ hs => hs.2)

/-- The actual retained state subtype inherits the sparse exponential bound.
No formula-size estimate for the number of slots is assumed or concluded. -/
theorem sparse_restriction_state_card_le {Slot : Type*} [Fintype Slot]
    (T : Tableau Clock Var (Section3.TransitionForm Clock Var))
    (P : Finset (Formula Var)) (t : Slot → FiniteInventory.Triple Clock Var) :
    Nat.card ↥(restrict T {S | FiniteInventory.TransitionWithin
      (FiniteInventory.locals P t) (FiniteInventory.guards t) (FiniteInventory.resets t) S}).states ≤
      2 ^ (2 * (P.card + 3 + 64 * Fintype.card Slot) + 1) := by
  let A : Set (Section3.TransitionForm Clock Var) := {S | FiniteInventory.TransitionWithin
    (FiniteInventory.locals P t) (FiniteInventory.guards t) (FiniteInventory.resets t) S}
  haveI : Finite ↥A := Set.finite_coe_iff.mpr (FiniteInventory.sparse_transition_finite P t)
  have hi : Function.Injective (fun s : ↥(restrict T A).states => (⟨s.val,s.property.2⟩ : ↥A)) := by
    intro s u h
    exact Subtype.ext (congrArg (fun x : ↥A => x.val) h)
  exact (Nat.card_le_card_of_injective _ hi).trans (FiniteInventory.sparse_transition_card_le P t)

end STLTableau.Section4.Finiteness.Subgraph
