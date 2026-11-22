/-
Copyright (c) 2026 STLTableau contributors. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: STLTableau contributors
-/
import STLTableaux.Finiteness.Correctness.SimplifiedTableauPaths
import STLTableaux.Finiteness.Derivation.CompletedFreeClocks
import STLTableaux.Finiteness.Correctness.SimplifiedTableauCorrectness
import STLTableaux.Finiteness.ClockAllocation.SelectedTypedExtension
import STLTableaux.Finiteness.ClockAllocation.InitialSlotFrame
import STLTableaux.Tableau.Correctness.GeneratorPathCompleteness
import STLTableaux.Syntax.InputSyntax

/-! The finite tableau of Theorem 4.37 restricts the simplified tableau
(Definition D.4) to a fixed finite set of clocks and a finite set of states. -/
namespace STLTableau.Section4.Finiteness
open Section3 ResetTrimming
local notation "StateForm" => Section3.StateForm
local notation "TransitionForm" => Section3.TransitionForm

variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

noncomputable def simplifiedTableau (X : Set Var) (Q : Set Clock) (root : Formula Var) :=
  PairedTableau.tableau X Q (plainInitialState root) CompletedDerivation.Admitted

omit [DecidableEq Clock] in
noncomputable def finiteRootClocks (root : Formula Var) : Finset Clock :=
  FiniteInventory.clocks (rootSlotTriples root)

omit [DecidableEq Clock] in
noncomputable def finiteRootInventory (root : Formula Var) : Set (TransitionForm Clock Var) :=
  let ts := rootSlotTriples (Clock := Clock) root
  let locals := FiniteInventory.locals (Finiteness.rootPlainFormulas root) ts
  {F | FiniteInventory.TransitionWithin locals
    (FiniteInventory.guards ts) (FiniteInventory.resets ts) F}

omit [DecidableEq Clock] in
noncomputable def finitePairInventory (root : Formula Var) : Set (ClosureState Clock Var) :=
  {s | s.form ∈ finiteRootInventory root ∧ .ofState s.generator ∈ finiteRootInventory root}

private noncomputable def boundedCore (X : Set Var) (root : Formula Var) :=
  Subgraph.restrict (simplifiedTableau X ((finiteRootClocks root : Finset Clock) : Set Clock) root)
    (finitePairInventory root)

/-- The empty requirement paired with its empty closure. -/
def emptyFinalState : ClosureState Clock Var :=
  ⟨.ofState .empty, .empty⟩

local notation "qEmpty" => (emptyFinalState (Clock := Clock) (Var := Var))

/-- A final state has an empty next requirement. Its continuation uses the
empty state already in the finite inventory, and adds no guard or reset. The
empty state itself can continue flowing without a self-edge. -/
noncomputable def finiteTableau (X : Set Var) (root : Formula Var) :
    Tableau Clock Var (ClosureState Clock Var) :=
  let T := boundedCore (Clock := Clock) X root
  { T with edges := {e | e ∈ T.edges ∨
      (e.1 ∈ T.final ∧ e.1 ≠ qEmpty ∧ e.2.1 = (qEmpty).incoming ∧ e.2.2 = qEmpty)} }

section
variable (X : Set Var) (root : Formula Var)
local notation "FinTab" => finiteTableau (Clock := Clock) X root
local notation "Bnd" => boundedCore (Clock := Clock) X root
local notation "labs" => Generated.labels (Clock := Clock) (Var := Var)
local notation "hfin" => Generated.labels_finite (Clock := Clock) (Var := Var)

theorem finiteTableau_empty_final : qEmpty ∈ (FinTab).final := by
  have closed : ConcreteContextual.catalogue.IsClosed
      (.ofState (.empty : Section3.StateForm Clock Var)) := by
    intro p hp
    exact False.elim hp
  have hc := ClosureCatalogue.IsClosure.self closed
  have hReady : (Section3.StateForm.empty : Section3.StateForm Clock Var).Ready := by
    intro l hl
    exact False.elim hl
  have inv : (Section3.TransitionForm.ofState
      (Section3.StateForm.empty : Section3.StateForm Clock Var)) ∈ finiteRootInventory root := by
    refine ⟨⟨Set.empty_subset _, Set.empty_subset _, ?_⟩, ?_⟩
    · intro c a h
      cases h
    · intro N h
      cases h
  exact ⟨rfl, ⟨⟨_, hc⟩, .original hc hReady⟩, inv, inv⟩

omit [DecidableEq Clock] [Infinite Clock] in
@[simp] theorem emptyFinalState_labels : Generated.labels qEmpty = ∅ := by
  ext l
  change (l ∈ (∅ : Set (Local Clock Var)) ∧ _) ↔ l ∈ (∅ : Set (Local Clock Var))
  simp

theorem finiteTableau_final_empty_edge {q : ClosureState Clock Var}
    (final : q ∈ (FinTab).final) (ne : q ≠ qEmpty) :
    (q, (qEmpty).incoming, qEmpty) ∈ (FinTab).edges :=
  Or.inr ⟨final, ne, rfl, rfl⟩

private theorem boundedCore_no_final_edge {q q' : ClosureState Clock Var} {l : EdgeLabel Clock}
    (hf : q ∈ (Bnd).final) (he : (q, l, q') ∈ (Bnd).edges) : False := by
  obtain ⟨M, hn, _, _⟩ := he.1.2.2
  have hnone : q.form.nextPart = none := hf.1
  rw [hnone] at hn
  contradiction

theorem finiteTableau_final_successor
    {e : ClosureState Clock Var × EdgeLabel Clock × ClosureState Clock Var}
    (final : e.1 ∈ (FinTab).final) (edge : e ∈ (FinTab).edges) : e.2.2 ∈ (FinTab).final := by
  rcases edge with old | ⟨_, _, _, h⟩
  · exact (boundedCore_no_final_edge X root final old).elim
  · rw [h]
    exact finiteTableau_empty_final X root

theorem finiteTableau_edge_states
    {e : ClosureState Clock Var × EdgeLabel Clock × ClosureState Clock Var}
    (h : e ∈ (FinTab).edges) : e.1 ∈ (FinTab).states ∧ e.2.2 ∈ (FinTab).states := by
  rcases h with old | ⟨final, _, _, eq⟩
  · exact old.2
  · exact ⟨final.2, eq ▸ (finiteTableau_empty_final X root).2⟩

theorem finiteTableau_edge_incoming
    {e : ClosureState Clock Var × EdgeLabel Clock × ClosureState Clock Var}
    (h : e ∈ (FinTab).edges) : e.2.1 = e.2.2.incoming := by
  rcases h with old | ⟨_, _, he, ht⟩
  · obtain ⟨_, _, _, eq⟩ := old.1.2.2
    exact eq
  · exact he.trans (congrArg ClosureState.incoming ht).symm

theorem finiteTableau_edge_input_or_empty
    {e : ClosureState Clock Var × EdgeLabel Clock × ClosureState Clock Var}
    (h : e ∈ (FinTab).edges) :
    (∃ M, e.1.form.nextPart = some M ∧
      CompletedDerivation.Admitted M e.2.2.form) ∨ e.2.2 = qEmpty := by
  rcases h with old | ⟨_, _, _, ht⟩
  · obtain ⟨M, hn, hM, _⟩ := old.1.2.2
    exact Or.inl ⟨M, hn, hM⟩
  · exact Or.inr ht

private theorem empty_no_edge {e : EdgeLabel Clock} {s : ClosureState Clock Var}
    (edge : (qEmpty, e, s) ∈ (FinTab).edges) : False := by
  rcases edge with old | ⟨_, ne, _, _⟩
  · exact boundedCore_no_final_edge X root (finiteTableau_empty_final X root) old
  · exact ne rfl

/-- The optional last empty frame contributes no free clocks and may be removed. -/
private theorem trim_final_empty (p : Path Clock (ClosureState Clock Var))
    (valid : p.valid FinTab) :
    ∃ q : Path Clock (ClosureState Clock Var), q.valid Bnd ∧
      q.firstState = p.firstState ∧ q.firstIncoming = p.firstIncoming ∧
      (p.lastState ∈ (FinTab).final → q.lastState ∈ (Bnd).final) ∧
      (q.trace labs hfin).freeClocks = (p.trace labs hfin).freeClocks ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) k,
        (p.trace labs hfin).holds σ P α k → (q.trace labs hfin).holds σ P α k := by
  induction p with
  | last e s => exact ⟨.last e s, valid, rfl, rfl, id, rfl, fun _ _ _ _ => id⟩
  | step e s t ih =>
    rcases valid.2.2 with old | added
    · obtain ⟨u, hu, hs, hl, hg, hc, ht⟩ := ih valid.2.1
      refine ⟨.step e s u, ⟨valid.1, hu, ?_⟩, rfl, rfl, hg, ?_, ?_⟩
      · simpa only [hs, hl] using old
      · simp only [Path.trace, Trace.freeClocks, hc]
      · intro σ P α k sat
        refine ⟨sat.1, ?_⟩
        have tail := sat.2
        by_cases hk : k.val < P.size
        · simp only [dif_pos hk] at tail ⊢
          exact ht _ _ _ _ tail
        · simp only [dif_neg hk] at tail
    · obtain ⟨final, _, he, hs⟩ := added
      cases t with
      | step l q rest =>
        change q = qEmpty at hs
        subst q
        exact (empty_no_edge X root valid.2.1.2.2).elim
      | last l q =>
        change q = qEmpty at hs
        change l = (qEmpty).incoming at he
        subst q
        subst l
        refine ⟨.last e s, valid.1, rfl, rfl, fun _ => final, ?_,
          fun _ _ _ _ sat => sat.1⟩
        simp only [Path.trace, Trace.freeClocks, emptyFinalState_labels]
        simp [ClosureState.incoming, emptyFinalState, Section3.TransitionForm.ofState,
          Section3.StateForm.empty, Section3.StateForm.freeClocks, Section3.StateForm.guardClocks,
          Section3.StateForm.localClocks]

private theorem valid_of_bounded (p : Path Clock (ClosureState Clock Var))
    (hv : p.valid Bnd) : p.valid FinTab := by
  induction p with
  | last => exact hv
  | step l s p ih => exact ⟨hv.1, ih hv.2.1, Or.inl hv.2.2⟩

private theorem recognizes_bounded_iff (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (FinTab).recognizes hfin σ P ↔ (Bnd).recognizes hfin σ P := by
  constructor
  · rintro ⟨p, run, goal, trace⟩
    obtain ⟨q, hq, hs, hl, hg, _, ht⟩ := trim_final_empty X root p run.1
    exact ⟨q, ⟨hq, by rw [hs, hl]; exact run.2⟩, ⟨hq, hg goal.2⟩,
      fun α => ht _ _ _ _ (trace α)⟩
  · rintro ⟨p, run, goal, trace⟩
    have v := valid_of_bounded X root p run.1
    exact ⟨p, ⟨v, run.2⟩, ⟨v, goal.2⟩, trace⟩

theorem finiteTableau_trace_closed (p : Path Clock (ClosureState Clock Var))
    (hr : p.run FinTab) : (p.trace labs hfin).freeClocks = ∅ := by
  obtain ⟨q, hq, hs, hl, _, hc, _⟩ := trim_final_empty X root p hr.1
  have hcore : q.run Bnd := ⟨hq, by rw [hs, hl]; exact hr.2⟩
  have hp := (Subgraph.run_iff _ _ q).1 hcore |>.1
  let Q : Set Clock := (finiteRootClocks root : Finset Clock)
  have hp' := PairedTableau.forget_run X Q (plainInitialState root)
    CompletedDerivation.Admitted q hp
  have hroot : (plainInitialState (Clock := Clock) root).freeClocks = ∅ := by
    ext c
    simp [plainInitialState, Section3.StateForm.ofLocal, Section3.StateForm.freeClocks,
      Section3.StateForm.guardClocks, Section3.StateForm.localClocks, Local.freeClocks,
      Local.toJudgement, Section3.Judgement.freeClocks]
  have ht := JudgementTableau.fullTrace_closed_of_run X Q (plainInitialState root)
    CompletedDerivation.Admitted (fun _ _ h => h.free_subset)
    (JudgementTableau.forgetGenerator q) hp' hroot
  rw [← hc, ← JudgementTableau.ordinary_trace_forward]
  exact Set.eq_empty_of_subset_empty (ht ▸ ordinaryTrace_free_subset_fullTrace _)

end

private def finiteStateCode (X : Set Var) (root : Formula Var)
    (s : ↥(finiteTableau (Clock := Clock) X root).states) :
    ↥(finiteRootInventory (Clock := Clock) root) ×
      ↥(finiteRootInventory (Clock := Clock) root) :=
  (⟨s.val.form,s.property.2.1⟩, ⟨.ofState s.val.generator,s.property.2.2⟩)

private theorem finiteStateCode_injective (X : Set Var) (root : Formula Var) :
    Function.Injective (finiteStateCode (Clock := Clock) X root) := by
  intro ⟨⟨F,M⟩, hs⟩ ⟨⟨G,N⟩, ht⟩ he
  apply Subtype.ext
  have hF : F = G := congrArg (fun s => s.1.val) he
  have hM : M = N := congrArg (fun s => s.2.val.current) he
  cases hF
  cases hM
  rfl

omit [DecidableEq Clock] in
private theorem finiteRootInventory_finite (root : Formula Var) :
    (finiteRootInventory (Clock := Clock) root).Finite :=
  FiniteInventory.sparse_transition_finite _ _

theorem finiteTableau_states_finite (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).states.Finite := by
  haveI := Set.finite_coe_iff.mpr (finiteRootInventory_finite (Clock := Clock) root)
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (finiteStateCode_injective X root))

theorem finiteTableau_state_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(finiteTableau (Clock := Clock) X root).states ≤
      2 ^ (11268 * literalFormulaSize root * Finiteness.formulaResolution root + 14) := by
  let A := ↥(finiteRootInventory (Clock := Clock) root)
  haveI : Finite A := Set.finite_coe_iff.mpr (finiteRootInventory_finite (Clock := Clock) root)
  let e := 5634 * literalFormulaSize root * Finiteness.formulaResolution root + 7
  have hA : Nat.card A ≤ 2 ^ e :=
    (FiniteInventory.sparse_transition_card_le _ _).trans
      (Nat.pow_le_pow_right (by omega) (rootSlot_sparse_exponent_le_resolution root))
  calc
    _ ≤ Nat.card (A × A) := Nat.card_le_card_of_injective _ (finiteStateCode_injective X root)
    _ = Nat.card A * Nat.card A := Nat.card_prod _ _
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul hA hA
    _ = _ := by rw [← pow_add]; congr 1; dsimp [e]; ring

theorem finiteTableau_clocks_finite (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).clocks.Finite := Finset.finite_toSet _

theorem finiteTableau_edges_finite (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).edges.Finite := by
  let T := finiteTableau (Clock := Clock) X root
  have hS : T.states.Finite := finiteTableau_states_finite X root
  refine ((hS.prod hS).image (fun p => (p.1,p.2.incoming,p.2))).subset ?_
  rintro ⟨s,e,t⟩ he
  have h : (s,e,t) ∈ T.edges := he
  have heq := finiteTableau_edge_incoming X root h
  exact ⟨(s,t), finiteTableau_edge_states X root h,
    congrArg (fun l => (s,l,t)) heq.symm⟩

theorem finiteTableau_initial_finite (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).initial.Finite := by
  let T := finiteTableau (Clock := Clock) X root
  have hS : T.states.Finite := finiteTableau_states_finite X root
  refine (hS.image (fun s => (s.incoming,s))).subset ?_
  rintro ⟨e,s⟩ he
  have h : (e,s) ∈ T.initial := he
  exact ⟨s,h.2,congrArg (fun l => (l,s)) h.1.2.2.symm⟩

theorem finiteTableau_final_finite (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).final.Finite :=
  (finiteTableau_states_finite X root).subset (fun _ h => h.2)

theorem finiteTableau_clock_card_le (X : Set Var) (root : Formula Var) :
    Nat.card ↥(finiteTableau (Clock := Clock) X root).clocks ≤
      132 * literalFormulaSize root * Finiteness.formulaResolution root := by
  change Nat.card ↥((finiteRootClocks root : Finset Clock) : Set Clock) ≤ _
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact rootSlot_clocks_card_le_resolution root

omit [DecidableEq Clock] [Infinite Clock] in
private theorem trimState_plainInitial (root : Formula Var) :
    trimState (plainInitialState (Clock := Clock) root) = plainInitialState root := by
  classical
  refine Section3.StateForm.ext_components (S := trimState (plainInitialState root))
    (T := plainInitialState root) rfl ?_ rfl
  apply (ClockResetSet.mk.injEq _ _ _ _).mpr
  funext c
  change (if c ∈ (plainInitialState (Clock := Clock) root).localClocks then
    (none : Option NNReal) else none) = none
  split <;> rfl

/-- Accepting path construction for Theorem 4.37. The path uses the
finite set of clocks determined by the input formula. -/
theorem finiteTableau_bounded_accepting_path
    (X : Set Var) (root : Formula Var) (ready : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (plain : Judgement.holds σ P α k (.predicate (.plain root)))
    (stable : σ.StablePartition root P) :
    ∃ p : Path Clock (ClosureState Clock Var),
      p.run (finiteTableau X root) ∧ p.accepting (finiteTableau X root) ∧
      p.fullTrace.holds σ P α k := by
  classical
  let t := rootSlotTriples (Clock := Clock) root
  let Q : Set Clock := (finiteRootClocks root : Finset Clock)
  let L := FiniteInventory.locals (Finiteness.rootPlainFormulas root) t
  let G := FiniteInventory.guards t
  let R := FiniteInventory.resets t
  let Inv := fun (β : ClockValuation Clock) (j : STLTableau.Judgement.Position P)
    (N : StateForm Clock Var) => Nonempty (InputOrigins σ P β j N) ∧
      Finiteness.StateFormulasBelow root N ∧ ∃ J, SafeNormalization J (.ofState N)
  let Frame := fun (_ : ClockValuation Clock) (_ : STLTableau.Judgement.Position P)
    (N : StateForm Clock Var) (e : Equiv.Perm Clock) => Nonempty (SlotFrame t N e)
  let O := plainInitialOrigins (Clock := Clock) root σ P α k ready plain stable
  have hi : Inv α k (plainInitialState root) :=
    ⟨⟨O⟩, Finiteness.plain_formulas_below root, ⟨.predicate (.plain root),.predicate _⟩⟩
  have hf : Frame α k (plainInitialState root) (Equiv.refl Clock) :=
    ⟨plain_initial_slot_frame t root (Equiv.refl Clock)⟩
  have hroot : trimState ((plainInitialState (Clock := Clock) root).rename (Equiv.refl Clock)) =
      plainInitialState root := by
    have he : (plainInitialState (Clock := Clock) root).rename (Equiv.refl Clock) =
        plainInitialState root := by
      simp [plainInitialState, rename_state_local, Local.rename, Predicate.rename]
    rw [he, trimState_plainInitial]
  have h := path_of_local_extensions X Q σ P Inv Frame
    (fun s => s ∈ finitePairInventory root) ?_ ?_ α α k (plainInitialState root) hi
    (Equiv.refl Clock) hf (fun _ _ => rfl)
  · rw [hroot] at h
    obtain ⟨p,hr,ha,htrace,hgood⟩ := h
    have hrun : p.run (boundedCore X root) := (Subgraph.run_iff _ _ p).2 ⟨hr,hgood⟩
    have hacc := (Subgraph.accepting_iff _ _ p).2 ⟨ha,hgood⟩
    have hvalid := valid_of_bounded X root p hrun.1
    exact ⟨p, ⟨hvalid, hrun.2⟩, ⟨hvalid, hacc.2⟩, htrace⟩
  · intro β j N hI
    obtain ⟨O'⟩ := hI.1
    exact ⟨O'.holds,O'.fullInvariant,O'.stable.current⟩
  · intro β j N hI incoming hFr
    obtain ⟨O'⟩ := hI.1
    obtain ⟨frame⟩ := hFr
    have hGenerator : FiniteInventory.Within L G R (N.rename incoming) :=
      frame.stateTyped.rename_within (Finiteness.rootPlainFormulas root) incoming frame.realizes
        (by
          intro φ hp
          exact Finiteness.subformula_mem_rootPlainFormulas (hI.2.1 (.predicate (.plain φ)) hp))
    have hGen : Section3.TransitionForm.ofState (trimState (N.rename incoming)) ∈
        finiteRootInventory root :=
      ⟨trimState_within hGenerator, by intro M hm; cases hm⟩
    by_cases hne : N.locals.Nonempty
    · obtain ⟨J,W,owned,H,Er,F,tree,hnil,hInput,_,hFacts,_,hSuccessor⟩ :=
        O'.nonempty_selected_origin_step hne
      have hLocal := owned.local_mem_of_safe hInput
      obtain ⟨C,e,hAgree,hF,hTyped,hNextFrame⟩ :=
        tree.exists_root_typed_extension O' root hI.2.1 hInput hLocal hnil hFacts frame
      refine ⟨F,C,e,hAgree,hF,⟨trim_within hTyped,hGen⟩,?_⟩
      intro M hn hj
      have hBelow := tree.realize.normalized_formulas_below hInput hFacts.1 root hI.2.1
      exact ⟨⟨hSuccessor hj M hn,hBelow.2 M hn,hFacts.1.next_input hn⟩,hNextFrame M hn⟩
    · have he : N.locals = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      obtain ⟨J,hJ⟩ := hI.2.2
      have hz := hJ.weight_zero_of_locals_empty he
      let C : ResolvedCertificate N (.ofState N) :=
        ⟨J, J, J, PendingCompletionBase.resolve_zero J hz, hJ, hJ,
          PendingCompletionBase.erased_safe J hz hJ⟩
      refine ⟨.ofState N,C,incoming,(fun _ _ => rfl),⟨O'.holds,trivial⟩,?_,?_⟩
      · rw [rename_ofState]
        exact ⟨trim_within ⟨hGenerator, by intro M hm; cases hm⟩,hGen⟩
      · intro M hm
        cases hm

/-- Lemma D.5 (soundness of the simplified tableau) on any partition. -/
theorem simplifiedTableau_sound (X : Set Var) (Q : Set Clock) (root : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (h : (simplifiedTableau X Q root).recognizes Generated.labels_finite σ P) :
    σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ := by
  obtain ⟨p,hr,ha,hs⟩ := h
  exact (simplified_fullTrace_and_formula_of_atomic X Q root p hr ha σ P _ (hs (fun _ => 0))).2

theorem finiteTableau_sound (X : Set Var) (root : Formula Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (h : (finiteTableau (Clock := Clock) X root).recognizes Generated.labels_finite σ P) :
    σ.Satisfies root ⟨0, le_rfl, σ.horizon_pos⟩ :=
  simplifiedTableau_sound X _ root σ P (Subgraph.recognizes_lift _ _ _ σ P
    ((recognizes_bounded_iff X root σ P).mp h))

/-- Completeness in Theorem 4.37. On the given fully stable partition, one
bounded accepting run has a satisfied trace for every initial clock valuation. -/
theorem finiteTableau_complete (X : Set Var) (root : Formula Var) (ready : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (stable : σ.StablePartition root P)
    (truth : σ.Satisfies root ⟨0, le_rfl, σ.horizon_pos⟩) :
    (finiteTableau (Clock := Clock) X root).recognizes Generated.labels_finite σ P := by
  let α : ClockValuation Clock := fun _ => 0
  let k : STLTableau.Judgement.Position P := ⟨0,by omega⟩
  have plain : Judgement.holds σ P α k (.predicate (.plain root)) := by
    change if h : 0 < P.size then _ else False
    simp only [dif_pos (Generated.partition_size_pos σ P)]
    intro t ht
    exact ((stable ⟨0,Generated.partition_size_pos σ P⟩).stable
      ⟨0,le_rfl,σ.horizon_pos⟩ t (Generated.zero_mem_first_interval σ P) ht).mp truth
  obtain ⟨p,hr,ha,hs⟩ := finiteTableau_bounded_accepting_path X root ready σ P α k plain stable
  exact ⟨p, hr, ha, fun β =>
    ((p.trace Generated.labels Generated.labels_finite).holds_independent_of_initial_clocks σ P
      (finiteTableau_trace_closed X root p hr) α β k).1
      (Generated.atomic_trace_of_fullTrace p σ P α k hs)⟩

/-- Recognition equivalence in Theorem 4.37 on a fully stable partition. -/
theorem finiteTableau_recognizes_iff (X : Set Var) (root : Formula Var)
    (ready : root.MixedReady)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (stable : σ.StablePartition root P) :
    (finiteTableau (Clock := Clock) X root).recognizes Generated.labels_finite σ P ↔
      σ.Satisfies root ⟨0,le_rfl,σ.horizon_pos⟩ :=
  ⟨finiteTableau_sound X root σ P, finiteTableau_complete X root ready σ P stable⟩

theorem finiteTableau_recognizes_normalized_input (X : Set Var) (root : Formula.NormalizedInput Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (stable : σ.StablePartition root.val P) :
    (finiteTableau (Clock := Clock) X root.val).recognizes Generated.labels_finite σ P ↔
      σ.Satisfies root.val ⟨0,le_rfl,σ.horizon_pos⟩ :=
  finiteTableau_recognizes_iff X root.val root.property.mixedReady σ P stable

end STLTableau.Section4.Finiteness
