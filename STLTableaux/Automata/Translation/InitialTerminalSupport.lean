import STLTableaux.Automata.Translation.InitialClockSupport
import STLTableaux.Automata.Recognition.TableauExecutionTime

/-! Current terminal propositions are inherited, not introduced by expansion.
Terminal propositions under next are deliberately allowed. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def NoCurrentTerminal : MixedJ Clock Var → Prop
  | .terminal => False
  | .conj J K => NoCurrentTerminal J ∧ NoCurrentTerminal K
  | .reset _ J => NoCurrentTerminal J
  | _ => True

theorem normalize_noCurrentTerminal (J : MixedJ Clock Var)
    {F : Section3.TransitionForm Clock Var}
    (hn : Section3.TransitionForm.normalize? J = some F) :
    Local.terminal ∉ F.current.locals ↔ NoCurrentTerminal J := by
  induction J generalizing F with
  | terminal =>
    cases hn
    simp [NoCurrentTerminal, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | clock =>
    cases hn
    simp [NoCurrentTerminal, Section3.TransitionForm.ofState, Section3.StateForm.ofGuard]
  | marker =>
    cases hn
    simp [NoCurrentTerminal, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | predicate =>
    cases hn
    simp [NoCurrentTerminal, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | reset R J ih =>
    cases he : TransitionForm.normalize? J with
    | none => simp [TransitionForm.normalize?, he] at hn
    | some G =>
      simp only [TransitionForm.normalize?, he, Option.map_some, Option.some.injEq] at hn
      subst F
      exact ih (F := G) he
  | conj J K ih ik =>
    cases he : TransitionForm.normalize? J with
    | none => simp [TransitionForm.normalize?, he] at hn
    | some G =>
      cases hf : TransitionForm.normalize? K with
      | none => simp [TransitionForm.normalize?, he, hf] at hn
      | some H =>
        simp [TransitionForm.normalize?, he, hf] at hn
        subst F
        change (Local.terminal ∉ G.current.locals ∪ H.current.locals) ↔ _
        simpa only [Set.mem_union, not_or, NoCurrentTerminal] using and_congr (ih he) (ik hf)
  | next J ih =>
    cases he : TransitionForm.normalize? J with
    | none => simp [TransitionForm.normalize?, he] at hn
    | some G =>
      cases hx : G.nextPart with
      | some N => simp [TransitionForm.normalize?, he, hx] at hn
      | none =>
        simp [TransitionForm.normalize?, he, hx] at hn
        subst F
        simp [Section3.TransitionForm.ofNextState, Section3.StateForm.empty, NoCurrentTerminal]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem finite_branch_noCurrentTerminal [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) : NoCurrentTerminal (Judgement.ofFinite B) := by
  classical
  open STLTableau.ExpansionRule in
    cases hr <;>
      simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
        upperAlways, boundedAlways, upperEventually, boundedEventually,
        List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlways_defer, upperAlways_check, boundedAlways_defer,
        boundedAlways_check, boundedAlways_finish, upperEventually_defer,
        upperEventually_check, boundedEventually_defer, boundedEventually_check,
        boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
        STLTableau.Judgement.markedGT_eq_clock, Judgement.ofFinite, NoCurrentTerminal]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem infinite_branch_noCurrentTerminal [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var}
    (hB : B ∈ Bs) : NoCurrentTerminal (Judgement.ofUnbounded B) := by
  classical
  open UnboundedClocked in
    cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        Node.lt, Node.gt, Judgement.ofUnbounded, NoCurrentTerminal]

theorem RawBranch.noCurrentTerminal [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hb : RawBranch p B) :
    NoCurrentTerminal B := by
  cases hb with
  | finite hr hm => exact finite_branch_noCurrentTerminal hr hm
  | infinite hr hm => exact infinite_branch_noCurrentTerminal hr hm
  | opening => trivial

theorem ACIdem.noCurrentTerminal_iff {J K : MixedJ Clock Var} (h : ACIdem J K) :
    NoCurrentTerminal J ↔ NoCurrentTerminal K := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ig => exact ih.trans ig
  | assoc => simp only [NoCurrentTerminal, and_assoc]
  | comm => exact and_comm
  | idem => simp only [NoCurrentTerminal, and_self]
  | conj _ _ ih ig => exact and_congr ih ig
  | reset _ _ ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

theorem noCurrentTerminal_withBoundaryGuard (c : Clock) (b : Marker) (J : MixedJ Clock Var) :
    NoCurrentTerminal (withBoundaryGuard c b J) ↔ NoCurrentTerminal J := by
  cases b <;> simp [withBoundaryGuard, NoCurrentTerminal]

theorem Resolve.noCurrentTerminal [DecidableEq Clock]
    {J H A : MixedJ Clock Var} (hd : Resolve J H A)
    (hj : NoCurrentTerminal J) : NoCurrentTerminal H := by
  induction hd with
  | leaf => exact hj
  | conj _ _ ih ig => exact ⟨ih hj.1, ig hj.2⟩
  | reset _ _ ih => exact ih hj
  | structural he _ ih => exact ih (he.noCurrentTerminal_iff.mp hj)
  | expandCtx hb _ _ _ ih => exact ⟨trivial, ih ⟨hb.noCurrentTerminal, hj.2⟩⟩
  | expandSolo hb _ _ _ ih => exact ⟨trivial, ih hb.noCurrentTerminal⟩
  | boundaryRequired _ _ _ ih =>
    apply ih
    simpa only [NoCurrentTerminal, noCurrentTerminal_withBoundaryGuard, true_and] using hj.2
  | boundaryOptional _ _ _ ih =>
    apply ih
    simpa only [NoCurrentTerminal, noCurrentTerminal_withBoundaryGuard, true_and] using hj.2
  | unusedReset _ _ _ _ _ ih => exact ih hj

theorem alpha_current_terminal_iff {F G : Section3.TransitionForm Clock Var}
    (ha : Section3.TransitionForm.AlphaEquivalent F G) :
    Local.terminal ∈ F.current.locals ↔ Local.terminal ∈ G.current.locals := by
  induction ha with
  | refl => rfl
  | outer F e _ =>
    change Local.terminal ∈ Local.rename e '' F.current.locals ↔ _
    constructor
    · rintro ⟨l, hl, he⟩
      cases l with
      | terminal => exact hl
      | marker => cases he
      | predicate => cases he
    · intro hl
      exact ⟨.terminal, hl, rfl⟩
  | next => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ig => exact ih.trans ig

theorem mixed_branch_no_terminal [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) : Local.terminal ∉ B.current.locals := by
  rcases hb with hb | hb | hb
  · obtain ⟨p, R, raw, F, rfl, hr, hm, hn, rfl⟩ := hb
    exact (normalize_noCurrentTerminal _ (F := F) hn).mpr (finite_branch_noCurrentTerminal hr hm)
  · obtain ⟨p, Bs, raw, F, rfl, hr, hm, hn, rfl⟩ := hb
    exact (normalize_noCurrentTerminal _ (F := F) hn).mpr (infinite_branch_noCurrentTerminal hr hm)
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := hb
    exact (normalize_noCurrentTerminal _ (F := F) hn).mpr (by cases kind <;> trivial)

theorem contextual_branch_no_terminal [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B) : Local.terminal ∉ B.current.locals := by
  obtain ⟨R, A, hr, ha, rfl⟩ := hb
  exact fun ht => mixed_branch_no_terminal hr ((alpha_current_terminal_iff ha).mp ht)

theorem closure_no_terminal [DecidableEq Clock]
    {Φ U : Section3.TransitionForm Clock Var}
    (hc : ConcreteContextual.catalogue.IsClosure Φ U)
    (hΦ : Local.terminal ∉ Φ.current.locals) : Local.terminal ∉ U.current.locals := by
  let V : Section3.TransitionForm Clock Var :=
    { U with current := { U.current with
      locals := {l ∈ U.current.locals | l ≠ Local.terminal}
      locals_finite := U.current.locals_finite.subset (fun _ hl => hl.1) } }
  have hΦV : Section3.SyntacticallySubsumed Φ V := by
    refine ⟨⟨hc.extension.current.guards, hc.extension.current.resets, ?_⟩,
      hc.extension.outerFresh, hc.extension.next⟩
    intro l hl
    exact ⟨hc.extension.current.locals hl, fun he => hΦ (he ▸ hl)⟩
  have hVU : Section3.SyntacticallySubsumed V U := by
    have hr := Section3.SyntacticallySubsumed.refl U
    exact ⟨⟨hr.current.guards, hr.current.resets, fun _ hl => hl.1⟩,
      Set.disjoint_left.mpr (fun _ hc hd => hd.2 hc), hr.next⟩
  have hclosed : ConcreteContextual.catalogue.IsClosed V := by
    intro p hp
    rcases hc.closed p hp.1 with hn | ⟨B, hb, hs⟩
    · exact Or.inl hn
    · refine Or.inr ⟨B, hb, ⟨⟨hs.current.guards, hs.current.resets, ?_⟩,
        hs.outerFresh, hs.next⟩⟩
      intro l hl
      exact ⟨hs.current.locals hl, fun he => contextual_branch_no_terminal hb (he ▸ hl)⟩
  intro ht
  exact ((hc.minimal V hΦV hclosed hVU).current.locals ht).2 rfl

theorem derives_no_terminal [DecidableEq Clock]
    {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (hd : Derives N F) (hn : Local.terminal ∉ N.locals) : Local.terminal ∉ F.current.locals := by
  cases hd with
  | original hc _ => exact closure_no_terminal hc hn
  | resolved hd hi hf _ =>
    exact (normalize_noCurrentTerminal _ hf.normalizes).mpr
      (hd.noCurrentTerminal ((normalize_noCurrentTerminal _ hi.normalizes).mp hn))

theorem finiteRootTableau_initial_nonterminal [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var)
    (e : EdgeLabel Clock × Section3.TransitionForm Clock Var)
    (he : e ∈ (finiteRootTableau (Clock := Clock) X root).initial) :
    Local.terminal ∉ (finiteRootTableau (Clock := Clock) X root).label e.2 := by
  have hn := derives_no_terminal he.1.1
    (by simp [Section3.StateForm.ofLocal])
  exact fun ht => hn ht.1

theorem finiteRootTableau_execution_initial_nonterminal
    [DecidableEq Clock] [Infinite Clock] (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    (τ : ℝ) (hτ : 0 < τ)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau (Clock := Clock) X root).toAutomaton h τ hτ).Execution σ) :
    e.initialState.val.1 ∉ (finiteRootTableau (Clock := Clock) X root).terminalModes := by
  obtain ⟨l, hl, _⟩ := e.initial_mem
  exact finiteRootTableau_initial_nonterminal X root (l, e.initialState.val.1.val) hl

/-- The concrete generated tableau discharges the initial-mode premise;
terminal acceptance cannot occur at an early stopping time. -/
theorem finiteRootTableau_terminal_acceptance_exhausts
    [DecidableEq Clock] [Infinite Clock] (X : Set Var) (root : Formula Var)
    (h : (finiteRootTableau (Clock := Clock) X root).TranslationReady)
    {σ : FiniteSignal (finiteRootTableau (Clock := Clock) X root).HAVar}
    (e : ((finiteRootTableau (Clock := Clock) X root).toAutomaton
      h σ.horizon σ.horizon_pos).Execution σ)
    (ht : e.finalState.val.1 ∈ (finiteRootTableau (Clock := Clock) X root).terminalModes) :
    e.boundary ⟨e.count, by omega⟩ = σ.horizon :=
  Tableau.execution_terminal_acceptance_exhausts _ h _ _ e rfl
    (finiteRootTableau_execution_initial_nonterminal X root h _ _ e) ht

end STLTableau.Section4.Finiteness
