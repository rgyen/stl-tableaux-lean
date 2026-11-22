/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Tableau.Construction.GeneratorPath
import STLTableaux.Closure.Expansion.FaithfulLevelRankBounds
import STLTableaux.Examples.UpperAlwaysClosure

/-! Complexity (Example 4.12), trace unfolding (Example 4.26), tableau
construction (Example 4.29), and symbolic merging (Example 4.38). -/

namespace STLTableau.Examples.TableauConstruction
open STLTableau.Section3 STLTableau.Section4
open scoped STL

inductive Variable where | u | t
inductive Clock where | c | c₁ | d₁ | c₂
  deriving DecidableEq

def numericalAtom (v : Variable) (a : ℝ) (r : RealRelation) : Formula Variable :=
  .atom ⟨1, fun _ => v, fun x => x 0 - a, r⟩
def uGe4 := numericalAtom .u 4 .ge
def tLe5 := numericalAtom .t 5 .le
def uGe0 := numericalAtom .u 0 .ge
def sixTwelve : BoundedTimeInterval := ⟨6,12,by norm_num,by norm_num⟩
def twoFour : BoundedTimeInterval := ⟨2,4,by norm_num,by norm_num⟩
def alwaysSixTwelve := Formula.always (.bounded sixTwelve) uGe4
def releaseFormula := Formula.release (.unbounded 0) alwaysSixTwelve tLe5

/-- Example 4.12. The release predicate has complexity 4, and the generated
unclocked predicate for `□` has complexity 2. -/
theorem release_complexity :
    (Predicate.plain releaseFormula : Predicate Clock Variable).complexity = 4 ∧
    (Predicate.plain alwaysSixTwelve : Predicate Clock Variable).complexity = 2 := by
  constructor <;> rfl

theorem introduced_predicate_strictly_smaller :
    (Predicate.plain alwaysSixTwelve : Predicate Clock Variable).complexity <
      (Predicate.plain releaseFormula : Predicate Clock Variable).complexity := by
  norm_num [release_complexity.1,release_complexity.2]

theorem release_branch_introduces_always :
    STLTableau.Judgement.predicate (.plain alwaysSixTwelve) ∈
      (ExpansionRule.plainRelease (Clock := Clock) alwaysSixTwelve tLe5).branches := by
  simp [ExpansionRule.plainRelease]

/-- Example 4.26. The next operator scopes the trace of the path suffix. -/
theorem path_trace_unfold {C S V : Type*} (labels : S → Set (Local C V))
    (hf : ∀ s, (labels s).Finite) (e : EdgeLabel C) (s : S) (tail : Path C S) :
    (Path.step e s tail).trace labels hf =
      .step ⟨e.guards,e.guards_finite,e.resets,labels s,hf s⟩ (tail.trace labels hf) := rfl

theorem path_trace_last {C S V : Type*} (labels : S → Set (Local C V))
    (hf : ∀ s, (labels s).Finite) (e : EdgeLabel C) (s : S) :
    (Path.last e s).trace labels hf =
      .last ⟨e.guards,e.guards_finite,e.resets,labels s,hf s⟩ := rfl

def releaseSuccessor : STLTableau.Section3.StateForm Clock Variable where
  guards := {⟨Clock.c,.gt,6⟩}
  guards_finite := Set.finite_singleton _
  resets := ClockResetSet.empty
  locals := {.terminal}
  locals_finite := Set.finite_singleton _

def successorState : ClosureState Clock Variable :=
  ⟨.ofState releaseSuccessor,releaseSuccessor⟩

theorem release_successor_incoming : successorState.incoming.guards = {⟨Clock.c,.gt,6⟩} ∧
    successorState.incoming.resets = ClockResetSet.empty := ⟨rfl,rfl⟩

def releaseRoot : STLTableau.Section3.StateForm Clock Variable :=
  .ofLocal (.predicate (.plain releaseFormula))
def releaseReset : ClockResetSet Clock := .singleton .c 0
def releaseUpper : Predicate Clock Variable :=
  .upper .c ● .always (.bounded sixTwelve) uGe4
def releaseClosure : STLTableau.Section3.TransitionForm Clock Variable where
  current := ⟨∅,Set.finite_empty,releaseReset,
    {.predicate (.plain releaseFormula),.predicate (.plain alwaysSixTwelve),
      .predicate releaseUpper,.predicate (.plain uGe4),.marker ●},by simp⟩
  nextPart := some releaseSuccessor
def releaseState : ClosureState Clock Variable := ⟨releaseClosure,releaseRoot⟩

theorem release_initial_incoming : releaseState.incoming.guards = ∅ ∧
    releaseState.incoming.resets = ClockResetSet.singleton Clock.c 0 := ⟨rfl,rfl⟩

theorem release_successor_compatible :
    releaseState.edge successorState.incoming successorState := ⟨rfl,rfl⟩

private theorem finite_contextual_branch (p : IntervalPredicate Clock Variable)
    (R : ExpansionRule Clock Variable) (hr : ConcreteRule p R)
    (J : STLTableau.Judgement Clock Variable) (hj : J ∈ R.branches)
    (F : STLTableau.Section3.TransitionForm Clock Variable)
    (hn : STLTableau.Section3.TransitionForm.normalize?
      (STLTableau.Section3.Judgement.ofFinite J) = some F) :
    ConcreteContextual.catalogue.Branch (Predicate.ofFinite p) releaseReset
      (F.underReset releaseReset) := by
  refine ⟨F,F,Or.inl ?_,.refl _,rfl⟩
  refine ⟨p,R,J,F,rfl,hr,hj,hn,?_⟩
  cases F with
  | mk S N =>
    congr 1
    apply STLTableau.Section3.StateForm.ext_components
    · rfl
    · cases hS : S.resets with
      | mk value finite =>
        congr 1
        funext clock
        change value clock = match value clock with | some a => some a | none => none
        cases value clock <;> rfl
    · rfl

def releaseLeftBranch : STLTableau.Section3.TransitionForm Clock Variable :=
  .ofState (.ofLocal (.predicate (.plain alwaysSixTwelve)))

theorem release_left_actual_branch : ConcreteContextual.catalogue.Branch
    (.plain releaseFormula) releaseReset (releaseLeftBranch.underReset releaseReset) := by
  apply finite_contextual_branch (.plain releaseFormula)
    (ExpansionRule.plainRelease alwaysSixTwelve tLe5) (.plainRelease _ _)
    (.predicate (.plain alwaysSixTwelve)) (by simp [ExpansionRule.plainRelease])
  rfl

def releaseOpeningBranch : STLTableau.Section3.TransitionForm Clock Variable :=
  ((STLTableau.Section3.TransitionForm.ofState (.ofLocal (.predicate releaseUpper))).union
    (.ofState (.ofLocal (.marker ●)))).underReset releaseReset

theorem release_opening_actual_branch : ConcreteContextual.catalogue.Branch
    (.plain alwaysSixTwelve) releaseReset
    (releaseOpeningBranch.underReset releaseReset) := by
  apply finite_contextual_branch (.plain alwaysSixTwelve)
    (ExpansionRule.openAlways Clock.c sixTwelve uGe4) (.openAlways _ _ _)
    (.reset releaseReset (.conj (.predicate (.upper .c ● .always sixTwelve uGe4))
      (.leftMarker ●))) (by simp [ExpansionRule.openAlways,releaseReset])
  rfl

def releaseTerminalCheck : STLTableau.Section3.TransitionForm Clock Variable :=
  (STLTableau.Section3.TransitionForm.ofState (.ofLocal (.predicate (.plain uGe4)))).union
    (.ofNextState releaseSuccessor)

theorem release_upper_actual_branch : ConcreteContextual.catalogue.Branch
    releaseUpper releaseReset (releaseTerminalCheck.underReset releaseReset) := by
  apply finite_contextual_branch (.upper Clock.c ● .always sixTwelve uGe4)
    (ExpansionRule.upperAlways Clock.c Clock.d₁ ● sixTwelve uGe4)
    (.upperAlways _ _ _ _ _ (by decide))
    (.conj (.predicate (.plain uGe4)) (.next (.conj (.clock .c .gt 6) .terminal)))
    (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hM : (STLTableau.Section3.StateForm.ofGuard (Var := Variable) ⟨Clock.c,.gt,6⟩).union
      (.ofLocal .terminal) = releaseSuccessor := by
    apply STLTableau.Section3.StateForm.ext_components
    · simp [STLTableau.Section3.StateForm.union,STLTableau.Section3.StateForm.ofGuard,
        STLTableau.Section3.StateForm.ofLocal,releaseSuccessor]
    · rfl
    · simp [STLTableau.Section3.StateForm.union,STLTableau.Section3.StateForm.ofGuard,
        STLTableau.Section3.StateForm.ofLocal,releaseSuccessor]
  change some ((STLTableau.Section3.TransitionForm.ofState
    (.ofLocal (.predicate (.plain uGe4)))).union (.ofNextState
      ((STLTableau.Section3.StateForm.ofGuard ⟨Clock.c,.gt,6⟩).union (.ofLocal .terminal)))) = _
  rw [hM]
  rfl

private theorem release_left_subsumed : STLTableau.Section3.SyntacticallySubsumed
    (releaseLeftBranch.underReset releaseReset) releaseClosure := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro g hg; cases hg
  · intro clock a ha; exact ha
  · intro l hl; have h : l = .predicate (.plain alwaysSixTwelve) := hl
    subst l; exact Or.inr (Or.inl rfl)
  · apply Set.disjoint_left.mpr
    intro clock hr hf
    exact hf.2 hr
  · intro N hn; cases hn

private theorem release_opening_subsumed : STLTableau.Section3.SyntacticallySubsumed
    (releaseOpeningBranch.underReset releaseReset) releaseClosure := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro g hg; cases hg <;> contradiction
  · intro clock a ha
    change (releaseReset.union releaseReset).value clock = some a at ha
    change releaseReset.value clock = some a
    cases clock <;> exact ha
  · intro l hl
    rcases hl with hl | hl
    · have h : l = .predicate releaseUpper := hl
      subst l; exact Or.inr (Or.inr (Or.inl rfl))
    · have h : l = .marker ● := hl
      subst l; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · apply Set.disjoint_left.mpr
    intro clock hr hf
    apply hf.2
    obtain ⟨a,ha⟩ := hr
    exact ⟨a,by cases clock <;> exact ha⟩
  · intro N hn; cases hn

private theorem release_terminal_subsumed : STLTableau.Section3.SyntacticallySubsumed
    (releaseTerminalCheck.underReset releaseReset) releaseClosure := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro g hg; cases hg <;> contradiction
  · intro clock a ha; exact ha
  · intro l hl
    rcases hl with hl | hl
    · have h : l = .predicate (.plain uGe4) := hl
      subst l; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · cases hl
  · apply Set.disjoint_left.mpr
    intro clock hr hf
    exact hf.2 hr
  · intro N hn
    cases hn
    exact ⟨_,rfl,⟨fun _ h => h,fun _ _ h => h,fun _ h => h⟩,
      Set.disjoint_left.mpr (fun _ h he => he.2 h)⟩

theorem release_closure_closed : ConcreteContextual.catalogue.IsClosed releaseClosure := by
  intro p hp
  rcases hp with hp | hp | hp | hp | hp
  · cases Local.predicate.inj hp
    exact Or.inr ⟨_,release_left_actual_branch,release_left_subsumed⟩
  · cases Local.predicate.inj hp
    exact Or.inr ⟨_,release_opening_actual_branch,release_opening_subsumed⟩
  · cases Local.predicate.inj hp
    exact Or.inr ⟨_,release_upper_actual_branch,release_terminal_subsumed⟩
  · cases Local.predicate.inj hp
    apply ConcreteContextual.zero_complexity_ruleClosed
    rfl
  · cases hp

private theorem release_finite_source {p₀ : IntervalPredicate Clock Variable}
    {R : ExpansionRule Clock Variable} (hr : ConcreteRule p₀ R)
    (hp : Predicate.ofFinite p₀ = .plain releaseFormula) :
    R = ExpansionRule.plainRelease alwaysSixTwelve tLe5 := by
  cases hr <;>
    simp only [Predicate.ofFinite,releaseFormula,Formula.release,Formula.or,
      Formula.untimedUntil,Formula.always,Formula.eventually,Predicate.plain.injEq,
      reduceCtorEq,Formula.neg.injEq,Formula.until.injEq,true_and,false_and,and_self] at hp
  rcases hp with ⟨hφ,hψ⟩
  subst hφ
  subst hψ
  rfl

private theorem release_branch_current {Λ : ClockResetSet Clock}
    {B : STLTableau.Section3.TransitionForm Clock Variable}
    (hb : ConcreteContextual.catalogue.Branch (.plain releaseFormula) Λ B) :
    Local.predicate (.plain alwaysSixTwelve) ∈ B.current.locals ∨
      Local.predicate (.plain tLe5) ∈ B.current.locals := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  change ConcreteMixed.catalogue.Branch _ _ R at hR
  rcases hR with hf | hi | ho
  · obtain ⟨p₀,rule,J,F,hp,hr,hJ,hn,rfl⟩ := hf
    have he := release_finite_source hr hp.symm
    subst rule
    have hm : Local.predicate (.plain alwaysSixTwelve) ∈
          (F.underReset ClockResetSet.empty).current.locals ∨
        Local.predicate (.plain tLe5) ∈
          (F.underReset ClockResetSet.empty).current.locals := by
      have hd : J = .predicate (.plain alwaysSixTwelve) ∨
          J = .conj (.predicate (.plain tLe5))
            (.next (.predicate (.plain releaseFormula))) ∨
          J = .conj (.predicate (.plain tLe5)) (.next .terminal) := by
        simpa [ExpansionRule.plainRelease,releaseFormula] using hJ
      rcases hd with rfl | rfl | rfl
      all_goals
        simp only [STLTableau.Section3.Judgement.ofFinite,
          STLTableau.Section3.TransitionForm.normalize?,
          STLTableau.Section3.TransitionForm.ofState,STLTableau.Section3.TransitionForm.union,
          STLTableau.Section3.TransitionForm.unionNext,
          STLTableau.Section3.TransitionForm.ofNextState,
          STLTableau.Section3.StateForm.ofLocal,STLTableau.Section3.StateForm.union,
          Option.some.injEq,Option.bind_eq_bind,Option.bind_some,Option.pure_def,
          Set.empty_union,Set.singleton_union] at hn
        cases hn
        simp [STLTableau.Section3.TransitionForm.underReset,Predicate.ofFinite,
          STLTableau.Section3.StateForm.empty]
    exact hm.elim (fun h => Or.inl ((ha.current_plain _).2 h))
      (fun h => Or.inr ((ha.current_plain _).2 h))
  · obtain ⟨p₀,Bs,J,F,hp,_,_,_,_⟩ := hi
    cases p₀ <;> cases hp
  · obtain ⟨clock,m,kind,a,φ,F,hp,_,_⟩ := ho
    cases kind <;> simp only [releaseFormula,Formula.release,
      STLTableau.UnboundedClocked.formula,Formula.always,Formula.eventually,
      Predicate.plain.injEq,Formula.neg.injEq,Formula.until.injEq,
      reduceCtorEq,false_and,and_false] at hp

theorem release_closed_extension_contains_always
    (Θ : STLTableau.Section3.TransitionForm Clock Variable)
    (he : STLTableau.Section3.SyntacticallySubsumed (.ofState releaseRoot) Θ)
    (hc : ConcreteContextual.catalogue.IsClosed Θ)
    (hb : STLTableau.Section3.SyntacticallySubsumed Θ releaseClosure) :
    Local.predicate (.plain alwaysSixTwelve) ∈ Θ.current.locals := by
  have hp : Local.predicate (.plain releaseFormula) ∈ Θ.current.locals :=
    he.current.locals rfl
  rcases hc _ hp with hn | ⟨B,hB,hsub⟩
  · exact (hn ⟨_,ConcreteContextual.branch_change_reset release_left_actual_branch
      Θ.current.resets |>.choose_spec⟩).elim
  · rcases release_branch_current hB with hg | ht
    · exact hsub.current.locals hg
    · have hbad := hb.current.locals (hsub.current.locals ht)
      simp [releaseClosure,releaseFormula,alwaysSixTwelve,uGe4,tLe5,numericalAtom,
        Formula.release,Formula.always,Formula.eventually,releaseUpper] at hbad

private theorem opening_finite_source {p₀ : IntervalPredicate Clock Variable}
    {R : ExpansionRule Clock Variable} (hr : ConcreteRule p₀ R)
    (hp : Predicate.ofFinite p₀ = .plain alwaysSixTwelve) :
    ∃ clock, R = ExpansionRule.openAlways clock sixTwelve uGe4 := by
  cases hr <;>
    simp only [Predicate.ofFinite,alwaysSixTwelve,Formula.release,Formula.or,
      Formula.untimedUntil,Formula.always,Formula.eventually,Predicate.plain.injEq,
      reduceCtorEq,Formula.neg.injEq,Formula.until.injEq,true_and,false_and,and_self,
      TimeInterval.bounded.injEq] at hp
  rcases hp with ⟨hI,hφ⟩
  subst hI
  subst hφ
  exact ⟨_,rfl⟩

def HasOpening (S : STLTableau.Section3.StateForm Clock Variable) : Prop :=
  ∃ clock m, S.resets.value clock = some 0 ∧
    Local.predicate (.upper clock m .always (.bounded sixTwelve) uGe4) ∈ S.locals ∧
    Local.marker m ∈ S.locals

private theorem hasOpening_alpha (S : STLTableau.Section3.StateForm Clock Variable)
    (e : Equiv.Perm Clock) : HasOpening (S.alphaReset e) ↔ HasOpening S := by
  constructor
  · rintro ⟨clock,m,hr,⟨l,hl,he⟩,⟨l',hl',he'⟩⟩
    refine ⟨e.symm clock,m,hr,?_,?_⟩
    · cases l with
      | terminal => cases he
      | marker n => cases he
      | predicate p =>
        cases p with
        | plain φ => cases he
        | bounded clock₁ clock₂ b q kind I φ => cases he
        | upper clock₁ b kind I φ =>
          simp only [Local.rename,Predicate.rename,Local.predicate.injEq,
            Predicate.upper.injEq] at he
          rcases he with ⟨hc,rfl,rfl,rfl,rfl⟩
          simpa [← hc] using hl
    · cases l' with
      | terminal => cases he'
      | predicate p => cases he'
      | marker n => cases he'; exact hl'
  · rintro ⟨clock,m,hr,hp,hm⟩
    refine ⟨e clock,m,?_,⟨_,hp,?_⟩,⟨_,hm,rfl⟩⟩
    · simpa [STLTableau.Section3.StateForm.alphaReset,STLTableau.Section3.StateForm.rename,
        ClockResetSet.rename] using hr
    · rfl

private theorem opening_branch_hasOpening {Λ : ClockResetSet Clock}
    {B : STLTableau.Section3.TransitionForm Clock Variable}
    (hb : ConcreteContextual.catalogue.Branch (.plain alwaysSixTwelve) Λ B) :
    HasOpening B.current := by
  obtain ⟨R,A,hR,ha,rfl⟩ := hb
  have hraw : HasOpening R.current := by
    rcases hR with hf | hi | ho
    · obtain ⟨p₀,rule,J,F,hp,hr,hJ,hn,rfl⟩ := hf
      obtain ⟨clock,he⟩ := opening_finite_source hr hp.symm
      subst rule
      have hd : J = .reset (ClockResetSet.singleton clock 0)
          (.conj (.predicate (.upper clock ○ .always sixTwelve uGe4)) (.leftMarker ○)) ∨
          J = .reset (ClockResetSet.singleton clock 0)
          (.conj (.predicate (.upper clock ● .always sixTwelve uGe4)) (.leftMarker ●)) := by
        simpa [ExpansionRule.openAlways] using hJ
      rcases hd with rfl | rfl
      all_goals
        simp only [STLTableau.Section3.Judgement.ofFinite,
          STLTableau.Section3.TransitionForm.normalize?,
          STLTableau.Section3.TransitionForm.ofState,STLTableau.Section3.TransitionForm.union,
          STLTableau.Section3.TransitionForm.unionNext,
          STLTableau.Section3.StateForm.ofLocal,STLTableau.Section3.StateForm.union,
          Option.pure_def,Option.bind_eq_bind,Option.bind_some,Set.union_empty,
          Set.union_singleton,Option.map_some,Option.some.injEq] at hn
        cases hn
        refine ⟨clock,_,?_,Or.inr rfl,Or.inl rfl⟩
        change (match (if clock = clock then some (0 : NNReal) else none) with
          | some a => some a | none => none) = some 0
        simp
    · obtain ⟨p₀,Bs,J,F,hp,_,_,_,_⟩ := hi
      cases p₀ <;> cases hp
    · obtain ⟨clock,m,kind,a,φ,F,hp,_,_⟩ := ho
      cases kind <;> simp [alwaysSixTwelve,STLTableau.UnboundedClocked.formula,
        Formula.always,Formula.eventually] at hp
  obtain ⟨clock,m,hr,hp,hm⟩ :=
    (ha.current_state_observation HasOpening hasOpening_alpha).2 hraw
  exact ⟨clock,m,by simp [STLTableau.Section3.TransitionForm.underReset,
    ClockResetSet.union,hr],hp,hm⟩

theorem release_closed_extension_opening
    (Θ : STLTableau.Section3.TransitionForm Clock Variable)
    (he : STLTableau.Section3.SyntacticallySubsumed (.ofState releaseRoot) Θ)
    (hc : ConcreteContextual.catalogue.IsClosed Θ)
    (hb : STLTableau.Section3.SyntacticallySubsumed Θ releaseClosure) :
    Θ.current.resets.value Clock.c = some 0 ∧
      Local.predicate releaseUpper ∈ Θ.current.locals ∧ Local.marker ● ∈ Θ.current.locals := by
  have hg := release_closed_extension_contains_always Θ he hc hb
  rcases hc _ hg with hn | ⟨B,hB,hsub⟩
  · obtain ⟨B,hB⟩ := ConcreteContextual.branch_change_reset
      release_opening_actual_branch Θ.current.resets
    exact (hn ⟨B,hB⟩).elim
  · obtain ⟨clock,m,hr,hp,hm⟩ := opening_branch_hasOpening hB
    have hpu := hsub.current.locals hp
    have hpt := hb.current.locals hpu
    have hcm : clock = Clock.c ∧ m = ● := by
      simpa [releaseClosure,releaseUpper] using hpt
    rcases hcm with ⟨rfl,rfl⟩
    exact ⟨hsub.current.resets _ _ hr,hpu,hsub.current.locals hm⟩

theorem release_closed_extension_checked
    (Θ : STLTableau.Section3.TransitionForm Clock Variable)
    (he : STLTableau.Section3.SyntacticallySubsumed (.ofState releaseRoot) Θ)
    (hc : ConcreteContextual.catalogue.IsClosed Θ)
    (hb : STLTableau.Section3.SyntacticallySubsumed Θ releaseClosure) :
    UpperAlwaysClosure.Checked Θ Clock.c sixTwelve
      ⟨1,fun _ => Variable.u,fun x => x 0 - 4,.ge⟩ := by
  have hp := (release_closed_extension_opening Θ he hc hb).2.1
  exact UpperAlwaysClosure.ruleClosed_forced Clock.c Clock.d₁ (by decide) sixTwelve
    ⟨1,fun _ => Variable.u,fun x => x 0 - 4,.ge⟩ rfl rfl rfl hb (hc _ hp)

private theorem release_body_closed :
    releaseClosure.bodyFreeClocks \ releaseClosure.current.resets.clocks = ∅ := by
  ext clock
  suffices clock = Clock.c →
      ∃ a : NNReal, (if clock = Clock.c then some 0 else none) = some a by
    simpa [releaseClosure,STLTableau.Section3.TransitionForm.bodyFreeClocks,
    STLTableau.Section3.StateForm.localClocks,Local.freeClocks,Local.toJudgement,
    STLTableau.Section3.Judgement.freeClocks,releaseUpper,releaseSuccessor,
    STLTableau.Section3.StateForm.freeClocks,STLTableau.Section3.StateForm.guardClocks,
      releaseReset,ClockResetSet.clocks,ClockResetSet.singleton] using this
  intro hclock
  subst clock
  exact ⟨0,rfl⟩

theorem release_closure_isClosure : ConcreteContextual.catalogue.IsClosure
    (.ofState releaseRoot) releaseClosure := by
  refine ⟨?_,release_closure_closed,?_⟩
  · refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · intro g hg; cases hg
    · intro clock a ha; cases ha
    · intro l hl
      have h : l = .predicate (.plain releaseFormula) := hl
      subst l; exact Or.inl rfl
    · simp [STLTableau.Section3.TransitionForm.ofState,
        STLTableau.Section3.TransitionForm.bodyFreeClocks,
        releaseRoot,STLTableau.Section3.StateForm.ofLocal,STLTableau.Section3.StateForm.localClocks,
        Local.freeClocks,Local.toJudgement,STLTableau.Section3.Judgement.freeClocks]
    · intro N hn; cases hn
  · intro Θ he hc hb
    have hG := release_closed_extension_contains_always Θ he hc hb
    obtain ⟨hreset,hupper,hmarker⟩ := release_closed_extension_opening Θ he hc hb
    obtain ⟨hatom,⟨M,hM,hguard⟩,⟨N,hN,hterminal⟩⟩ := release_closed_extension_checked Θ he hc hb
    have hMN : M = N := Option.some.inj (hM.symm.trans hN)
    subst N
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · intro g hg; cases hg
    · intro clock a ha
      by_cases hclock : clock = Clock.c
      · subst clock
        have ha0 : (0 : NNReal) = a := Option.some.inj ha
        subst a
        exact hreset
      · change (if clock = Clock.c then some 0 else none) = some a at ha
        rw [if_neg hclock] at ha
        cases ha
    · intro l hl
      rcases hl with hl | hl | hl | hl | hl
      · subst l; exact he.current.locals rfl
      · subst l; exact hG
      · subst l; exact hupper
      · subst l; exact hatom
      · subst l; exact hmarker
    · rw [release_body_closed]
      exact Set.disjoint_empty _
    · intro K hK
      cases hK
      refine ⟨M,hM,⟨?_,?_,?_⟩,?_⟩
      · intro g hg
        have : g = ⟨Clock.c,.gt,6⟩ := hg
        subst g; exact hguard
      · intro clock a ha; cases ha
      · intro l hl
        have : l = Local.terminal := hl
        subst l; exact hterminal
      · simp [releaseSuccessor,STLTableau.Section3.StateForm.localClocks,Local.freeClocks,
          Local.toJudgement,STLTableau.Section3.Judgement.freeClocks]

theorem release_successor_contextual_self_closure : ConcreteContextual.catalogue.IsClosure
    (.ofState releaseSuccessor) (.ofState releaseSuccessor) := by
  apply ClosureCatalogue.IsClosure.self
  intro p hp
  have h : Local.predicate p = Local.terminal := hp
  cases h

noncomputable def releaseTableau := Generated.closureTableau ConcreteContextual.catalogue
  (Set.univ : Set Variable) (Set.univ : Set Clock) releaseRoot

/-- Example 4.29. The incoming transition of the initial state resets `c` to zero. -/
theorem release_generated_initial :
    (releaseState.incoming,releaseState) ∈ releaseTableau.initial :=
  ⟨release_closure_isClosure,rfl,rfl⟩

/-- Example 4.29. The successor transition has clock constraint `c > 6`. -/
theorem release_generated_edge :
    (releaseState,successorState.incoming,successorState) ∈ releaseTableau.edges :=
  ⟨release_closure_isClosure,release_successor_contextual_self_closure,
    release_successor_compatible⟩

theorem release_generated_final : successorState ∈ releaseTableau.states ∧
    successorState ∈ releaseTableau.final :=
  ⟨release_successor_contextual_self_closure,rfl⟩

theorem release_generated_accepting_path :
    (Path.step releaseState.incoming releaseState
      (.last successorState.incoming successorState)).run releaseTableau ∧
    (Path.step releaseState.incoming releaseState
      (.last successorState.incoming successorState)).accepting releaseTableau := by
  have hv : (Path.step releaseState.incoming releaseState
      (.last successorState.incoming successorState)).valid releaseTableau :=
    ⟨release_closure_isClosure,release_generated_final.1,release_generated_edge⟩
  exact ⟨⟨hv,release_generated_initial⟩,⟨hv,release_generated_final.2⟩⟩

def mergeResets : ClockResetSet Clock :=
  (ClockResetSet.singleton .d₁ 0).union (ClockResetSet.singleton .c₂ 0)
def mergeBefore : STLTableau.Section3.Judgement Clock Variable :=
  .conj (.clock .c₁ .ge 0) (.reset mergeResets
    (.conj (.marker ●) (.conj
      (.predicate (.bounded .c₁ .d₁ ● ○ .always (.bounded twoFour) uGe0))
      (.predicate (.upper .c₂ ● .always (.bounded twoFour) uGe0)))))
def mergeAfter : STLTableau.Section3.Judgement Clock Variable :=
  .conj (.clock .c₁ .ge 0) (.conj (.marker ●)
    (.predicate (.upper .c₁ ● .always (.bounded twoFour) uGe0)))

/-- Example 4.38. The judgements before and after symbolic merging are equivalent. -/
theorem symbolic_merging (σ : FiniteSignal Variable) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    mergeBefore.holds σ P α k ↔ mergeAfter.holds σ P α k := by
  have hc : mergeResets.apply α Clock.c₁ = α Clock.c₁ := by
    rfl
  have hd : mergeResets.apply α Clock.d₁ = 0 := by
    rfl
  have he : mergeResets.apply α Clock.c₂ = 0 := by
    rfl
  have hg : (0 : ℝ) ≤ α Clock.c₁ := (α Clock.c₁).coe_nonneg
  have hm := STLTableau.Section3.Judgement.predicate_merge_connected σ P
      (mergeResets.apply α) k Clock.c₁ Clock.d₁ Clock.c₂ ● ○ ●
      .always (.bounded twoFour) uGe0 (by simp [hd,he,Marker.disj,MarkedLT])
      (by rw [hc,he]; simpa only [Marker.imp,Marker.Includes,MarkedLT,NNReal.coe_zero,and_true]
        using lt_or_eq_of_le hg)
  have hr : STLTableau.Section3.Judgement.holds σ P (mergeResets.apply α) k
        (.predicate (.upper Clock.c₁ ● .always (.bounded twoFour) uGe0)) ↔
        STLTableau.Section3.Judgement.holds σ P α k
        (.predicate (.upper Clock.c₁ ● .always (.bounded twoFour) uGe0)) := by
      apply STLTableau.Section3.Judgement.holds_congr_of_agree
      intro clock h
      have : clock = Clock.c₁ := h
      subst clock
      exact hc
  simpa [mergeBefore,mergeAfter,STLTableau.Section3.Judgement.holds,ClockRelation.Holds]
    using and_congr Iff.rfl (hm.trans hr)

end STLTableau.Examples.TableauConstruction
