import STLTableaux.Closure.Expansion.BranchwiseExpansion
import STLTableaux.Closure.Support.BranchFreeClocks
import STLTableaux.Closure.Expansion.FixedExpansionOrder

/-! Search toward a fixed target using one-step expansions. The termination
argument in Lemma C.15 uses this expansion family. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace ConcreteContextual

/-- Change a represented branch's inherited resets from those of the target
back to those of the source. The branch only reads free clocks of `p`, so
the target's extra resets cannot capture a clock made free by the change. -/
theorem branch_under_source_subsumed [DecidableEq Clock]
    {p : Predicate Clock Var} {F G B : TransitionForm Clock Var}
    (hp : Local.predicate p ∈ F.current.locals) (hFG : SyntacticallySubsumed F G)
    (hB : catalogue.Branch p G.current.resets B) (hBG : SyntacticallySubsumed B G) :
    ∃ A, catalogue.Branch p F.current.resets A ∧ SyntacticallySubsumed A G := by
  obtain ⟨R, A, hR, hA, rfl⟩ := hB
  refine ⟨A.underReset F.current.resets, ⟨R, A, hR, hA, rfl⟩, ?_⟩
  refine ⟨⟨hBG.current.guards, ?_, hBG.current.locals⟩, ?_, hBG.next⟩
  · intro c a hc
    change (A.current.resets.union F.current.resets).value c = some a at hc
    cases he : A.current.resets.value c with
    | none => exact hFG.current.resets c a (by simpa only [ClockResetSet.union, he] using hc)
    | some b =>
        apply hBG.current.resets c a
        change (A.current.resets.union G.current.resets).value c = some a
        simpa only [ClockResetSet.union, he] using hc
  · apply Set.disjoint_left.2
    intro c hcG hc
    change c ∈ A.bodyFreeClocks \ (A.current.resets.union F.current.resets).clocks at hc
    have hn := hc.2
    rw [ClockResetSet.clocks_union] at hn
    have hcA : c ∈ A.freeClocks := Or.inr ⟨hc.1, fun h => hn (Or.inl h)⟩
    have hcP := ConcreteMixed.branch_freeClocks hR (hA.freeClocks ▸ hcA)
    exact Set.disjoint_left.1 hFG.outerFresh hcG
      ⟨Or.inl ⟨.predicate p, hp, hcP⟩, fun h => hn (Or.inr h)⟩

/-- Global minimality among all rule-closed targets implies minimality for
one of their witnessing branches. This implication need not be reversible. -/
theorem branchwise_of_pExpansion [DecidableEq Clock]
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hp : Local.predicate p ∈ F.current.locals) (h : catalogue.PExpansion p F G) :
    catalogue.BranchwisePExpansion p F G := by
  rcases h with hi | ⟨hopen, hFG, hclosed, hmin⟩
  · exact Or.inl hi
  · rcases hclosed with hnone | ⟨B, hB, hBG⟩
    · exact (hnone (branch_exists_of_not_ruleClosed hopen G.current.resets)).elim
    obtain ⟨A, hA, hAG⟩ := branch_under_source_subsumed hp hFG hB hBG
    exact Or.inr ⟨A, hA, hFG, hAG,
      fun H hFH hAH hHG => hmin H hFH (Or.inr (branch_rebase hA hAH)) hHG⟩

theorem alphaBranchwise_of_alphaPExpansion [DecidableEq Clock]
    {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (hp : Local.predicate p ∈ F.current.locals) (h : AlphaPExpansion p F G) :
    AlphaBranchwisePExpansion p F G := by
  obtain ⟨Fa, ha, hstep⟩ := h
  exact ⟨Fa, ha, branchwise_of_pExpansion (by rwa [ha.current]) hstep⟩

/-- Proposition 4.16: keep the satisfied branch fixed when minimizing below
the normalized union, preserving truth and both scoped invariants. -/
theorem satisfied_alphaBranchwise_preserving [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ F.current.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ G, AlphaBranchwisePExpansion p F G ∧ G.holds σ P α k ∧
      G.EvaluatedInvariant σ P α k ∧ G.UnderlyingStable σ P := by
  classical
  by_cases hc : catalogue.RuleClosedFor F p
  · exact ⟨F, ⟨F, .refl F, Or.inl ⟨hc, rfl⟩⟩, hs, hi, hst⟩
  · obtain ⟨e, B, U, hf, hFU, hb, hBU, hSat, hInv, hStable⟩ :=
      preserving_union_for F p hp hc σ P α k hs hi hst
    obtain ⟨G, hstep, hGU⟩ := catalogue.branchwisePExpansion_exists_below hb hFU hBU
    exact ⟨G, ⟨F.alphaNext e, .step F e hf (.refl _), hstep⟩,
      hGU.sound σ P α k hSat, hGU.evaluatedInvariant σ P α k hInv,
      hGU.underlyingStable σ P hStable⟩

end ConcreteContextual

namespace ExpansionFamily

/-- A finite sequence of single-predicate expansions, where the predicate
chosen at every edge must occur in that edge's source. -/
inductive CurrentExpansionPath
    (Step : Predicate Clock Var → TransitionForm Clock Var → TransitionForm Clock Var → Prop) :
    TransitionForm Clock Var → TransitionForm Clock Var → Prop where
  | nil (F) : CurrentExpansionPath Step F F
  | cons {p F G H} : Local.predicate p ∈ F.current.locals → Step p F G →
      CurrentExpansionPath Step G H → CurrentExpansionPath Step F H

namespace CurrentExpansionPath

variable {Step Step' : Predicate Clock Var → TransitionForm Clock Var →
    TransitionForm Clock Var → Prop}

theorem append {F G H : TransitionForm Clock Var} (h : CurrentExpansionPath Step F G)
    (g : CurrentExpansionPath Step G H) : CurrentExpansionPath Step F H := by
  induction h with
  | nil => exact g
  | cons hp hs ht ih => exact .cons hp hs (ih g)

theorem mono {F G : TransitionForm Clock Var} (h : CurrentExpansionPath Step F G)
    (hs : ∀ {p F G}, Local.predicate p ∈ F.current.locals → Step p F G → Step' p F G) :
    CurrentExpansionPath Step' F G := by
  induction h with
  | nil F => exact .nil F
  | cons hp hstep ht ih => exact .cons hp (hs hp hstep) ih

theorem mem_some_level {F G : TransitionForm Clock Var} (h : CurrentExpansionPath Step F G) :
    ∃ i, G ∈ BranchwiseExpansion.level Step
      (fun A => {p | Local.predicate p ∈ A.current.locals}) F i := by
  let current := fun A : TransitionForm Clock Var => {p | Local.predicate p ∈ A.current.locals}
  have aux : ∀ {A B : TransitionForm Clock Var}, CurrentExpansionPath Step A B →
      ∀ i, A ∈ BranchwiseExpansion.level Step current F i →
      ∃ j, B ∈ BranchwiseExpansion.level Step current F j := by
    intro A B hAB
    induction hAB with
    | nil => exact fun i hi => ⟨i, hi⟩
    | cons hp hs ht ih =>
        intro i hi
        exact ih (i + 1) ⟨_, hi, _, hp, hs⟩
  exact aux h 0 rfl

end CurrentExpansionPath

theorem Sequence.currentExpansionPath
    {Step : Predicate Clock Var → TransitionForm Clock Var → TransitionForm Clock Var → Prop}
    (mono : ∀ {p F G}, Step p F G → F.current.locals ⊆ G.current.locals)
    {ps F G} (h : Sequence Step ps F G)
    (hp : ∀ p ∈ ps, Local.predicate p ∈ F.current.locals) :
    CurrentExpansionPath Step F G := by
  induction h with
  | nil F => exact .nil F
  | cons hs ht ih =>
      exact .cons (hp _ List.mem_cons_self) hs
        (ih (fun p hm => mono hs (hp p (List.mem_cons_of_mem _ hm))))

theorem level_currentExpansionPath
    {Step : Predicate Clock Var → TransitionForm Clock Var → TransitionForm Clock Var → Prop}
    (mono : ∀ {p F G}, Step p F G → F.current.locals ⊆ G.current.locals)
    {F G : TransitionForm Clock Var} (i : ℕ) (h : G ∈ level Step F i) :
    CurrentExpansionPath Step F G := by
  induction i generalizing G with
  | zero =>
      have hGF : G = F := h
      subst G
      exact .nil F
  | succ i ih =>
      obtain ⟨H, hH, ps, hen, hseq⟩ := h
      exact (ih hH).append (hseq.currentExpansionPath mono (fun p hp => (hen.2 p).1 hp))

end ExpansionFamily

namespace ConcreteContextual
open ExpansionFamily

section
variable [DecidableEq Clock]

/-- A literal target-guided prefix: each step closes a current open predicate
and stays between the initial transition form and the fixed target. -/
structure ClosureGuidedPrefix (F U : TransitionForm Clock Var) (n : ℕ)
    (A : ℕ → TransitionForm Clock Var) : Prop where
  start : A 0 = F
  step : ∀ i < n, ∃ p ∈ branchwiseCurrent (A i),
    ¬ catalogue.RuleClosedFor (A i) p ∧ catalogue.BranchwisePExpansion p (A i) (A (i + 1))
  between : ∀ i ≤ n, SyntacticallySubsumed F (A i) ∧ SyntacticallySubsumed (A i) U

theorem ClosureGuidedPrefix.mem_level {F U : TransitionForm Clock Var} {n : ℕ}
    {A : ℕ → TransitionForm Clock Var} (h : ClosureGuidedPrefix F U n A) :
    ∀ i ≤ n, A i ∈ branchwiseExpansionLevel F i := by
  intro i
  induction i with
  | zero => exact fun _ => h.start
  | succ i ih =>
    intro hi
    obtain ⟨p, hp, _, hs⟩ := h.step i (by omega)
    exact ⟨A i, ih (by omega), p, hp, hs⟩

/-- If the guided sequence has not yet reached its fixed closure, a
current predicate not yet rule-closed has a next expansion below it. -/
private theorem expansion_below_closure {F A U : TransitionForm Clock Var}
    (hc : catalogue.IsClosure F U) (hFA : SyntacticallySubsumed F A)
    (hAU : SyntacticallySubsumed A U) (hne : A ≠ U) :
    ∃ p ∈ branchwiseCurrent A, ¬ catalogue.RuleClosedFor A p ∧
      ∃ B, catalogue.BranchwisePExpansion p A B ∧ SyntacticallySubsumed B U := by
  classical
  have hopen : ¬ catalogue.IsClosed A := fun hA =>
    hne (hAU.antisymm (hc.minimal A hFA hA hAU))
  unfold ClosureCatalogue.IsClosed at hopen
  push Not at hopen
  obtain ⟨p, hp, hpo⟩ := hopen
  rcases hc.closed p (hAU.current.locals hp) with hn | ⟨C, hC, hCU⟩
  · exact (hn (branch_exists_of_not_ruleClosed hpo U.current.resets)).elim
  · obtain ⟨C', hC', hC'U⟩ := branch_under_source_subsumed hp hAU hC hCU
    exact ⟨p, hp, hpo, catalogue.branchwisePExpansion_exists_below hC' hAU hC'U⟩

/-- The fixed-target step in C.15: failing to reach the closure by depth
`N` constructs a strictly open guided prefix of length `N + 1`. -/
theorem guided_closure_of_length_bound {F U : TransitionForm Clock Var} (N : ℕ)
    (hc : catalogue.IsClosure F U)
    (bound : ∀ n A, ClosureGuidedPrefix F U n A → n ≤ N) :
    ∃ i ≤ N, U ∈ branchwiseExpansionLevel F i := by
  classical
  by_contra h
  have build : ∀ n ≤ N + 1, ∃ A, ClosureGuidedPrefix F U n A := by
    intro n
    induction n with
    | zero =>
      exact fun _ => ⟨fun _ => F, rfl, fun i hi => (Nat.not_lt_zero i hi).elim,
        fun _ _ => ⟨.refl F, hc.extension⟩⟩
    | succ n ih =>
      intro hn
      obtain ⟨A, hA⟩ := ih (by omega)
      have hb := hA.between n le_rfl
      have hne : A n ≠ U := fun he => h ⟨n, by omega, he ▸ hA.mem_level n le_rfl⟩
      obtain ⟨p, hp, ho, B, hE, hBU⟩ := expansion_below_closure hc hb.1 hb.2 hne
      refine ⟨Function.update A (n + 1) B, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (show 0 ≠ n + 1 by omega)]
        exact hA.start
      · intro i hi
        by_cases he : i = n
        · subst i
          simp only [Function.update_self, Function.update_of_ne (show n ≠ n + 1 by omega)]
          exact ⟨p, hp, ho, hE⟩
        · simpa only [Function.update_of_ne (show i ≠ n + 1 by omega),
            Function.update_of_ne (show i + 1 ≠ n + 1 by omega)] using hA.step i (by omega)
      · intro i hi
        by_cases he : i = n + 1
        · subst i
          simp only [Function.update_self]
          exact ⟨hb.1.trans hE.extension, hBU⟩
        · rw [Function.update_of_ne he]
          exact hA.between i (by omega)
  obtain ⟨A, hA⟩ := build (N + 1) le_rfl
  have := bound (N + 1) A hA
  omega

theorem branchwiseExpansionLevel_subset_alpha (F : TransitionForm Clock Var) (n : ℕ) :
    branchwiseExpansionLevel F n ⊆ alphaBranchwiseExpansionLevel F n := by
  induction n with
  | zero => exact Set.Subset.refl _
  | succ n ih =>
    rintro G ⟨H, hH, p, hp, hs⟩
    exact ⟨H, ih hH, p, hp, H, .refl _, hs⟩

private theorem literal_level_currentExpansionPath {F U : TransitionForm Clock Var}
    (n : ℕ) (h : U ∈ branchwiseExpansionLevel F n) :
    CurrentExpansionPath catalogue.BranchwisePExpansion F U := by
  induction n generalizing U with
  | zero =>
    have he : U = F := h
    subst U
    exact .nil F
  | succ n ih =>
    obtain ⟨H, hH, p, hp, hs⟩ := h
    exact (ih hH).append (.cons hp hs (.nil U))

/-- Each literal guided step closes an open predicate, hence strictly
increases the number of components, which is bounded by the fixed target. -/
theorem ClosureGuidedPrefix.length_le_componentCount {F U : TransitionForm Clock Var}
    {n : ℕ} {A : ℕ → TransitionForm Clock Var} (h : ClosureGuidedPrefix F U n A) :
    n ≤ U.componentCount := by
  have aux : ∀ i ≤ n, i ≤ (A i).componentCount := by
    intro i
    induction i with
    | zero => exact fun _ => Nat.zero_le _
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      obtain ⟨p, _, ho, hs⟩ := h.step i hi'
      have hle := hs.extension.componentCount_le
      have hlt : (A i).componentCount < (A (i + 1)).componentCount := by
        by_contra hn
        have he := hs.extension.eq_of_componentCount_eq (Nat.le_antisymm hle (by omega))
        exact ho (he.symm ▸ branchwisePExpansion_target_ruleClosed hs)
      have := ih (Nat.le_of_lt hi')
      omega
  exact (aux n le_rfl).trans (h.between n le_rfl).2.componentCount_le

/-- A literal path to the minimal closure from the same target-guided
argument as C.15, using the component count of this one fixed target. -/
theorem minimal_closure_guided_path {F U : TransitionForm Clock Var}
    (hc : catalogue.IsClosure F U) :
    CurrentExpansionPath catalogue.BranchwisePExpansion F U := by
  obtain ⟨i, _, hi⟩ := guided_closure_of_length_bound U.componentCount hc
    (fun _ _ h => h.length_le_componentCount)
  exact literal_level_currentExpansionPath i hi

end

/-- Every minimal closure has a finite branchwise derivation, using the
literal representatives of the given closure. -/
theorem minimal_closure_branchwise_path [DecidableEq Clock]
    {F U : TransitionForm Clock Var} (hc : catalogue.IsClosure F U) :
    CurrentExpansionPath catalogue.BranchwisePExpansion F U := by
  obtain ⟨i, hm⟩ := minimal_closure_mem_expansion_level hc
  exact (level_currentExpansionPath literalStepLaws.current_mono i hm).mono
    (fun hp hs => branchwise_of_pExpansion hp hs)

theorem minimal_closure_mem_branchwise_level [DecidableEq Clock]
    {F U : TransitionForm Clock Var} (hc : catalogue.IsClosure F U) :
    ∃ i, U ∈ branchwiseExpansionLevel F i :=
  (minimal_closure_branchwise_path hc).mem_some_level

/-- The appendix's fixed-order search works inside the larger branchwise
family. Its auxiliary round count is independent of one-step level depth. -/
theorem minimal_closure_mem_fixed_branchwise_rounds [DecidableEq Clock]
    (order : TransitionForm Clock Var → List (Predicate Clock Var))
    (enumerates : ∀ F, EnumeratesCurrent (order F) F)
    {F U : TransitionForm Clock Var} (hc : catalogue.IsClosure F U) :
    ∃ i, U ∈ fixedLevel catalogue.BranchwisePExpansion order F i := by
  obtain ⟨i, hz⟩ := literal_level_rank_eventually_zero F
  have hm := minimal_closure_mem_fixed_expansion_level_at_rank_zero order enumerates hc i
    (hz i le_rfl)
  refine ⟨i, ?_⟩
  have aux : ∀ n, catalogue.fixedExpansionLevel order F n ⊆
      fixedLevel catalogue.BranchwisePExpansion order F n := by
    intro n
    induction n with
    | zero => exact Set.Subset.refl _
    | succ n ih =>
        rintro G ⟨H, hH, hseq⟩
        have convert : ∀ {ps : List (Predicate Clock Var)} {A B : TransitionForm Clock Var},
            catalogue.ExpansionSequence ps A B →
            (∀ p ∈ ps, Local.predicate p ∈ A.current.locals) →
            Sequence catalogue.BranchwisePExpansion ps A B := by
          intro ps A B seq
          induction seq with
          | nil A => exact fun _ => .nil A
          | cons hs ht ihseq =>
              intro hp
              exact .cons (branchwise_of_pExpansion (hp _ List.mem_cons_self) hs)
                (ihseq (fun p hmem => hs.extension.current.locals
                  (hp p (List.mem_cons_of_mem _ hmem))))
        exact ⟨H, ih hH, convert hseq (fun p hp => ((enumerates H).2 p).1 hp)⟩
  exact aux i hm

/-- A satisfied minimal closure below a satisfied, closed branchwise
extension. The chosen source representative and both paths are explicit. -/
theorem satisfied_closure_branchwise_path [DecidableEq Clock] [Infinite Clock]
    (F : TransitionForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : F.holds σ P α k) (hi : F.EvaluatedInvariant σ P α k)
    (hst : F.UnderlyingStable σ P) :
    ∃ G Fa U, CurrentExpansionPath AlphaBranchwisePExpansion F G ∧
      catalogue.IsClosed G ∧ G.holds σ P α k ∧ G.EvaluatedInvariant σ P α k ∧
      NextAlphaPath F Fa ∧ catalogue.IsClosure Fa U ∧
      CurrentExpansionPath catalogue.BranchwisePExpansion Fa U ∧
      SyntacticallySubsumed U G ∧ U.holds σ P α k ∧
      U.EvaluatedInvariant σ P α k ∧ U.UnderlyingStable σ P := by
  obtain ⟨i, hz⟩ := alpha_level_rank_eventually_zero F
  obtain ⟨G, hm, hsat, hinv, hstable⟩ := alpha_level_satisfied F σ P α k hs hi hst i
  have hclosed := (familyRank_zero_iff_closed (alpha_expansionLevel_bounded F i)).1
    (hz i le_rfl) G hm
  obtain ⟨Fa, hp, hFaG⟩ := alpha_level_source F i hm
  obtain ⟨U, hc, hUG⟩ := catalogue.exists_minimal_closed_extension_below hFaG hclosed
  have hG := (level_currentExpansionPath alphaStepLaws.current_mono i hm).mono
    (Step' := AlphaBranchwisePExpansion (Clock := Clock) (Var := Var))
    (fun hp hs => alphaBranchwise_of_alphaPExpansion hp hs)
  exact ⟨G, Fa, U, hG, hclosed, hsat, hinv, hp, hc, minimal_closure_branchwise_path hc,
    hUG, hUG.sound σ P α k hsat, hUG.evaluatedInvariant σ P α k hinv,
    hUG.underlyingStable σ P hstable⟩

end ConcreteContextual

run_elab do
  for name in #[``ConcreteContextual.branchwise_of_pExpansion,
      ``ConcreteContextual.satisfied_alphaBranchwise_preserving,
      ``ConcreteContextual.minimal_closure_mem_branchwise_level,
      ``ConcreteContextual.minimal_closure_mem_fixed_branchwise_rounds,
      ``ConcreteContextual.satisfied_closure_branchwise_path] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end STLTableau.Section3
