import STLTableaux.Closure.Expansion.BranchwiseUnion
import STLTableaux.Closure.Expansion.BranchwiseRuleShape

/-! Single-predicate expansion levels and the rank on current predicates
with their clock names fixed. The orbit rank of Definition 4.18 is
related to this rank in `BranchwiseRankOrbit.lean`. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

private theorem NextAlphaPath.bodyFree_eq {F G : TransitionForm Clock Var}
    (h : NextAlphaPath F G) : G.bodyFreeClocks = F.bodyFreeClocks := by
  induction h with
  | refl => rfl
  | step F e hf _ ih =>
    rw [ih]
    cases hn : F.nextPart with
    | none => simp [TransitionForm.bodyFreeClocks, TransitionForm.alphaNext, hn]
    | some N =>
      simp [TransitionForm.bodyFreeClocks, TransitionForm.alphaNext, hn,
        N.alphaReset_freeClocks e (hf N hn)]

namespace ConcreteContextual
open BranchwiseExpansion
variable [DecidableEq Clock]

private abbrev Label (F : TransitionForm Clock Var) :=
  labels AlphaBranchwisePExpansion branchwiseCurrent F

private def unboundBody (F : TransitionForm Clock Var) : Set Clock :=
  F.bodyFreeClocks \ F.current.resets.clocks

private theorem alphaBranchwise_unboundBody_eq {p : Predicate Clock Var}
    {F G : TransitionForm Clock Var} (hp : p ∈ branchwiseCurrent F)
    (hs : AlphaBranchwisePExpansion p F G) :
    unboundBody G = unboundBody F := by
  obtain ⟨A, ha, hs⟩ := hs
  have hA : unboundBody A = unboundBody F := by
    simp only [unboundBody, ha.bodyFree_eq, ha.current]
  rw [← hA]
  have hpa : Local.predicate p ∈ A.current.locals := by
    rw [ha.current]
    exact hp
  exact Set.Subset.antisymm (branchwise_free_under_current_subset hpa hs)
    hs.extension.unboundBody_mono

private theorem branchwise_current_reset {p : Predicate Clock Var}
    {F G : TransitionForm Clock Var} (hs : catalogue.BranchwisePExpansion p F G)
    {c : Clock} {a : NNReal} (hc : G.current.resets.value c = some a) :
    F.current.resets.value c = some a ∨ a = 0 := by
  rcases hs.eq_union_or_identity with ⟨_, rfl⟩ | ⟨B, hB, _, rfl⟩
  · exact Or.inl hc
  obtain ⟨R, A, hR, ha, rfl⟩ := hB
  change (F.current.resets.union (A.current.resets.union F.current.resets)).value c =
    some a at hc
  cases hf : F.current.resets.value c with
  | none =>
    cases hA : A.current.resets.value c with
    | none => simp only [ClockResetSet.union, hf, hA, reduceCtorEq] at hc
    | some b =>
      have hab : b = a := by simpa only [ClockResetSet.union, hf, hA, Option.some.injEq] using hc
      exact Or.inr (hab.symm.trans (alpha_current_reset_zero hR ha hA))
  | some b => exact Or.inl (by simpa only [ClockResetSet.union, hf] using hc)

private theorem alpha_level_clock_data {F G : TransitionForm Clock Var} {i : ℕ}
    (hm : G ∈ alphaBranchwiseExpansionLevel F i) :
    unboundBody G = unboundBody F ∧
      ResetIncluded F.current.resets G.current.resets ∧
      ∀ c a, G.current.resets.value c = some a →
        F.current.resets.value c = some a ∨ a = 0 := by
  induction i generalizing G with
  | zero =>
    have he : G = F := hm
    subst G
    exact ⟨rfl, fun _ _ h => h, fun _ _ h => Or.inl h⟩
  | succ i ih =>
    obtain ⟨H, hH, p, hp, hs⟩ := mem_level_succ.mp hm
    obtain ⟨hfree, hinc, hres⟩ := ih hH
    have hfree' := alphaBranchwise_unboundBody_eq hp hs
    obtain ⟨A, ha, hs⟩ := hs
    refine ⟨hfree'.trans hfree, ?_, ?_⟩
    · intro c a hc
      apply hs.extension.current.resets c a
      rw [ha.current]
      exact hinc c a hc
    · intro c a hc
      rcases branchwise_current_reset hs hc with hA | hzero
      · rw [ha.current] at hA
        exact hres c a hA
      · exact Or.inr hzero

private theorem opening_compatible (F : TransitionForm Clock Var)
    (c : Clock) (m : Marker) (k : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hc : c ∉ unboundBody F)
    (hz : ∀ a, F.current.resets.value c = some a → a = 0) :
    F.UnionCompatible ((openingForm c m k I φ).underReset F.current.resets) := by
  let B := (openingForm c m k I φ).underReset F.current.resets
  have hr : B.current.resets =
      (ClockResetSet.singleton c 0).union F.current.resets := by
    change (openingForm c m k I φ).current.resets.union _ = _
    rw [openingForm_resets]
  have hn : B.nextPart = none := openingForm_next c m k I φ
  apply TransitionForm.unionCompatible_of_captureFree F B
  · intro d a b hda hdb
    rw [hr] at hdb
    by_cases hdc : d = c
    · subst d
      have hb : b = 0 := by
        simpa only [ClockResetSet.union, ClockResetSet.singleton, ↓reduceIte,
          Option.some.injEq] using hdb.symm
      exact (hz a hda).trans hb.symm
    · have hb : F.current.resets.value d = some b := by
        simpa only [ClockResetSet.union, ClockResetSet.singleton, hdc, ↓reduceIte] using hdb
      exact Option.some.inj (hda.symm.trans hb)
  · rw [hr, ClockResetSet.clocks_union, ClockResetSet.clocks_singleton]
    apply Set.disjoint_left.2
    rintro d (hd | hd) hdF
    · have he : d = c := hd
      exact hc (he ▸ hdF)
    · exact hdF.2 hd
  · rw [hr, ClockResetSet.clocks_union]
    exact Set.disjoint_left.2 (fun _ h hfree => hfree.2 (Or.inr h))
  all_goals intro N M hN hM; rw [hn] at hM; cases hM

/-- The only possible name obstruction to a literal opening is a
conflicting current assignment or a free occurrence it would capture. -/
private theorem opening_available_from_data
    {F H S : TransitionForm Clock Var}
    (hfH : unboundBody H = unboundBody F)
    (hincH : ResetIncluded F.current.resets H.current.resets)
    (hfS : unboundBody S = unboundBody F)
    (hresS : ∀ c a, S.current.resets.value c = some a →
      F.current.resets.value c = some a ∨ a = 0)
    {c : Clock} {m : Marker} {k : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {G : TransitionForm Clock Var}
    (hHG : SyntacticallySubsumed H G)
    (hBG : SyntacticallySubsumed ((openingForm c m k I φ).underReset H.current.resets) G) :
    S.UnionCompatible ((openingForm c m k I φ).underReset S.current.resets) := by
  have hcB : ((openingForm c m k I φ).underReset H.current.resets).current.resets.value c =
      some 0 := by
    change ((openingForm c m k I φ).current.resets.union H.current.resets).value c = _
    rw [openingForm_resets]
    simp [ClockResetSet.union, ClockResetSet.singleton]
  have hcG := hBG.current.resets c 0 hcB
  have hcH : c ∉ unboundBody H :=
    fun hc => Set.disjoint_left.1 hHG.outerFresh ⟨0, hcG⟩ hc
  have hcS : c ∉ unboundBody S := by rwa [hfS, ← hfH]
  refine opening_compatible S c m k I φ hcS ?_
  intro a hSa
  rcases hresS c a hSa with hFa | hz
  · exact Option.some.inj ((hHG.current.resets c a (hincH c a hFa)).symm.trans hcG)
  · exact hz

omit [DecidableEq Clock] in
private theorem plain_mem_alpha_iff {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (φ : Formula Var) :
    Local.predicate (.plain φ) ∈ F.current.locals ↔
      Local.predicate (.plain φ) ∈ G.current.locals := by
  classical
  let Q := fun q : Predicate Clock Var => q ≠ .plain φ
  have hQ (S : TransitionForm Clock Var) :
      (∀ q, Local.predicate q ∈ S.current.locals → Q q) ↔
        Local.predicate (.plain φ) ∉ S.current.locals := by
    constructor
    · intro ha hp
      exact ha _ hp rfl
    · intro ha q hq he
      exact ha (he ▸ hq)
  have he := h.current_property Q (by intro e q; cases q <;> simp [Q, Predicate.rename])
  exact not_iff_not.mp ((hQ F).symm.trans (he.trans (hQ G)))

/-- A branch that adds an unclocked current predicate can be replayed with
the same selected predicate, after freshening only binders. -/
private theorem replay_plain [Infinite Clock] {p : Predicate Clock Var}
    {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p Λ B) {φ : Formula Var}
    (hq : Local.predicate (.plain φ) ∈ B.current.locals) (F : TransitionForm Clock Var) :
    ∃ G, AlphaBranchwisePExpansion p F G ∧
      Local.predicate (.plain φ) ∈ G.current.locals := by
  obtain ⟨R, A, hr, ha, rfl⟩ := hb
  obtain ⟨e, C, hf, hC, hcon⟩ := F.contextual_compatible_branch R
  have hqR := (plain_mem_alpha_iff ha φ).1 hq
  have hqC := (plain_mem_alpha_iff hC φ).2 hqR
  have hbranch : catalogue.Branch p (F.alphaNext e).current.resets
      (C.underReset F.current.resets) := ⟨R, C, hr, hC, rfl⟩
  exact ⟨_, ⟨_, .step F e hf (.refl _), .of_compatible_union hbranch hcon⟩,
    hcon.right.current.locals hqC⟩

/-- The same literal current output is possible at every earlier level
that contains its producer. Clocked outputs are only temporal openings. -/
private theorem replay_child [Infinite Clock] {F H G : TransitionForm Clock Var}
    {n i : ℕ} {p q : Predicate Clock Var}
    (hH : H ∈ alphaBranchwiseExpansionLevel F n)
    (hs : AlphaBranchwisePExpansion p H G)
    (hp : p ∈ Label F i)
    (hq : q ∈ branchwiseCurrent G) (hnew : q ∉ branchwiseCurrent H) :
    q ∈ Label F (i+1) := by
  obtain ⟨S, hS, hpS⟩ := mem_labels.mp hp
  obtain ⟨A, ha, hs⟩ := hs
  have hnew' : Local.predicate q ∉ A.current.locals := by
    rw [ha.current]
    exact hnew
  obtain ⟨B, hb, hBG, hqB⟩ := hs.new_current_witness hq hnew'
  cases q with
  | plain φ =>
    obtain ⟨T, hT, ht⟩ := replay_plain hb hqB S
    exact ⟨T, ⟨S, hS, p, hpS, hT⟩, ht⟩
  | bounded c d m m' k I φ =>
    exact (branch_no_bounded_child hb c d m m' k I φ hqB).elim
  | upper c m k I φ =>
    obtain ⟨rfl, rfl⟩ := branch_upper_child hb hqB
    obtain ⟨hfH, hincH, _⟩ := alpha_level_clock_data hH
    obtain ⟨hfS, _, hresS⟩ := alpha_level_clock_data hS
    have hfreeA : unboundBody A = unboundBody F := by
      simpa only [unboundBody, ha.bodyFree_eq, ha.current] using hfH
    have hincA : ResetIncluded F.current.resets A.current.resets := by
      rwa [ha.current]
    have hcon := opening_available_from_data hfreeA hincA hfS hresS hs.extension hBG
    have hstep := ClosureCatalogue.BranchwisePExpansion.of_compatible_union
      (E := catalogue) (opening_branch c m k I φ S.current.resets) hcon
    refine ⟨_, ⟨S, hS, _, hpS, ⟨S, .refl _, hstep⟩⟩, ?_⟩
    exact hcon.right.current.locals ((openingForm_current_mem c m k I φ _).2 rfl)

theorem alpha_branchwise_freshProvenance [Infinite Clock] (F : TransitionForm Clock Var) :
    FreshProvenance AlphaBranchwisePExpansion branchwiseCurrent Predicate.complexity F := by
  intro i q hq
  obtain ⟨hnext, hold⟩ := mem_fresh_succ.mp hq
  obtain ⟨G, hG, hqG⟩ := mem_labels.mp hnext
  obtain ⟨H, hH, p, hp, hs⟩ := mem_level_succ.mp hG
  have hqH : q ∉ branchwiseCurrent H := fun h => hold ⟨H, hH, h⟩
  have hpL : p ∈ Label F i := ⟨H, hH, hp⟩
  have hlt : q.complexity < p.complexity := by
    obtain ⟨A, ha, hs⟩ := hs
    apply hs.new_current_complexity hqG
    rw [ha.current]
    exact hqH
  refine ⟨p, ?_, hlt⟩
  cases i with
  | zero => exact hpL
  | succ i => exact ⟨hpL, fun hpOld => hold (replay_child hH hs hpOld hqG hqH)⟩

omit [DecidableEq Clock] in
private theorem initial_bounded (F : TransitionForm Clock Var) :
    ∃ N, ∀ p ∈ branchwiseCurrent F, Predicate.complexity p ≤ N := by
  have hf : (branchwiseCurrent F).Finite := by
    have hi : Function.Injective (Local.predicate : Predicate Clock Var → Local Clock Var) :=
      fun _ _ h => Local.predicate.inj h
    exact F.current.locals_finite.preimage hi.injOn
  exact (hf.image Predicate.complexity).bddAbove.imp (fun _ h _ hp => h ⟨_, hp, rfl⟩)

/-- Lemma 4.19 (expansion rank decrease). -/
theorem alpha_branchwise_rank_decrease [Infinite Clock] (F : TransitionForm Clock Var)
    (i : ℕ) (hi : 0 < alphaBranchwiseLevelRank F i) :
    alphaBranchwiseLevelRank F (i+1) < alphaBranchwiseLevelRank F i := by
  obtain ⟨N, hN⟩ := initial_bounded F
  exact rank_succ_lt_of_pos (alpha_branchwise_freshProvenance F) hN hi

/-- Lemma 4.20: eventually there are no new
positive-complexity predicates; this does not assert rule-closure. -/
theorem alpha_branchwise_rank_eventually_zero [Infinite Clock] (F : TransitionForm Clock Var) :
    ∃ k : ℕ, ∀ i ≥ k, alphaBranchwiseLevelRank F i = 0 := by
  obtain ⟨N, hN⟩ := initial_bounded F
  exact rank_eventually_zero (alpha_branchwise_freshProvenance F) hN

run_elab do
  for name in #[``alpha_branchwise_freshProvenance, ``alpha_branchwise_rank_decrease,
      ``alpha_branchwise_rank_eventually_zero] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name}: unexpected axiom {ax}"

end ConcreteContextual
end STLTableau.Section3
