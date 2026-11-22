import STLTableaux.Closure.Expansion.BranchwiseUnion
import STLTableaux.Closure.Expansion.BranchwiseRuleShape
import STLTableaux.Closure.Expansion.FiniteClockPalette
import STLTableaux.Closure.Expansion.FiniteClockFormInventory
import STLTableaux.Finiteness.ClockAllocation.SupportedClockPermutations
import STLTableaux.Finiteness.Derivation.NormalizationSupport
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization
import STLTableaux.Finiteness.Inventory.BranchFormulaConfinement
import STLTableaux.Finiteness.Inventory.RootClockConstants
import STLTableaux.Finiteness.Inventory.RootFormulaInventory

/-! Local finiteness of successor orbits. Alpha conversion may split names
that coincide in different scopes, so clock support is bounded by counting
guards, local predicates and reset names separately in both state parts. -/

namespace STLTableau.Section3.ConcreteContextual
open STLTableau.Section4 Finiteness
open STLTableau.Section4.Finiteness
open scoped STL
set_option linter.unnecessarySeqFocus false
variable {Clock Var : Type*} [DecidableEq Clock]

private theorem mixed_raw_branch {p : Predicate Clock Var} {R : TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    ∃ J, RawBranch p J ∧ TransitionForm.normalize? J = some R := by
  rcases h with h | h | h
  · obtain ⟨p₀, E, J, F, rfl, hE, hJ, hn, rfl⟩ := h
    exact ⟨_, .finite hE hJ, by simpa using hn⟩
  · obtain ⟨p₀, E, J, F, rfl, hE, hJ, hn, rfl⟩ := h
    exact ⟨_, .infinite hE hJ, by simpa using hn⟩
  · obtain ⟨c, m, k, a, φ, F, rfl, hn, rfl⟩ := h
    exact ⟨_, .opening c m k a φ, by simpa using hn⟩

set_option maxHeartbeats 2400000 in
-- The support proof evaluates every finite and unbounded raw rule branch.
set_option linter.unusedSimpArgs false in
private theorem raw_three_names {p : Predicate Clock Var} {J : MixedJ Clock Var}
    (h : RawBranch p J) :
    ∃ s : Finset Clock, s.card ≤ 3 ∧ syntaxClocks J ⊆ (s : Set Clock) := by
  classical
  cases h with
  | finite hr hb =>
    cases hr
    case' plainAnd _ _ => refine ⟨∅, by simp, ?_⟩
    case' plainOr _ _ => refine ⟨∅, by simp, ?_⟩
    case' plainUntil _ _ => refine ⟨∅, by simp, ?_⟩
    case' plainRelease _ _ => refine ⟨∅, by simp, ?_⟩
    case' openEventually c _ _ => refine ⟨{c}, by simp, ?_⟩
    case' openAlways c _ _ => refine ⟨{c}, by simp, ?_⟩
    case' upperAlways c d _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' upperEventually c d _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' boundedAlways c d _ _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' boundedEventually c d _ _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    all_goals
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append]
        at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [syntaxClocks, resetNames, Judgement.ofFinite, Predicate.ofFinite,
      ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,
      ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,
      ExpansionRule.boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock, ClockResetSet.clocks_union,Set.subset_def]
  | infinite hr hb =>
    cases hr
    case' upperAlways c d _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' upperEventually c d _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' boundedAlways c d _ _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    case' boundedEventually c d _ _ _ _ _ =>
      refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
    all_goals
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [syntaxClocks,resetNames,Judgement.ofUnbounded,Predicate.ofUnbounded,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,
      UnboundedClocked.alwaysLast,
      UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,ClockResetSet.clocks_union,Set.subset_def]
  | opening c m k a φ =>
    refine ⟨{c}, by simp, ?_⟩
    simp [syntaxClocks, Judgement.ofUnbounded, UnboundedClocked.opening,
      Predicate.ofUnbounded]

section

omit [DecidableEq Clock]

private noncomputable def stateWidth (N : StateForm Clock Var) : ℕ :=
  N.guardClocks.ncard + N.localClocks.ncard + N.resets.clocks.ncard

private noncomputable def width (F : TransitionForm Clock Var) : ℕ :=
  stateWidth F.current + match F.nextPart with
    | none => 0
    | some N => stateWidth N

private theorem stateWidth_rename (N : StateForm Clock Var) (e : Equiv.Perm Clock) :
    stateWidth (N.rename e) = stateWidth N := by
  unfold stateWidth
  rw [guardClocks_rename, StateForm.localClocks_rename]
  change (e '' N.guardClocks).ncard + (e '' N.localClocks).ncard +
    (N.resets.rename e).clocks.ncard = _
  rw [ClockResetSet.clocks_rename]
  simp only [Set.ncard_image_of_injective _ e.injective]

private theorem stateWidth_alphaReset (N : StateForm Clock Var) (e : Equiv.Perm Clock) :
    stateWidth (N.alphaReset e) = stateWidth N := by
  unfold stateWidth
  change N.guardClocks.ncard + (N.rename e).localClocks.ncard +
    (N.resets.rename e).clocks.ncard = _
  rw [StateForm.localClocks_rename, ClockResetSet.clocks_rename]
  simp only [Set.ncard_image_of_injective _ e.injective]

private theorem width_alphaNext (F : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    width (F.alphaNext e) = width F := by
  cases h : F.nextPart <;> simp [width, TransitionForm.alphaNext, h, stateWidth_alphaReset]

private theorem width_alpha {F G : TransitionForm Clock Var} (h : F.AlphaEquivalent G) :
    width F = width G := by
  induction h with
  | refl => rfl
  | outer F e _ =>
    cases h : F.nextPart <;>
      simp [width, TransitionForm.alphaOuter, h, stateWidth_rename, stateWidth_alphaReset]
  | next F e _ => exact width_alphaNext F e
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

private theorem nextAlpha_equivalent {F G : TransitionForm Clock Var} (h : NextAlphaPath F G) :
    F.AlphaEquivalent G := by
  induction h with
  | refl => exact .refl _
  | step F e h _ ih => exact (TransitionForm.AlphaEquivalent.next F e h).symm.trans ih

private theorem stateSupport_le (N : StateForm Clock Var) :
    (stateClockSupport N).ncard ≤ stateWidth N := by
  exact (Set.ncard_union_le _ _).trans
    (Nat.add_le_add_right (Set.ncard_union_le _ _) _)

private theorem allClocks_le_width (F : TransitionForm Clock Var) :
    F.allClocks.ncard ≤ width F := by
  rw [transition_support_eq]
  cases h : F.nextPart with
  | none => simpa [width, h] using stateSupport_le F.current
  | some N =>
    simp only [width, h]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add (stateSupport_le _) (stateSupport_le _))

private theorem stateWidth_le {N : StateForm Clock Var} {U : Finset Clock}
    (h : stateClockSupport N ⊆ (U : Set Clock)) : stateWidth N ≤ 3 * U.card := by
  have hg := Set.ncard_le_ncard
    (fun c hc => h (Or.inl (Or.inl hc)) :
      N.guardClocks ⊆ (U : Set Clock)) U.finite_toSet
  have hl := Set.ncard_le_ncard
    (fun c hc => h (Or.inl (Or.inr hc)) :
      N.localClocks ⊆ (U : Set Clock)) U.finite_toSet
  have hr := Set.ncard_le_ncard
    (fun c hc => h (Or.inr hc) :
      N.resets.clocks ⊆ (U : Set Clock)) U.finite_toSet
  simp only [Set.ncard_coe_finset] at hg hl hr
  unfold stateWidth
  omega

private theorem width_le {F : TransitionForm Clock Var} {U : Finset Clock}
    (h : F.allClocks ⊆ (U : Set Clock)) : width F ≤ 6 * U.card := by
  rw [transition_support_eq] at h
  have hcur := stateWidth_le (fun c hc => h (Or.inl hc) :
    stateClockSupport F.current ⊆ (U : Set Clock))
  cases hn : F.nextPart with
  | none => simp only [width, hn]; omega
  | some N =>
    rw [hn] at h
    have hnxt := stateWidth_le (fun c hc => h (Or.inr hc) :
      stateClockSupport N ⊆ (U : Set Clock))
    simp only [width, hn]
    omega

end

private theorem mixed_width_bound {p : Predicate Clock Var} {R : TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    width R ≤ 18 := by
  obtain ⟨J, hJ, hnorm⟩ := mixed_raw_branch h
  obtain ⟨F, hs, _⟩ := hJ.safe_normalization
  have he : F = R := Option.some.inj (hs.normalizes.symm.trans hnorm)
  subst R
  obtain ⟨U, hcard, hU⟩ := raw_three_names hJ
  have := width_le (hs.allClocks_subset_syntax.trans hU)
  omega

private theorem successor_card {p : Predicate Clock Var} {F G : TransitionForm Clock Var}
    (h : AlphaBranchwisePExpansion p F G) : G.allClocks.ncard ≤ width F + 18 := by
  obtain ⟨A, hA, hstep⟩ := h
  have he := width_alpha (nextAlpha_equivalent hA)
  have hA' := allClocks_le_width A
  rcases hstep.eq_union_or_identity with ⟨_, rfl⟩ | ⟨B, hb, _, rfl⟩
  · omega
  obtain ⟨R, C, hR, ha, rfl⟩ := hb
  rw [NormalizationSupport.allClocks_union, NormalizationSupport.allClocks_underReset]
  have hs : A.current.resets.clocks ⊆ A.allClocks := fun _ h => Or.inr (Or.inl h)
  have heq : A.allClocks ∪ (C.allClocks ∪ A.current.resets.clocks) =
      A.allClocks ∪ C.allClocks := by
    ext c
    constructor
    · rintro (ha | hc | hr)
      · exact Or.inl ha
      · exact Or.inr hc
      · exact Or.inl (hs hr)
    · rintro (ha | hc)
      · exact Or.inl ha
      · exact Or.inr (Or.inl hc)
  rw [heq]
  have hC := allClocks_le_width C
  have hR' := mixed_width_bound hR
  have hc := width_alpha ha
  have := Set.ncard_union_le A.allClocks C.allClocks
  omega

section

omit [DecidableEq Clock]

private theorem state_formulas_finite (N : StateForm Clock Var) :
    N.underlyingFormulas.Finite := by
  let fn : Local Clock Var → Formula Var := fun l =>
    match l with | .predicate p => p.formula | _ => .truth
  apply (N.locals_finite.image fn).subset
  rintro φ ⟨p, hp, rfl⟩
  exact ⟨.predicate p, hp, rfl⟩

private theorem formulas_finite (F : TransitionForm Clock Var) :
    F.underlyingFormulas.Finite := by
  cases hn : F.nextPart with
  | none => simpa [TransitionForm.underlyingFormulas, hn] using state_formulas_finite F.current
  | some N =>
    simpa [TransitionForm.underlyingFormulas, hn] using
      (state_formulas_finite F.current).union (state_formulas_finite N)

private theorem state_constant_cover (N : StateForm Clock Var) :
    ∃ C : Finset NNReal, StateConstantsWithin C N := by
  classical
  refine ⟨N.guards_finite.toFinset.image Guard.bound ∪
    N.resets.finite_domain.toFinset.image (fun c => (N.resets.value c).getD 0), ?_, ?_⟩
  · intro g hg
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g, by simpa using hg, rfl⟩)
  · intro c a ha
    have hc : c ∈ N.resets.clocks := ⟨a, ha⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨c, (Set.Finite.mem_toFinset _).2 hc,
        by rw [ha]; rfl⟩)

private theorem state_constants_mono {C D : Finset NNReal} (h : C ⊆ D)
    {N : StateForm Clock Var} (hN : StateConstantsWithin C N) : StateConstantsWithin D N :=
  ⟨fun g hg => h (hN.1 g hg), fun c a ha => h (hN.2 c a ha)⟩

private theorem constants_cover (F : TransitionForm Clock Var) :
    ∃ C : Finset NNReal, FormConstantsWithin C F := by
  classical
  obtain ⟨C, hC⟩ := state_constant_cover F.current
  cases h : F.nextPart with
  | none => exact ⟨C, hC, by simp [h]⟩
  | some N =>
    obtain ⟨D, hD⟩ := state_constant_cover N
    refine ⟨C ∪ D, state_constants_mono Finset.subset_union_left hC, ?_⟩
    intro M hm
    have he : N = M := Option.some.inj (h.symm.trans hm)
    subst M
    exact state_constants_mono Finset.subset_union_right hD

private theorem state_constants_union {C : Finset NNReal} {N M : StateForm Clock Var}
    (hN : StateConstantsWithin C N) (hM : StateConstantsWithin C M) :
    StateConstantsWithin C (N.union M) :=
  ⟨fun g hg => hg.elim (hN.1 g) (hM.1 g), reset_union C N.resets M.resets hN.2 hM.2⟩

private theorem constants_union {C : Finset NNReal} {F G : TransitionForm Clock Var}
    (hF : FormConstantsWithin C F) (hG : FormConstantsWithin C G) :
    FormConstantsWithin C (F.union G) := by
  refine ⟨state_constants_union hF.1 hG.1, ?_⟩
  intro N hn
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp only [TransitionForm.union, TransitionForm.unionNext, hf, hg] at hn
  · cases hn
  · cases hn
    exact hG.2 _ hg
  · cases hn
    exact hF.2 _ hf
  · cases hn
    exact state_constants_union (hF.2 _ hf) (hG.2 _ hg)

private theorem constants_rename {C : Finset NNReal} {F : TransitionForm Clock Var}
    (hF : FormConstantsWithin C F) (e : Equiv.Perm Clock) :
    FormConstantsWithin C (renameTransition e F) := by
  refine ⟨(state_rename_iff _ _ _).2 hF.1, ?_⟩
  intro N hn
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.mp hn
  exact (state_rename_iff _ _ _).2 (hF.2 _ hM)

private theorem formulas_rename (F : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (renameTransition e F).underlyingFormulas = F.underlyingFormulas := by
  cases h : F.nextPart <;> simp [renameTransition, TransitionForm.underlyingFormulas, h]

private theorem allClocks_rename (F : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (renameTransition e F).allClocks = e '' F.allClocks := by
  have st (N : StateForm Clock Var) :
      stateClockSupport (N.rename e) = e '' stateClockSupport N := by
    unfold stateClockSupport
    rw [guardClocks_rename, StateForm.localClocks_rename]
    change e '' N.guardClocks ∪ e '' N.localClocks ∪ (N.resets.rename e).clocks = _
    simp only [ClockResetSet.clocks_rename, Set.image_union]
  rw [transition_support_eq, transition_support_eq F]
  cases h : F.nextPart <;> simp [renameTransition, h, st, Set.image_union]

end

private theorem successor_profiles (F : TransitionForm Clock Var) :
    ∃ (P : Finset (Formula Var)) (C : Finset NNReal), ∀ {p G},
      p ∈ branchwiseCurrent F → AlphaBranchwisePExpansion p F G →
      G.underlyingFormulas ⊆ (P : Set (Formula Var)) ∧ FormConstantsWithin C G := by
  classical
  obtain ⟨D, hD⟩ := constants_cover F
  let R := (formulas_finite F).toFinset
  let P := R.biUnion rootPlainFormulas
  let C := D ∪ R.biUnion rootClockConstants
  refine ⟨P, C, ?_⟩
  intro p G hp h
  have hpR : p.formula ∈ R := (Set.Finite.mem_toFinset _).2
    (Or.inl ⟨p, hp, rfl⟩)
  have hFP : F.underlyingFormulas ⊆ (P : Set (Formula Var)) := by
    intro φ hφ
    exact Finset.mem_biUnion.mpr
      ⟨φ, (Set.Finite.mem_toFinset _).2 hφ, root_mem_rootPlainFormulas φ⟩
  have hpC : rootClockConstants p.formula ⊆ C :=
    fun a ha => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_,hpR,ha⟩)
  obtain ⟨A, hA, hstep⟩ := h
  have hα := nextAlpha_equivalent hA
  have hAP : A.underlyingFormulas ⊆ (P : Set (Formula Var)) := hα.underlyingFormulas ▸ hFP
  have hAC : FormConstantsWithin C A :=
    (alpha_numeric_constants_iff _ hα).1 (numeric_mono Finset.subset_union_left hD)
  rcases hstep.eq_union_or_identity with ⟨_, rfl⟩ | ⟨B, hb, _, rfl⟩
  · exact ⟨hAP, hAC⟩
  constructor
  · rw [TransitionForm.underlyingFormulas_union]
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact hAP hφ
    · exact Finset.mem_biUnion.mpr
        ⟨_, hpR, subformula_mem_rootPlainFormulas (branch_underlying_subformula hb hφ)⟩
  · apply constants_union hAC
    obtain ⟨J, K, hJ, hK, rfl⟩ := hb
    apply underReset_numeric_constants _ _ _ _ hAC.1.2
    exact numeric_mono hpC
      ((alpha_numeric_constants_iff _ hK).2 (mixed_branch_numeric_constants hJ))

/-- One fixed finite inventory covers all successors up to renaming fixing the
specified prefix clocks. The finite support of the source can be included in
that prefix without imposing any freshness restriction on the successors. -/
theorem finite_alphaBranchwise_successor_cover
    (F : TransitionForm Clock Var) (S : Finset Clock) :
    ∃ T : Set (TransitionForm Clock Var), T.Finite ∧ ∀ {p G},
      p ∈ branchwiseCurrent F → AlphaBranchwisePExpansion p F G →
      ∃ e : Equiv.Perm Clock, (∀ c ∈ S, e c = c) ∧ renameTransition e G ∈ T := by
  classical
  obtain ⟨Q, hp⟩ := FiniteClockPalette.exists_palette S (width F + 18)
  obtain ⟨P, C, hprofile⟩ := successor_profiles F
  obtain ⟨T, hT, hmem⟩ := FiniteClockFormInventory.finite_cover Q P C
  refine ⟨T, hT, ?_⟩
  intro p G hP hG
  let U := G.allClocks_finite.toFinset
  have hU : U.card ≤ width F + 18 := by
    rw [← Set.ncard_eq_toFinset_card _ G.allClocks_finite]
    exact successor_card hG
  obtain ⟨e, hfix, he⟩ := hp U hU
  refine ⟨e, hfix, hmem _ ?_ ?_ (constants_rename (hprofile hP hG).2 e)⟩
  · rw [allClocks_rename]
    rintro c ⟨d, hd, rfl⟩
    exact he d ((Set.Finite.mem_toFinset _).2 hd)
  · rw [formulas_rename]
    exact (hprofile hP hG).1

end STLTableau.Section3.ConcreteContextual
