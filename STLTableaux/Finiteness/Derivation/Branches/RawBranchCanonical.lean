import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization
import STLTableaux.Finiteness.Derivation.CanonicalResetMap

/-! Actual raw branches have explicit canonical current-local/next spines.
No ownership/progress/existence field is assumed. Duplicate locals are kept. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

private def CanonicalResult (support : Set Clock) (B : MixedJ Clock Var) : Prop :=
  ∃ (R : ClockResetSet Clock) (locals : List (Local Clock Var))
      (nextInputs : List (MixedJ Clock Var)) (C : MixedJ Clock Var),
    canonicalSyntax R [] locals nextInputs = some C ∧ StructuralEq B C ∧
      pendingWeight C ≤ pendingWeight B ∧ nextInputs.length ≤ 1 ∧
      (∀ K ∈ nextInputs, noNext K) ∧
      (R = ClockResetSet.empty ∨ ∃ c, R = ClockResetSet.singleton c 0) ∧
      (C = B ∨ C = .reset ClockResetSet.empty B) ∧
      Disjoint R.clocks support ∧ R.clocks ⊆ resetNames B

omit [DecidableEq Clock] in
private theorem add_empty_reset (J : MixedJ Clock Var) :
    StructuralEq J (.reset ClockResetSet.empty J) := by
  apply ACIdem.symm
  apply ACIdem.resetUnused
  rw [empty_reset_clocks]
  exact Set.empty_disjoint _

private theorem local_shape {support : Set Clock} (l : Local Clock Var) : CanonicalResult support l.toJudgement := by
  exact ⟨ClockResetSet.empty,[l],[],.reset ClockResetSet.empty l.toJudgement,
    rfl,add_empty_reset _,le_rfl,by simp,by simp,Or.inl rfl,Or.inr rfl,by simp [empty_reset_clocks],by simp [empty_reset_clocks]⟩

private theorem locals_shape {support : Set Clock} (l k : Local Clock Var) :
    CanonicalResult support (.conj l.toJudgement k.toJudgement) := by
  exact ⟨ClockResetSet.empty,[l,k],[],.reset ClockResetSet.empty (.conj l.toJudgement k.toJudgement),
    rfl,add_empty_reset _,le_rfl,by simp,by simp,Or.inl rfl,Or.inr rfl,by simp [empty_reset_clocks],by simp [empty_reset_clocks]⟩

private theorem local_next_shape {support : Set Clock} (l : Local Clock Var) (K : MixedJ Clock Var) (hK : noNext K) :
    CanonicalResult support (.conj l.toJudgement (.next K)) := by
  refine ⟨ClockResetSet.empty,[l],[K],.reset ClockResetSet.empty (.conj l.toJudgement (.next K)),
    rfl,add_empty_reset _,le_rfl,by simp,?_,Or.inl rfl,Or.inr rfl,by simp [empty_reset_clocks],by simp [empty_reset_clocks]⟩
  simpa using hK

private theorem next_shape {support : Set Clock} (K : MixedJ Clock Var) (hK : noNext K) :
    CanonicalResult support (.next K) := by
  refine ⟨ClockResetSet.empty,[],[K],.reset ClockResetSet.empty (.next K),
    rfl,add_empty_reset _,le_rfl,by simp,?_,Or.inl rfl,Or.inr rfl,by simp [empty_reset_clocks],by simp [empty_reset_clocks]⟩
  simpa using hK

private theorem opening_shape (c : Clock) (p : Predicate Clock Var) (m : Marker) :
    CanonicalResult ∅ (.reset (ClockResetSet.singleton c 0)
      (.conj (.predicate p) (.marker m))) := by
  exact ⟨ClockResetSet.singleton c 0,[.predicate p,.marker m],[],_,rfl,.refl _,
    le_rfl,by simp,by simp,Or.inr ⟨c,rfl⟩,Or.inl rfl,Set.disjoint_empty _,Set.subset_union_left⟩

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
/-- Concrete branches contain at most one literal next payload, without nested
next. Their only current reset is a zero opening reset or the empty reset. -/
private theorem canonical_shape {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) : CanonicalResult (syntaxClocks (.predicate p)) B := by
  cases h with
  | finite hr hb =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
        ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
        ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
        ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,
        ExpansionRule.boundedEventually_finish])
    all_goals simp only [STLTableau.Judgement.markedLT_eq_clock,
      STLTableau.Judgement.markedGT_eq_clock,Section3.Judgement.ofFinite]
    all_goals first
      | exact local_shape (.predicate _)
      | exact locals_shape (.predicate _) (.predicate _)
      | apply local_next_shape (.predicate _)
      | apply next_shape
      | exact opening_shape _ _ _
    all_goals simp [noNext]
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
        UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
        UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
        UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
        UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
        UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt])
    all_goals simp only [Section3.Judgement.ofUnbounded]
    all_goals first
      | exact local_shape (.predicate _)
      | exact locals_shape (.predicate _) (.predicate _)
      | apply local_next_shape (.predicate _)
      | apply next_shape
    all_goals simp [noNext]
  | opening c m kind a φ =>
    simpa only [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,syntaxClocks] using
      opening_shape c (Predicate.ofUnbounded (.upper c m kind a φ)) m

omit [DecidableEq Clock] in
private theorem fold_empty_current_reset (Xs : List (MixedJ Clock Var))
    (h : ∀X∈Xs,currentResetMap X=ClockResetSet.empty)
    {J : MixedJ Clock Var} (hf : foldCurrent Xs=some J) : currentResetMap J=ClockResetSet.empty := by
  induction Xs generalizing J with
  | nil => cases hf
  | cons X Xs ih =>
    rw [foldCurrent_cons] at hf
    have he := Option.some.inj hf
    subst J
    cases ht : foldCurrent Xs with
    | none => exact h X List.mem_cons_self
    | some T =>
      change (currentResetMap X).union (currentResetMap T)=ClockResetSet.empty
      rw [h X List.mem_cons_self,ih (fun K hK => h K (List.mem_cons_of_mem X hK)) ht]
      rfl

omit [DecidableEq Clock] in
/-- Current locals and literal next payloads carry no current reset map. -/
theorem fold_locals_next_reset_map_empty (L : List (Local Clock Var)) (Ns : List (MixedJ Clock Var))
    {J : MixedJ Clock Var} (hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)=some J) :
    currentResetMap J=ClockResetSet.empty := by
  apply fold_empty_current_reset _ _ hf
  intro X hX
  rcases List.mem_append.mp hX with hl | hn
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hl
    cases l <;> rfl
  · obtain ⟨N,hn,rfl⟩ := List.mem_map.mp hn
    rfl

omit [DecidableEq Clock] in
/-- A nonempty canonical spine with no outside guards records precisely its
common reset, including actual assigned constants. -/
theorem canonical_reset_map_without_guards
    {R : ClockResetSet Clock} {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)}
    {C : MixedJ Clock Var} (hs : canonicalSyntax R [] L Ns=some C) : currentResetMap C=R := by
  cases hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none => simp [canonicalSyntax,hf,foldCurrent,optionalConj] at hs
  | some Body =>
    have he : .reset R Body=C := by
      simpa only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hf,Option.map_some,Option.some.injEq] using hs
    rw [←he]
    change (currentResetMap Body).union R=R
    rw [fold_locals_next_reset_map_empty L Ns hf]
    rfl

omit [DecidableEq Clock] in
private theorem reset_value_ext {R S : ClockResetSet Clock} (h:R.value=S.value) : R=S := by
  cases R
  cases S
  cases h
  rfl

omit [DecidableEq Clock] in
private theorem map_union_empty_right (R : ClockResetSet Clock) : R.union ClockResetSet.empty=R := by
  apply reset_value_ext
  funext c
  change (match R.value c with | some v=>some v | none=>none)=R.value c
  cases R.value c <;> rfl

/-- Construct the canonical data AND a safe normalizer for that actual syntax.
No generic safety transfer across StructuralEq is assumed. -/
theorem RawBranch.canonical {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) :
    ∃ (R : ClockResetSet Clock) (locals : List (Local Clock Var))
      (nextInputs : List (MixedJ Clock Var)) (C : MixedJ Clock Var),
      canonicalSyntax R [] locals nextInputs = some C ∧ StructuralEq B C ∧
      pendingWeight C ≤ pendingWeight B ∧ nextInputs.length ≤ 1 ∧
      (∀ K ∈ nextInputs, noNext K) ∧
      (R = ClockResetSet.empty ∨ ∃ c, R = ClockResetSet.singleton c 0) ∧
      ∃ F, SafeNormalization C F := by
  obtain ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hform,_hdisjoint,_hsubset⟩ := canonical_shape h
  obtain ⟨F,hsafe,_⟩ := h.safe_normalization
  have hc : ∃ G, SafeNormalization C G := by
    rcases hform with rfl | rfl
    · exact ⟨F,hsafe⟩
    · refine ⟨_,.reset ClockResetSet.empty hsafe ?_⟩
      rw [empty_reset_clocks]
      exact Set.empty_disjoint _
  exact ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hc⟩

/-- The actual canonical current reset avoids the source predicate and comes
from resets actually present in the chosen raw branch. This extra provenance
cannot be inferred from arbitrary structural equivalence alone. -/
theorem RawBranch.canonical_with_reset_support {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) :
    ∃ (R : ClockResetSet Clock) (locals : List (Local Clock Var))
      (nextInputs : List (MixedJ Clock Var)) (C : MixedJ Clock Var),
      canonicalSyntax R [] locals nextInputs = some C ∧ StructuralEq B C ∧
      pendingWeight C ≤ pendingWeight B ∧ nextInputs.length ≤ 1 ∧
      (∀ K ∈ nextInputs, noNext K) ∧
      (R = ClockResetSet.empty ∨ ∃ c, R = ClockResetSet.singleton c 0) ∧
      (∃ F, SafeNormalization C F) ∧
      Disjoint R.clocks (syntaxClocks (.predicate p)) ∧ R.clocks ⊆ resetNames B := by
  obtain ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hform,hdisjoint,hsubset⟩ := canonical_shape h
  obtain ⟨F,hsafe,_⟩ := h.safe_normalization
  have hc : ∃ G, SafeNormalization C G := by
    rcases hform with rfl | rfl
    · exact ⟨F,hsafe⟩
    · refine ⟨_,.reset ClockResetSet.empty hsafe ?_⟩
      rw [empty_reset_clocks]
      exact Set.empty_disjoint _
  exact ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hc,hdisjoint,hsubset⟩

/-- The actual canonical current reset avoids the source predicate and comes
from resets actually present in the chosen raw branch. This extra provenance
cannot be inferred from arbitrary structural equivalence alone. -/
theorem RawBranch.canonical_with_exact_reset_map {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) :
    ∃ (R : ClockResetSet Clock) (locals : List (Local Clock Var))
      (nextInputs : List (MixedJ Clock Var)) (C : MixedJ Clock Var),
      canonicalSyntax R [] locals nextInputs = some C ∧ StructuralEq B C ∧
      pendingWeight C ≤ pendingWeight B ∧ nextInputs.length ≤ 1 ∧
      (∀ K ∈ nextInputs, noNext K) ∧
      (R = ClockResetSet.empty ∨ ∃ c, R = ClockResetSet.singleton c 0) ∧
      (∃ F, SafeNormalization C F) ∧
      Disjoint R.clocks (syntaxClocks (.predicate p)) ∧ R.clocks ⊆ resetNames B ∧
      R=currentResetMap B := by
  obtain ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hform,hdisjoint,hsubset⟩ := canonical_shape h
  obtain ⟨F,hsafe,_⟩ := h.safe_normalization
  have hMap : R=currentResetMap B := by
    have hm := canonical_reset_map_without_guards hshape
    rcases hform with he | he
    · rw [he] at hm
      exact hm.symm
    · rw [he] at hm
      change (currentResetMap B).union ClockResetSet.empty=R at hm
      rw [map_union_empty_right] at hm
      exact hm.symm
  have hc : ∃ G, SafeNormalization C G := by
    rcases hform with rfl | rfl
    · exact ⟨F,hsafe⟩
    · refine ⟨_,.reset ClockResetSet.empty hsafe ?_⟩
      rw [empty_reset_clocks]
      exact Set.empty_disjoint _
  exact ⟨R,L,N,C,hshape,hregroup,hweight,hlen,hflat,hreset,hc,hdisjoint,hsubset,hMap⟩

end STLTableau.Section4.Finiteness
