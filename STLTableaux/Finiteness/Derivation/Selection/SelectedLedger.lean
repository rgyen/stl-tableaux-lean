import STLTableaux.Finiteness.Derivation.Selection.SelectedRealization
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalizedOrigin
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization

/-! Exact branch and consumption ledgers of the same selected proof tree.
No semantic or counting premise is added to the selected construction. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Current predicates inside literal next payloads; outer resets do not add
predicates. This observation retains actual raw syntax until occurrence recovery. -/
def nextCurrentPredicates : MixedJ Clock Var → Set (Predicate Clock Var)
  | .next K => K.currentPredicates
  | .conj J K => nextCurrentPredicates J ∪ nextCurrentPredicates K
  | .reset _ J => nextCurrentPredicates J
  | _ => ∅

structure RawLedgerEntry [DecidableEq Clock] where
  source : Predicate Clock Var
  body : MixedJ Clock Var
  actual : RawBranch source body

variable [DecidableEq Clock]

noncomputable def SelectedTree.rawLedger
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (RawLedgerEntry (Clock := Clock) (Var := Var)) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail => ⟨choice.p,choice.B,choice.branch⟩ :: tail.rawLedger
  | .required _ _ tail => tail.rawLedger
  | .optional _ _ upper _ tail => ⟨upper.p,upper.B,upper.branch⟩ :: tail.rawLedger

/-- Plain demands actually selected or consumed by required fusion. -/
noncomputable def SelectedTree.plainConsumed
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (Formula Var) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ choice tail => match choice.p with
    | .plain φ => φ :: tail.plainConsumed
    | _ => tail.plainConsumed
  | .required _ choice tail => timedFormula choice.kind choice.I choice.phi :: tail.plainConsumed
  | .optional _ _ _ _ tail => tail.plainConsumed

/-- Actual boundary-consumed `↑↓` source and required/optional tag. -/
noncomputable def SelectedTree.boundaryConsumed
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (Predicate Clock Var × Bool) :=
  match T with
  | .zero _ _ => []
  | .ordinary _ _ tail => tail.boundaryConsumed
  | .required _ choice tail =>
    (.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,true) :: tail.boundaryConsumed
  | .optional _ choice _ _ tail =>
    (.bounded choice.c choice.d choice.m (Marker.complement choice.ell) choice.kind choice.I choice.phi,false) :: tail.boundaryConsumed

omit [DecidableEq Clock] in
private theorem structural_next {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    nextCurrentPredicates J = nextCurrentPredicates K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib | resetUnused | resetNested => rfl

omit [DecidableEq Clock] in
private theorem fold_next {Xs : List (MixedJ Clock Var)} {J : MixedJ Clock Var}
    (hf : foldCurrent Xs = some J) (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates J ↔ ∃ K ∈ Xs, p ∈ nextCurrentPredicates K := by
  induction Xs generalizing J with
  | nil => cases hf
  | cons K Ks ih =>
    rw [foldCurrent_cons] at hf
    have he := Option.some.inj hf
    subst J
    cases ht : foldCurrent Ks with
    | none =>
      have he := (foldCurrent_none_iff _).1 ht
      subst Ks
      simp only [prependCurrent,List.mem_cons,List.not_mem_nil,or_false,exists_eq_left]
    | some T =>
      change (p ∈ nextCurrentPredicates K ∨ p ∈ nextCurrentPredicates T) ↔ _
      rw [ih ht]
      simp only [List.mem_cons]
      aesop

omit [DecidableEq Clock] in
private theorem guard_next_empty (G : List (Guard Clock)) {A : MixedJ Clock Var}
    (hf : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) = some A) :
    nextCurrentPredicates A = ∅ := by
  ext p
  rw [fold_next hf]
  simp only [Set.mem_empty_iff_false,iff_false,not_exists,not_and]
  intro K hK
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hK
  cases g
  exact id

omit [DecidableEq Clock] in
private theorem local_next_empty (l : Local Clock Var) :
    nextCurrentPredicates l.toJudgement = ∅ := by cases l <;> rfl

omit [DecidableEq Clock] in
private theorem locals_fold_next (L : List (Local Clock Var)) (Ns : List (MixedJ Clock Var))
    {Body : MixedJ Clock Var} (hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) = some Body)
    (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates Body ↔ ∃ K ∈ Ns, p ∈ K.currentPredicates := by
  rw [fold_next hf]
  simp only [List.mem_append,or_and_right,exists_or]
  constructor
  · rintro (⟨K,hK,hp⟩ | ⟨K,hK,hp⟩)
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hK
      rw [local_next_empty l] at hp
      cases hp
    · obtain ⟨M,hM,he⟩ := List.mem_map.mp hK
      subst K
      exact ⟨M,hM,hp⟩
  · rintro ⟨K,hK,hp⟩
    exact Or.inr ⟨.next K,List.mem_map.mpr ⟨K,hK,rfl⟩,hp⟩

omit [DecidableEq Clock] in
private theorem owned_next {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates J ↔ ∃ K ∈ owned.nextInputs, p ∈ K.currentPredicates := by
  rw [structural_next owned.regroup]
  cases hg : foldCurrent (owned.guards.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    cases hb : foldCurrent (owned.locals.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none =>
      have hs := owned.shape
      simp only [canonicalSyntax,hg,hb,Option.map_none,optionalConj] at hs
      cases hs
    | some Body =>
      have he : .reset R Body = owned.canonical := by
        simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
      rw [← he]
      exact locals_fold_next _ _ hb p
  | some A =>
    cases hb : foldCurrent (owned.locals.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
    | none =>
      have he : A = owned.canonical := by
        simpa only [canonicalSyntax,hg,hb,Option.map_none,optionalConj,Option.some.injEq] using owned.shape
      have hn := (foldCurrent_none_iff _).1 hb
      have hempty : owned.nextInputs = [] := by
        simpa only [List.map_eq_nil_iff] using (List.append_eq_nil_iff.mp hn).2
      rw [← he,guard_next_empty _ hg]
      simp only [hempty,Set.mem_empty_iff_false,List.not_mem_nil,exists_false,false_and]
    | some Body =>
      have he : .conj A (.reset R Body) = owned.canonical := by
        simpa only [canonicalSyntax,hg,hb,Option.map_some,optionalConj,Option.some.injEq] using owned.shape
      rw [← he]
      change p ∈ nextCurrentPredicates A ∪ nextCurrentPredicates Body ↔ _
      rw [guard_next_empty _ hg,Set.empty_union]
      exact locals_fold_next _ _ hb p

omit [DecidableEq Clock] in
private theorem outside_next (G : List (Guard Clock)) (R : ClockResetSet Clock) (K : MixedJ Clock Var) :
    nextCurrentPredicates (outsidePending G R K) = nextCurrentPredicates K := by
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,nextCurrentPredicates]
  | some A =>
    simp only [outsidePending,hg,nextCurrentPredicates]
    rw [guard_next_empty _ hg,Set.empty_union]

omit [DecidableEq Clock] in
private theorem boundary_guard_next (c : Clock) (m : Marker) (J : MixedJ Clock Var) :
    nextCurrentPredicates (withBoundaryGuard c m J) = nextCurrentPredicates J := by
  cases m <;> simp [withBoundaryGuard,nextCurrentPredicates]


private theorem ordinary_input_next
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned) (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates (ordinarySelectedInput R (choice.left++choice.right) choice.B
      (foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) ↔
    p ∈ nextCurrentPredicates choice.B ∨ p ∈ nextCurrentPredicates J := by
  cases hf : foldCurrent ((choice.left++choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
  | none =>
    have hn := (foldCurrent_none_iff _).1 hf
    have hempty : owned.nextInputs = [] := by
      simpa only [List.map_eq_nil_iff] using (List.append_eq_nil_iff.mp hn).2
    simp only [ordinarySelectedInput,owned_next owned p,hempty,List.not_mem_nil,exists_false,false_and,or_false]
  | some Γ =>
    simp only [ordinarySelectedInput,nextCurrentPredicates,Set.mem_union]
    rw [locals_fold_next _ _ hf p,owned_next owned p]

omit [DecidableEq Clock] in
private theorem marker_residual_next (ℓ : Marker) (L : List (Local Clock Var))
    (Ns : List (MixedJ Clock Var)) (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates (prependCurrent (.marker ℓ)
      (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next))) ↔
    ∃ K ∈ Ns, p ∈ K.currentPredicates := by
  cases hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
  | none =>
    have hn := (foldCurrent_none_iff _).1 hf
    have hempty : Ns = [] := by
      simpa only [List.map_eq_nil_iff] using (List.append_eq_nil_iff.mp hn).2
    simp only [prependCurrent,nextCurrentPredicates,Set.mem_empty_iff_false,hempty,List.not_mem_nil,exists_false,false_and]
  | some Γ =>
    simp only [prependCurrent,nextCurrentPredicates,Set.empty_union]
    exact locals_fold_next _ _ hf p

private theorem boundary_input_next
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {required : Bool} (choice : BoundaryChoice E owned required)
    (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates (boundaryReplacementChild choice.c choice.m choice.ell choice.kind choice.I choice.phi
      (.reset (copyActiveResets R (choice.left++choice.right)) choice.Gamma)) ↔
    p ∈ nextCurrentPredicates J := by
  simp only [boundaryReplacementChild,nextCurrentPredicates,Set.empty_union,boundary_guard_next]
  rw [choice.residual,marker_residual_next,owned_next owned p]

set_option maxHeartbeats 12000000 in
/-- Exact provenance in both raw outputs of the SAME selected tree. -/
theorem SelectedTree.raw_next_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (p : Predicate Clock Var) :
    (p ∈ nextCurrentPredicates H ↔ p ∈ nextCurrentPredicates J ∨
      ∃ entry ∈ T.rawLedger, p ∈ nextCurrentPredicates entry.body) ∧
    (p ∈ nextCurrentPredicates Er ↔ p ∈ nextCurrentPredicates J ∨
      ∃ entry ∈ T.rawLedger, p ∈ nextCurrentPredicates entry.body) := by
  induction T with
  | zero owned hz =>
    simp only [SelectedTree.rawLedger,List.not_mem_nil,false_and,exists_false,or_false]
    rw [← structural_next owned.regroup]
    exact ⟨Iff.rfl,Iff.rfl⟩
  | ordinary owned choice tail ih =>
    constructor
    · rw [outside_next]
      simp only [nextCurrentPredicates,Set.empty_union]
      rw [ih.1,ordinary_input_next owned choice p]
      simp only [SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto
    · rw [outside_next,ih.2,ordinary_input_next owned choice p]
      simp only [SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto
  | required owned choice tail ih =>
    constructor
    · rw [outside_next,ih.1,boundary_input_next owned choice p]
      rfl
    · rw [outside_next,ih.2,boundary_input_next owned choice p]
      rfl
  | optional owned choice upper forced tail ih =>
    constructor
    · rw [outside_next,outside_next]
      simp only [nextCurrentPredicates,Set.empty_union]
      rw [ih.1,ordinary_input_next choice.child upper p,boundary_input_next owned choice p]
      simp only [SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto
    · rw [outside_next,outside_next,ih.2,ordinary_input_next choice.child upper p,boundary_input_next owned choice p]
      simp only [SelectedTree.rawLedger,List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto


private def normalizedNextPredicates (F : Section3.TransitionForm Clock Var) : Set (Predicate Clock Var) :=
  match F.nextPart with
  | none => ∅
  | some N => {p | Local.predicate p ∈ N.locals}

omit [DecidableEq Clock] in
private theorem current_predicates_safe {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) (p : Predicate Clock Var) :
    Local.predicate p ∈ F.current.locals ↔ p ∈ J.currentPredicates := by
  induction h with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | clock => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,Section3.Judgement.currentPredicates]
  | marker => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | predicate q => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | conj h g hc ih ig => exact or_congr ih ig
  | reset R h hd ih => exact ih
  | next h hn ih => simp [Section3.TransitionForm.ofNextState,Section3.StateForm.empty,Section3.Judgement.currentPredicates]

omit [DecidableEq Clock] in
private theorem next_predicates_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextPredicates (F.union G) = normalizedNextPredicates F ∪ normalizedNextPredicates G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    ext p <;> simp [normalizedNextPredicates,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]

omit [DecidableEq Clock] in
private theorem next_predicates_safe {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    normalizedNextPredicates F = nextCurrentPredicates J := by
  induction h with
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | predicate => rfl
  | conj h g hc ih ig => exact (next_predicates_union _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | @next J F h hn ih =>
      ext p
      exact current_predicates_safe h p

omit [DecidableEq Clock] in
private theorem conjunct_next_subset {J K : MixedJ Clock Var} (h : Conjunct J K) :
    nextCurrentPredicates K ⊆ nextCurrentPredicates J := by
  induction h with
  | here => exact Set.Subset.refl _
  | left h ih => exact ih.trans Set.subset_union_left
  | right h ih => exact ih.trans Set.subset_union_right

private theorem entry_next_iff (entry : RawLedgerEntry (Clock := Clock) (Var := Var)) (p : Predicate Clock Var) :
    p ∈ nextCurrentPredicates entry.body ↔
      ∃ K, Conjunct entry.body (.next K) ∧ p ∈ K.currentPredicates := by
  constructor
  · intro hp
    obtain ⟨F,hF,hg⟩ := entry.actual.safe_normalization
    rw [← next_predicates_safe hF] at hp
    cases hn : F.nextPart with
    | none => simp only [normalizedNextPredicates,hn,Set.mem_empty_iff_false] at hp
    | some N =>
      have hmem : Local.predicate p ∈ N.locals := by
        simpa only [normalizedNextPredicates,hn,Set.mem_setOf_eq] using hp
      exact entry.actual.normalized_next_predicate_origin hF hn p hmem
  · rintro ⟨K,hK,hp⟩
    exact conjunct_next_subset hK hp

/-- Exact bidirectional provenance of the actual safely normalized full output:
every next predicate comes from an original next payload or an actual branch
in this tree's ledger, and all such contributions survive. -/
theorem SelectedTree.normalized_next_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N) (p : Predicate Clock Var) :
    Local.predicate p ∈ N.locals ↔
      (∃ K ∈ owned.nextInputs, p ∈ K.currentPredicates) ∨
      ∃ entry ∈ T.rawLedger, ∃ K, Conjunct entry.body (.next K) ∧ p ∈ K.currentPredicates := by
  have he : Local.predicate p ∈ N.locals ↔ p ∈ nextCurrentPredicates H := by
    rw [← next_predicates_safe hF]
    simp only [normalizedNextPredicates,hn,Set.mem_setOf_eq]
  rw [he,T.raw_next_provenance p |>.1,owned_next owned p]
  exact or_congr Iff.rfl (by
    constructor
    · rintro ⟨entry,hm,hp⟩
      exact ⟨entry,hm,(entry_next_iff entry p).1 hp⟩
    · rintro ⟨entry,hm,hp⟩
      exact ⟨entry,hm,(entry_next_iff entry p).2 hp⟩)

/-- The same exact next-predicate provenance for the erased output of this tree. -/
theorem SelectedTree.erased_next_provenance
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hF : SafeNormalization Er F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N) (p : Predicate Clock Var) :
    Local.predicate p ∈ N.locals ↔
      (∃ K ∈ owned.nextInputs, p ∈ K.currentPredicates) ∨
      ∃ entry ∈ T.rawLedger, ∃ K, Conjunct entry.body (.next K) ∧ p ∈ K.currentPredicates := by
  have he : Local.predicate p ∈ N.locals ↔ p ∈ nextCurrentPredicates Er := by
    rw [← next_predicates_safe hF]
    simp only [normalizedNextPredicates,hn,Set.mem_setOf_eq]
  rw [he,T.raw_next_provenance p |>.2,owned_next owned p]
  exact or_congr Iff.rfl (by
    constructor
    · rintro ⟨entry,hm,hp⟩
      exact ⟨entry,hm,(entry_next_iff entry p).1 hp⟩
    · rintro ⟨entry,hm,hp⟩
      exact ⟨entry,hm,(entry_next_iff entry p).2 hp⟩)
end STLTableau.Section4.Finiteness
