import STLTableaux.Finiteness.Derivation.Selection.SelectedLedger
import STLTableaux.Finiteness.Derivation.CanonicalResetMap

/-! Traces next judgements and their resets to the selected derivation.
Disjointness of their full clock supports prevents a reset in one next
judgement from affecting clocks in another, even if the reset binds a
clock that occurs in no predicate. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def nextPayloads : MixedJ Clock Var → Set (MixedJ Clock Var)
  | .next K => {K}
  | .conj J K => nextPayloads J ∪ nextPayloads K
  | .reset _ J => nextPayloads J
  | _ => ∅

theorem ACIdem.nextPayloads_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    nextPayloads J = nextPayloads K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

private theorem current_reset_support (J : MixedJ Clock Var) :
    (currentResetMap J).clocks ⊆ syntaxClocks J := by
  induction J with
  | terminal | clock | marker | predicate | next =>
      change ClockResetSet.empty.clocks ⊆ _
      rw [empty_reset_clocks]
      exact Set.empty_subset _
  | conj J K ih ik =>
      change ((currentResetMap J).union (currentResetMap K)).clocks ⊆ _
      rw [ClockResetSet.clocks_union]
      exact Set.union_subset_union ih ik
  | reset R J ih =>
      change ((currentResetMap J).union R).clocks ⊆ R.clocks ∪ syntaxClocks J
      rw [ClockResetSet.clocks_union]
      exact Set.union_subset (ih.trans Set.subset_union_right) Set.subset_union_left

private def mergeValue (a b : Option NNReal) : Option NNReal :=
  match a with | some v => some v | none => b

private def nextResetValue : MixedJ Clock Var → Clock → Option NNReal
  | .next K, c => (currentResetMap K).value c
  | .conj J K, c => mergeValue (nextResetValue J c) (nextResetValue K c)
  | .reset _ J, c => nextResetValue J c
  | _, _ => none

private theorem next_value_none (J : MixedJ Clock Var) (c : Clock) :
    nextResetValue J c = none ↔ ∀K∈nextPayloads J, (currentResetMap K).value c = none := by
  induction J with
  | terminal | clock | marker | predicate => simp [nextResetValue,nextPayloads]
  | next K => simp [nextResetValue,nextPayloads]
  | reset R J ih => exact ih
  | conj J K ih ik =>
      have hs : (∀L∈nextPayloads J ∪ nextPayloads K, (currentResetMap L).value c = none) ↔
          (∀L∈nextPayloads J, (currentResetMap L).value c = none) ∧
          (∀L∈nextPayloads K, (currentResetMap L).value c = none) := by
        constructor
        · intro h; exact ⟨fun L hL => h L (Or.inl hL),fun L hL => h L (Or.inr hL)⟩
        · rintro ⟨hJ,hK⟩ L (hL | hL)
          · exact hJ L hL
          · exact hK L hL
      simp only [nextResetValue,nextPayloads]
      rw [hs,← ih,← ik]
      cases nextResetValue J c <;> cases nextResetValue K c <;> simp only [mergeValue,reduceCtorEq,true_and,false_and]

private theorem next_value_origin (J : MixedJ Clock Var) (c : Clock) (v : NNReal)
    (hv : nextResetValue J c = some v) :
    ∃K∈nextPayloads J, (currentResetMap K).value c = some v := by
  induction J with
  | terminal | clock | marker | predicate => cases hv
  | next K => exact ⟨K,rfl,hv⟩
  | reset R J ih => exact ih hv
  | conj J K ih ik =>
      cases hj : nextResetValue J c with
      | none =>
          have hk : nextResetValue K c = some v := by simpa only [nextResetValue,hj,mergeValue] using hv
          obtain ⟨L,hL,hvL⟩ := ik hk
          exact ⟨L,Or.inr hL,hvL⟩
      | some w =>
          have he : w = v := by simpa only [nextResetValue,hj,mergeValue,Option.some.injEq] using hv
          subst w
          obtain ⟨L,hL,hvL⟩ := ih hj
          exact ⟨L,Or.inl hL,hvL⟩

private theorem next_value_separated (J K : MixedJ Clock Var) (c : Clock)
    (hK : K ∈ nextPayloads J) (hc : c ∈ syntaxClocks K)
    (hsep : ∀L∈nextPayloads J, L ≠ K → Disjoint (syntaxClocks L) (syntaxClocks K)) :
    nextResetValue J c = (currentResetMap K).value c := by
  have hforeign : ∀L∈nextPayloads J, L ≠ K → (currentResetMap L).value c = none := by
    intro L hL hne
    cases hv : (currentResetMap L).value c with
    | none => rfl
    | some v =>
        exact False.elim (Set.disjoint_left.1 (hsep L hL hne)
          (current_reset_support L ⟨v,hv⟩) hc)
  cases hkv : (currentResetMap K).value c with
  | none =>
      apply (next_value_none J c).2
      intro L hL
      by_cases he : L = K
      · simpa only [he] using hkv
      · exact hforeign L hL he
  | some v =>
      cases hv : nextResetValue J c with
      | none =>
          have he := (next_value_none J c).1 hv K hK
          rw [hkv] at he
          cases he
      | some w =>
          obtain ⟨L,hL,hlv⟩ := next_value_origin J c w hv
          have he : L = K := by
            by_contra hne
            rw [hforeign L hL hne] at hlv
            cases hlv
          subst L
          rw [hkv] at hlv
          exact congrArg some (Option.some.inj hlv).symm

private def normalizedNextValue (F : Section3.TransitionForm Clock Var) (c : Clock) : Option NNReal :=
  match F.nextPart with | none => none | some N => N.resets.value c

private theorem normalized_union_value (F G : Section3.TransitionForm Clock Var) (c : Clock) :
    normalizedNextValue (F.union G) c = mergeValue (normalizedNextValue F c) (normalizedNextValue G c) := by
  cases hf : F.nextPart with
  | none =>
      cases hg : G.nextPart <;> simp only [normalizedNextValue,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hf,hg,mergeValue]
  | some N =>
      cases hg : G.nextPart with
      | none =>
          simp only [normalizedNextValue,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hf,hg,mergeValue]
          cases N.resets.value c <;> rfl
      | some M =>
          simp only [normalizedNextValue,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hf,hg,Section3.StateForm.union,ClockResetSet.union,mergeValue]
          rfl

private theorem safe_next_value {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (c : Clock) : normalizedNextValue F c = nextResetValue J c := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | conj h g hc ih ig => exact (normalized_union_value _ _ c).trans (congrArg₂ mergeValue ih ig)
  | reset R h hd ih => exact ih
  | @next J F h hn ih =>
      change F.current.resets.value c = (currentResetMap J).value c
      rw [safe_reset_map h]

/-- Exact agreement on a literal payload's whole syntax support. Distinct
payload separation includes clocks used only by reset bindings or guards. -/
theorem SafeNormalization.next_reset_value_of_separated_payloads
    {J K : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} {N : Section3.StateForm Clock Var}
    (h : SafeNormalization J F) (hn : F.nextPart = some N) (hK : K ∈ nextPayloads J)
    (hsep : ∀L∈nextPayloads J, L ≠ K → Disjoint (syntaxClocks L) (syntaxClocks K))
    (c : Clock) (hc : c ∈ syntaxClocks K) :
    N.resets.value c = (currentResetMap K).value c := by
  have he := safe_next_value h c
  simp only [normalizedNextValue,hn] at he
  exact he.trans (next_value_separated J K c hK hc hsep)


private def optionPayloads : Option (MixedJ Clock Var) → Set (MixedJ Clock Var)
  | none => ∅
  | some J => nextPayloads J

private theorem optional_payloads (J K : Option (MixedJ Clock Var)) :
    optionPayloads (optionalConj J K) = optionPayloads J ∪ optionPayloads K := by
  cases J <;> cases K <;> simp [optionalConj,optionPayloads,nextPayloads]

private theorem fold_payloads (Js : List (MixedJ Clock Var)) (K : MixedJ Clock Var) :
    K ∈ optionPayloads (foldCurrent Js) ↔ ∃ J ∈ Js, K ∈ nextPayloads J := by
  induction Js with
  | nil => simp [foldCurrent,optionPayloads]
  | cons J Js ih =>
      rw [foldCurrent,optional_payloads]
      change (K ∈ nextPayloads J ∨ K ∈ optionPayloads (foldCurrent Js)) ↔ _
      simp only [ih,List.mem_cons,exists_eq_or_imp]

private theorem guard_payloads (G : List (Section3.Guard Clock)) :
    optionPayloads (foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var)))) = ∅ := by
  ext K
  rw [fold_payloads]
  simp only [List.mem_map]
  constructor
  · rintro ⟨J,⟨g,hg,rfl⟩,hK⟩; exact hK
  · exact False.elim

private theorem body_payloads (L : List (Local Clock Var)) (Ns : List (MixedJ Clock Var)) :
    optionPayloads (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) = {K | K∈Ns} := by
  ext K
  rw [fold_payloads]
  simp only [List.mem_append,List.mem_map]
  constructor
  · rintro ⟨J,(⟨l,hl,rfl⟩ | ⟨A,hA,rfl⟩),hK⟩
    · cases l <;> exact False.elim hK
    · have he : K = A := hK
      exact he ▸ hA
  · intro hK
    exact ⟨.next K,Or.inr ⟨K,hK,rfl⟩,rfl⟩

theorem canonical_nextPayloads
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)} {L : List (Local Clock Var)}
    {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) : nextPayloads C = {K | K∈Ns} := by
  have hr : optionPayloads ((foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)).map
      (Section3.Judgement.reset R)) = optionPayloads (foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)) := by
    cases foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) <;> rfl
  have he := congrArg optionPayloads h
  simp only [canonicalSyntax] at he
  rw [optional_payloads,guard_payloads,hr,body_payloads,Set.empty_union] at he
  exact he.symm

theorem OwnedPending.nextPayloads_eq
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) : nextPayloads J = {K | K∈owned.nextInputs} :=
  owned.regroup.nextPayloads_eq.trans (canonical_nextPayloads owned.shape)

@[simp] theorem nextPayloads_outsidePending (G : List (Section3.Guard Clock)) (R : ClockResetSet Clock)
    (J : MixedJ Clock Var) : nextPayloads (outsidePending G R J) = nextPayloads J := by
  have hG := guard_payloads (Var := Var) G
  cases hg : foldCurrent (G.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none => simp only [outsidePending,hg,nextPayloads]
  | some A =>
      have he : nextPayloads A = ∅ := by simpa only [hg,optionPayloads] using hG
      simp only [outsidePending,hg,nextPayloads,he,Set.empty_union]

variable [DecidableEq Clock]

/-- The terminal pending leaf is extracted from this tree, never postulated. -/
noncomputable def SelectedTree.finalNextInputs
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) : List (MixedJ Clock Var) :=
  match T with
  | .zero leaf _ => leaf.nextInputs
  | .ordinary _ _ tail => tail.finalNextInputs
  | .required _ _ tail => tail.finalNextInputs
  | .optional _ _ _ _ tail => tail.finalNextInputs

theorem SelectedTree.finalNextInputs_private
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    T.finalNextInputs.Pairwise (fun K L => Disjoint (syntaxClocks K) (syntaxClocks L)) := by
  induction T with
  | zero leaf hz => exact leaf.next_private
  | ordinary leaf choice tail ih => exact ih
  | required leaf choice tail ih => exact ih
  | optional leaf choice upper forced tail ih => exact ih

theorem SelectedTree.nextPayloads_final
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) :
    nextPayloads H = {K | K∈T.finalNextInputs} ∧ nextPayloads Er = {K | K∈T.finalNextInputs} := by
  induction T with
  | zero leaf hz => exact ⟨canonical_nextPayloads leaf.shape,canonical_nextPayloads leaf.shape⟩
  | ordinary leaf choice tail ih =>
      simpa only [nextPayloads_outsidePending,nextPayloads,Set.empty_union,SelectedTree.finalNextInputs] using ih
  | required leaf choice tail ih => simpa only [nextPayloads_outsidePending,SelectedTree.finalNextInputs] using ih
  | optional leaf choice upper forced tail ih =>
      simpa only [nextPayloads_outsidePending,nextPayloads,Set.empty_union,SelectedTree.finalNextInputs] using ih

omit [DecidableEq Clock] in
private theorem pairwise_members {Ns : List (MixedJ Clock Var)}
    (h : Ns.Pairwise (fun K L => Disjoint (syntaxClocks K) (syntaxClocks L)))
    {K L : MixedJ Clock Var} (hK : K∈Ns) (hL : L∈Ns) (hne : K≠L) :
    Disjoint (syntaxClocks K) (syntaxClocks L) := by
  induction Ns with
  | nil => cases hK
  | cons A As ih =>
      obtain ⟨ha,ht⟩ := List.pairwise_cons.1 h
      rcases List.mem_cons.1 hK with rfl | hKtail
      · rcases List.mem_cons.1 hL with rfl | hLtail
        · exact False.elim (hne rfl)
        · exact ha L hLtail
      · rcases List.mem_cons.1 hL with rfl | hLtail
        · exact (ha K hKtail).symm
        · exact ih ht hKtail hLtail

/-- Separation is proved from the final actual zero leaf of this same tree. -/
theorem SelectedTree.nextPayloads_separated
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) {K L : MixedJ Clock Var}
    (hK : K∈nextPayloads H) (hL : L∈nextPayloads H) (hne : K≠L) :
    Disjoint (syntaxClocks K) (syntaxClocks L) := by
  rw [T.nextPayloads_final.1] at hK hL
  exact pairwise_members T.finalNextInputs_private hK hL hne

/-- The same selected output has exact reset provenance on every literal
payload. No separate next-privacy or output-reset premise is supplied. -/
theorem SelectedTree.next_reset_value
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N)
    {K : MixedJ Clock Var} (hK : K∈nextPayloads H) (c : Clock) (hc : c∈syntaxClocks K) :
    N.resets.value c = (currentResetMap K).value c := by
  exact hSafe.next_reset_value_of_separated_payloads hn hK
    (fun L hL hne => T.nextPayloads_separated hL hK hne) c hc


private theorem ordinary_payloads
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} (choice : OrdinaryChoice E owned) :
    nextPayloads (ordinarySelectedInput R (choice.left ++ choice.right) choice.B
      (foldCurrent ((choice.left ++ choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) =
      nextPayloads choice.B ∪ {K | K∈owned.nextInputs} := by
  have he := body_payloads (choice.left ++ choice.right) owned.nextInputs
  cases hf : foldCurrent ((choice.left ++ choice.right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next) with
  | none =>
      have hz : {K | K∈owned.nextInputs} = (∅ : Set (MixedJ Clock Var)) := by
        simpa only [hf,optionPayloads] using he.symm
      simp only [ordinarySelectedInput,hz,Set.union_empty]
  | some Γ =>
      have hΓ : nextPayloads Γ = {K | K∈owned.nextInputs} := by simpa only [hf,optionPayloads] using he
      simp only [ordinarySelectedInput,nextPayloads,hΓ]

private theorem boundary_payloads
    {E : Set (Predicate Clock Var)} {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {required : Bool} (choice : BoundaryChoice E owned required) :
    nextPayloads (boundaryReplacementChild choice.c choice.m choice.ell choice.kind choice.I choice.phi
      (.reset (copyActiveResets R (choice.left ++ choice.right)) choice.Gamma)) = {K | K∈owned.nextInputs} := by
  have hf : foldCurrent ((Local.marker choice.ell :: choice.rest).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some choice.Gamma := by
    simp only [List.map_cons,List.cons_append,Local.toJudgement,foldCurrent_cons]
    rw [← choice.residual]
  have he := body_payloads (Local.marker choice.ell :: choice.rest) owned.nextInputs
  rw [hf] at he
  change nextPayloads choice.Gamma = {K | K∈owned.nextInputs} at he
  cases hg : Marker.imp choice.ell choice.m <;>
    simp [boundaryReplacementChild,withBoundaryGuard,hg,nextPayloads,he]

/-- Exact literal payload provenance of the SAME tree's full output. Existing
input payloads and actual recorded branches are the only sources. -/
theorem SelectedTree.nextPayloads_iff
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er) (K : MixedJ Clock Var) :
    K∈nextPayloads H ↔ K∈nextPayloads J ∨ ∃entry∈T.rawLedger, K∈nextPayloads entry.body := by
  induction T with
  | zero leaf hz =>
      rw [canonical_nextPayloads leaf.shape,leaf.nextPayloads_eq]
      simp only [SelectedTree.rawLedger,List.not_mem_nil,false_and,exists_false,or_false]
  | ordinary leaf choice tail ih =>
      simp only [nextPayloads_outsidePending,nextPayloads,Set.empty_union]
      rw [ih,ordinary_payloads choice,leaf.nextPayloads_eq]
      simp only [Set.mem_union,Set.mem_setOf_eq,SelectedTree.rawLedger,List.mem_cons]
      aesop
  | required leaf choice tail ih =>
      simp only [nextPayloads_outsidePending]
      rw [ih,boundary_payloads choice,leaf.nextPayloads_eq]
      rfl
  | optional leaf choice upper forced tail ih =>
      simp only [nextPayloads_outsidePending,nextPayloads,Set.empty_union]
      rw [ih,ordinary_payloads upper,← choice.child.nextPayloads_eq,boundary_payloads choice,leaf.nextPayloads_eq]
      simp only [Set.mem_union,Set.mem_setOf_eq,SelectedTree.rawLedger,List.mem_cons]
      aesop

/-- A recorded branch's actual literal payload has the full output's exact
reset map on its support, using final-leaf whole-syntax separation. -/
theorem SelectedTree.ledger_next_reset_value
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var}
    (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart = some N)
    {entry : RawLedgerEntry (Clock := Clock) (Var := Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : K∈nextPayloads entry.body) (c : Clock) (hc : c∈syntaxClocks K) :
    N.resets.value c = (currentResetMap K).value c := by
  exact T.next_reset_value hSafe hn ((T.nextPayloads_iff K).2 (Or.inr ⟨entry,he,hK⟩)) c hc

end STLTableau.Section4.Finiteness
