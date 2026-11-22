import STLTableaux.Finiteness.Derivation.NextPayloadLocals
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperEntry
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCanonical
import STLTableaux.Finiteness.Bounds.RightClockContext

/-! Actual upper-entry and bounded right-clock facts lifted through the SAME
selected tree into its complete normalized next state. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

private theorem conjunct_payload_subset {B J : MixedJ Clock Var} (h : Conjunct B J) :
    nextPayloads J ⊆ nextPayloads B := by
  induction h with
  | here => exact Set.Subset.rfl
  | left h ih => exact ih.trans Set.subset_union_left
  | right h ih => exact ih.trans Set.subset_union_right

theorem Conjunct.nextPayload_mem {B K : MixedJ Clock Var} (h : Conjunct B (.next K)) :
    K∈nextPayloads B := conjunct_payload_subset h rfl

private theorem predicate_local (J : MixedJ Clock Var) (p : Predicate Clock Var) :
    Local.predicate p ∈ currentLocalSet J ↔ p ∈ J.currentPredicates := by
  induction J with
  | terminal | marker | clock | next => simp [currentLocalSet,Section3.Judgement.currentPredicates]
  | predicate q => simp [currentLocalSet,Section3.Judgement.currentPredicates]
  | conj J K ih ik => exact or_congr ih ik
  | reset R J ih => exact ih

private theorem predicate_support {J : MixedJ Clock Var} {p : Predicate Clock Var}
    (hp : p∈J.currentPredicates) : syntaxClocks (.predicate p) ⊆ syntaxClocks J := by
  induction J with
  | terminal | clock | marker | next => cases hp
  | predicate q => have he : p=q := hp; subst p; exact Set.Subset.rfl
  | conj J K ih ik =>
      rcases hp with hp | hp
      · exact (ih hp).trans Set.subset_union_left
      · exact (ik hp).trans Set.subset_union_right
  | reset R J ih => exact (ih hp).trans Set.subset_union_right

private theorem no_next_empty {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (hn : F.nextPart = none) : nextPayloads J = ∅ := by
  induction h with
  | terminal | clock | marker | predicate => rfl
  | reset R h hd ih => exact ih hn
  | next h hnone ih => cases hn
  | @conj J K F G h g hc ih ig =>
      cases hf : F.nextPart <;> cases hg : G.nextPart
      · change nextPayloads J ∪ nextPayloads K = ∅
        rw [ih hf,ig hg,Set.union_empty]
      all_goals simp [Section3.TransitionForm.union,Section3.TransitionForm.unionNext,hf,hg] at hn

private theorem payload_next_exists {J K : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (hK : K∈nextPayloads J) : ∃N,F.nextPart=some N := by
  cases hn : F.nextPart with
  | some N => exact ⟨N,rfl⟩
  | none => rw [no_next_empty h hn] at hK; cases hK

private theorem raw_payload_unique [DecidableEq Clock]
    {p : Predicate Clock Var} {B K L : MixedJ Clock Var} (raw : RawBranch p B)
    (hK : K∈nextPayloads B) (hL : L∈nextPayloads B) : K=L := by
  obtain ⟨R,Ls,Ns,C,hs,hBC,_,hlen,_⟩ := raw.canonical
  rw [hBC.nextPayloads_eq,canonical_nextPayloads hs] at hK hL
  cases Ns with
  | nil => cases hK
  | cons A As =>
      have htail : As=[] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
      subst As
      have heK : K=A := by simpa only [Set.mem_setOf_eq,List.mem_cons,List.not_mem_nil,or_false] using hK
      have heL : L=A := by simpa only [Set.mem_setOf_eq,List.mem_cons,List.not_mem_nil,or_false] using hL
      exact heK.trans heL.symm

private theorem no_reset_current_map (d : Clock) (J : MixedJ Clock Var)
    (h : RightClockAge.NoRightReset d J) : (currentResetMap J).value d = none := by
  induction J with
  | terminal | clock | marker | predicate | next => rfl
  | conj J K ih ik =>
      change ((currentResetMap J).union (currentResetMap K)).value d = none
      simp only [ClockResetSet.union,ih h.1,ik h.2]
  | reset R J ih =>
      change ((currentResetMap J).union R).value d = none
      simp only [ClockResetSet.union,ih h.2,h.1]

private theorem conjunct_preserves_no_reset {B J : MixedJ Clock Var} (hJ : Conjunct B J)
    (d : Clock) (h : RightClockAge.NoRightReset d B) : RightClockAge.NoRightReset d J := by
  induction hJ with
  | here => exact h
  | left hJ ih => exact ih h.1
  | right hJ ih => exact ih h.2

private theorem conjunct_no_reset {B K : MixedJ Clock Var} (hK : Conjunct B (.next K))
    (d : Clock) (h : RightClockAge.NoRightReset d B) : RightClockAge.NoRightReset d K :=
  conjunct_preserves_no_reset hK d h

variable [DecidableEq Clock]

/-- The complete next map retains the right endpoint of an actual continuing
`↑↓` source. A finish-only payload need not protect an unused right clock. -/
theorem SelectedTree.ledger_bounded_right_unreset
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var} (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {entry : RawLedgerEntry (Clock:=Clock) (Var:=Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : Conjunct entry.body (.next K))
    (c d : Clock) (b q m q' : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hsource : entry.source = .bounded c d b q kind I φ)
    (hq : Predicate.bounded c d m q' kind I φ ∈ K.currentPredicates) : N.resets.value d = none := by
  have raw : RawBranch (.bounded c d b q kind I φ) entry.body := hsource ▸ entry.actual
  have hNo := RightClockContext.owned_bounded_noRightReset c d b q kind I φ entry.body raw
  have hd : d∈syntaxClocks K := predicate_support hq (Or.inr (Set.mem_singleton d))
  rw [T.ledger_next_reset_value hSafe hn he hK.nextPayload_mem d hd]
  exact no_reset_current_map d K (conjunct_no_reset hK d hNo)

/-- The reset and left marker from an expansion of the `↑` form are
preserved in the complete next state after normalization. -/
theorem SelectedTree.ledger_upper_entry
    {E : Set (Predicate Clock Var)} {U : Set Clock}
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    {owned : OwnedPending J R W} {H Er : MixedJ Clock Var} (T : SelectedTree E U owned H Er)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization H F)
    {N : Section3.StateForm Clock Var} (hn : F.nextPart=some N)
    {entry : RawLedgerEntry (Clock:=Clock) (Var:=Var)} (he : entry∈T.rawLedger)
    {K : MixedJ Clock Var} (hK : Conjunct entry.body (.next K))
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hsource : ∃b,entry.source=.upper c b kind I φ)
    (hq : Predicate.bounded c d m q kind I φ ∈ K.currentPredicates) :
    ∃ell, q=Marker.complement ell ∧ Local.marker ell∈N.locals ∧ N.resets.value d=some 0 ∧
      (Marker.imp ell m=Marker.open → N.resets.value c=none) ∧
      Nonempty (FrozenByUpper c d m ell kind I φ) := by
  have hPayload := hK.nextPayload_mem
  obtain ⟨Bf,hBf,_⟩ := entry.actual.safe_normalization
  obtain ⟨M,hM⟩ := payload_next_exists hBf hPayload
  have hqM : Local.predicate (.bounded c d m q kind I φ)∈M.locals :=
    hBf.next_local_of_payload hM hPayload ((predicate_local K _).2 hq)
  obtain ⟨ell,K',hqell,hmM,hdM,hcM,hK',hfrozen⟩ :=
    entry.actual.normalized_upper_entry_certificate hBf hM c d m q kind I φ hqM hsource
  have hcd : c≠d := by
    rcases entry.actual.next_bounded_origin hK c d m q kind I φ hq with hupper | hbounded
    · exact hupper.choose_spec.2.1
    · obtain ⟨b,hb,_⟩ := hbounded
      obtain ⟨b',hu⟩ := hsource
      rw [hu] at hb
      cases hb
  have hsep : ∀L∈nextPayloads entry.body,L≠K → Disjoint (syntaxClocks L) (syntaxClocks K) := by
    intro L hL hne
    exact False.elim (hne (raw_payload_unique entry.actual hL hPayload))
  have hcK : c∈syntaxClocks K := predicate_support hq (Or.inl rfl)
  have hdK : d∈syntaxClocks K := predicate_support hq (Or.inr (Set.mem_singleton d))
  have hsmallc := hBf.next_reset_value_of_separated_payloads hM hPayload hsep c hcK
  have hsmalld := hBf.next_reset_value_of_separated_payloads hM hPayload hsep d hdK
  have hbigc := T.ledger_next_reset_value hSafe hn he hPayload c hcK
  have hbigd := T.ledger_next_reset_value hSafe hn he hPayload d hdK
  obtain ⟨L,hL,hmL⟩ := (hBf.next_local_iff hM (.marker ell)).1 hmM
  have hLK : L=K := raw_payload_unique entry.actual hL hPayload
  subst L
  have hmN := T.ledger_next_local hSafe hn he hPayload hmL
  obtain ⟨b,hb⟩ := hsource
  have frozen : FrozenByUpper c d m ell kind I φ :=
    ⟨hcd,b,entry.body,K',hb ▸ entry.actual,hK',hfrozen⟩
  refine ⟨ell,hqell,hmN,hbigd.trans (hsmalld.symm.trans hdM),?_,⟨frozen⟩⟩
  intro hstrict
  exact hbigc.trans (hsmallc.symm.trans (hcM hstrict))

end STLTableau.Section4.Finiteness
