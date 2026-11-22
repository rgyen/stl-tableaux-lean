import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import STLTableaux.Finiteness.Derivation.Selection.SelectedBranchHistory
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCanonical
import STLTableaux.Finiteness.Derivation.Branches.RawBranchPrivacy
import STLTableaux.Finiteness.Derivation.Branches.RawBranchSupport
import STLTableaux.Finiteness.Inventory.LocalResetSupport
import STLTableaux.Finiteness.Derivation.CompletionInvariantTransport
import STLTableaux.Finiteness.Derivation.CanonicalProjections
import STLTableaux.Finiteness.Derivation.Pending.PendingCollection
import STLTableaux.Finiteness.Derivation.CanonicalSafety
import STLTableaux.Finiteness.Derivation.Pending.PendingChildShape
import STLTableaux.Finiteness.Derivation.Pending.PendingFold
import STLTableaux.Finiteness.Derivation.ResetScopeMerge

/-! Construction of selected ordinary pending steps. All reset and ownership
conditions below concern actual source syntax, never completion existence. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- Clock support of active CURRENT sources; outside guards and next payloads
are deliberately excluded from this protected-source condition. -/
def activeSupport (locals : List (Local Clock Var)) : Set Clock :=
  {c | ∃ p, Local.predicate p ∈ locals ∧ c ∈ syntaxClocks (.predicate p)}

def protectedActive {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) : Prop := Disjoint (activeSupport owned.locals) A

/-- Copy only inherited assignments owned by other still-active sources.
The copied bindings may lie in W; protection is against retained A, not W. -/
noncomputable def copyActiveResets (R : ClockResetSet Clock) (locals : List (Local Clock Var)) :
    ClockResetSet Clock := Finiteness.LocalResetSupport.restrictResets R (activeSupport locals)

theorem copyActiveResets_clocks (R : ClockResetSet Clock) (locals : List (Local Clock Var)) :
    (copyActiveResets R locals).clocks = R.clocks ∩ activeSupport locals :=
  Finiteness.LocalResetSupport.restrictResets_clocks R _

theorem copyActiveResets_absorb (R : ClockResetSet Clock) (locals : List (Local Clock Var)) :
    (copyActiveResets R locals).union R = R := by
  classical
  have hext : ∀ T U : ClockResetSet Clock, T.value = U.value → T = U := by
    intro T U h
    cases T
    cases U
    cases h
    rfl
  apply hext
  funext c
  change (match (if c ∈ activeSupport locals then R.value c else none) with
    | some v => some v | none => R.value c) = R.value c
  by_cases hc : c ∈ activeSupport locals
  · rw [if_pos hc]
    cases R.value c <;> rfl
  · rw [if_neg hc]

/-- Exact map absorption licenses syntactic duplication under the inherited
reset; no signal-dependent equivalence is admitted. -/
theorem copyActiveResets_expose (R : ClockResetSet Clock) (locals : List (Local Clock Var))
    (J : MixedJ Clock Var) :
    ACIdem (.reset R J) (.reset R (.reset (copyActiveResets R locals) J)) := by
  have h := ACIdem.resetNested R (copyActiveResets R locals) J
  rw [copyActiveResets_absorb] at h
  exact h.symm

theorem copied_source_exposure (R : ClockResetSet Clock) (locals : List (Local Clock Var))
    (p : Predicate Clock Var) (Γ : MixedJ Clock Var)
    (hd : Disjoint (copyActiveResets R locals).clocks
      (Section3.Judgement.freeClocks (.predicate p))) :
    ACIdem (.reset R (.conj (.predicate p) Γ))
      (.reset R (.conj (.predicate p) (.reset (copyActiveResets R locals) Γ))) :=
  .trans (copyActiveResets_expose R locals _)
    (.trans (.reset R (.resetDistrib _ _ _))
      (.reset R (.conj (.resetUnused _ _ hd) (.refl _))))

/-- Expose exactly the selected occurrence and a remainder with its original
list order. This gives a concrete decomposition for positive-step assembly. -/
theorem foldCurrent_expose_split (left right : List (MixedJ Clock Var)) (K J : MixedJ Clock Var)
    (hfold : foldCurrent (left ++ K :: right) = some J) :
    ACIdem J (prependCurrent K (foldCurrent (left ++ right))) ∧
      pendingWeight J = pendingWeight K + optionalWeight (foldCurrent (left ++ right)) := by
  induction left generalizing J with
  | nil =>
      rw [List.nil_append,foldCurrent_cons] at hfold
      have he := Option.some.inj hfold
      subst J
      refine ⟨.refl _,?_⟩
      cases h : foldCurrent right <;> simp [h,prependCurrent,optionalWeight,pendingWeight]
  | cons L Ls ih =>
      change foldCurrent (L :: (Ls ++ K :: right)) = some J at hfold
      rw [foldCurrent_cons] at hfold
      have he := Option.some.inj hfold
      subst J
      have htail : ∃ T, foldCurrent (Ls ++ K :: right) = some T := by
        cases h : foldCurrent (Ls ++ K :: right) with
        | some T => exact ⟨T,rfl⟩
        | none =>
            have hempty := (foldCurrent_none_iff _).1 h
            have hmem : K ∈ Ls ++ K :: right := List.mem_append_right _ List.mem_cons_self
            rw [hempty] at hmem
            cases hmem
      obtain ⟨T,htail⟩ := htail
      obtain ⟨hΓ,hweight⟩ := ih T htail
      rw [htail]
      change ACIdem (.conj L T)
        (prependCurrent K (foldCurrent (L :: (Ls ++ right)))) ∧ _
      rw [foldCurrent_cons]
      cases hrest : foldCurrent (Ls ++ right) with
      | none =>
          simp only [List.cons_append,foldCurrent_cons,hrest,prependCurrent,optionalWeight,pendingWeight] at hΓ hweight ⊢
          refine ⟨.trans (.conj (.refl L) hΓ) (.comm L K),?_⟩
          omega
      | some G =>
          simp only [List.cons_append,foldCurrent_cons,hrest,prependCurrent,optionalWeight,pendingWeight] at hΓ hweight ⊢
          refine ⟨.trans (.conj (.refl L) hΓ)
            (.trans (.symm (.assoc L K G))
              (.trans (.conj (.comm L K) (.refl G)) (.assoc K L G))),?_⟩
          omega

private theorem not_mem_removed {α : Type*} (left right : List α) (a : α)
    (h : (left ++ a :: right).Nodup) : a ∉ left ++ right := by
  induction left with
  | nil => exact (List.nodup_cons.mp h).1
  | cons b bs ih =>
      obtain ⟨hb,ht⟩ := List.nodup_cons.mp h
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · subst b
        exact hb (List.mem_append_right _ List.mem_cons_self)
      · exact ih ht hm

/-- Moving the selected source from active to retained strengthens protection
from A to A union source(p). Next leaves are intentionally not forbidden here. -/
theorem remaining_active_protected {J : MixedJ Clock Var} {R : ClockResetSet Clock}
    {W : Set Clock} (owned : OwnedPending J R W) (A : Set Clock)
    (hA : protectedActive owned A) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right) :
    Disjoint (activeSupport (left ++ right)) (A ∪ syntaxClocks (.predicate p)) := by
  have hsub : ∀ l ∈ left ++ right, l ∈ owned.locals := by
    intro l hl
    rw [hsplit]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hp : Local.predicate p ∈ owned.locals := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hnot : Local.predicate p ∉ left ++ right :=
    not_mem_removed left right _ (hsplit ▸ owned.locals_nodup)
  apply Set.disjoint_left.2
  rintro c ⟨q,hq,hc⟩ (hcA | hcp)
  · exact Set.disjoint_left.1 hA ⟨q,hsub _ hq,hc⟩ hcA
  · have hqp : q ≠ p := by intro he; subst q; exact hnot hq
    exact Set.disjoint_left.1 (owned.private_sources q p (hsub _ hq) hp hqp) hc hcp

theorem copied_remaining_protected {J : MixedJ Clock Var} {R : ClockResetSet Clock}
    {W : Set Clock} (owned : OwnedPending J R W) (A : Set Clock)
    (hA : protectedActive owned A) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right) :
    Disjoint (copyActiveResets R (left ++ right)).clocks
      (A ∪ syntaxClocks (.predicate p)) := by
  rw [copyActiveResets_clocks]
  exact (remaining_active_protected owned A hA p left right hsplit).mono_left Set.inter_subset_right

/-- Actual canonical current reset provenance turns history-fresh raw
introductions into a retention-safe current reset map. -/
theorem canonical_reset_protected {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (Rb : ClockResetSet Clock) (W A : Set Clock)
    (hnew : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W)
    (hsource : Disjoint Rb.clocks (syntaxClocks (.predicate p)))
    (hreset : Rb.clocks ⊆ resetNames B)
    (hA : A ∪ syntaxClocks (.predicate p) ⊆ W) :
    Disjoint Rb.clocks (A ∪ syntaxClocks (.predicate p)) := by
  apply hnew.mono
  · intro c hc
    exact ⟨hreset hc,fun hs => Set.disjoint_left.1 hsource hc hs⟩
  · exact hA

/-- The actual next current-reset map combines only fresh branch openings and
copied still-active assignments, so it avoids the newly retained annotation. -/
theorem next_current_reset_protected {J : MixedJ Clock Var} {R : ClockResetSet Clock}
    {W : Set Clock} (owned : OwnedPending J R W) (A : Set Clock)
    (hprotected : protectedActive owned A) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right)
    (Rb : ClockResetSet Clock)
    (hRb : Disjoint Rb.clocks (A ∪ syntaxClocks (.predicate p))) :
    Disjoint (Rb.union (copyActiveResets R (left ++ right))).clocks
      (A ∪ syntaxClocks (.predicate p)) := by
  rw [ClockResetSet.clocks_union]
  exact hRb.union_left (copied_remaining_protected owned A hprotected p left right hsplit)

theorem copyActiveResets_apply_inherited (R : ClockResetSet Clock) (locals : List (Local Clock Var))
    (α : ClockValuation Clock) :
    (copyActiveResets R locals).apply (R.apply α) = R.apply α := by
  rw [← ClockResetSet.apply_union_eq_comp,copyActiveResets_absorb]

private theorem nextSupport_subset (J : MixedJ Clock Var) : nextSyntaxClocks J ⊆ syntaxClocks J := by
  induction J with
  | next J ih => exact Set.Subset.refl _
  | conj J K ih ig => exact Set.union_subset_union ih ig
  | reset R J ih => exact ih.trans Set.subset_union_right
  | _ => exact Set.empty_subset _

private theorem branch_local_current {B C : MixedJ Clock Var}
    {Rb : ClockResetSet Clock} {Lb : List (Local Clock Var)} {Nb : List (MixedJ Clock Var)}
    (hshape : canonicalSyntax Rb [] Lb Nb = some C) (hBC : ACIdem B C)
    {q : Predicate Clock Var} (hq : Local.predicate q ∈ Lb) : q ∈ B.currentPredicates := by
  rw [hBC.currentPredicates_eq]
  exact (canonical_currentPredicates_iff hshape q).2 hq

private theorem branch_payload_support {B C : MixedJ Clock Var}
    {Rb : ClockResetSet Clock} {Lb : List (Local Clock Var)} {Nb : List (MixedJ Clock Var)}
    (hshape : canonicalSyntax Rb [] Lb Nb = some C) (hBC : ACIdem B C)
    {K : MixedJ Clock Var} (hK : K ∈ Nb) : syntaxClocks K ⊆ nextSyntaxClocks B := by
  rw [hBC.nextSyntaxClocks_eq,canonical_nextSyntaxClocks hshape]
  intro c hc
  exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,hc⟩⟩

private theorem old_local_budget {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {q : Predicate Clock Var}
    (hq : Local.predicate q ∈ owned.locals) : syntaxClocks (.predicate q) ⊆ W := by
  intro c hc
  exact owned.covers_input (Or.inl (Or.inr ((canonical_local_support owned.shape hq) hc)))

private theorem old_payload_budget {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) {K : MixedJ Clock Var}
    (hK : K ∈ owned.nextInputs) : syntaxClocks K ⊆ W := by
  intro c hc
  exact owned.covers_input (Or.inl (Or.inr ((canonical_payload_support owned.shape hK) hc)))

/-- Actual branch children plus untouched remaining sources satisfy every
privacy field of the new pending frame, before deterministic local collection.
This uses raw rule support and topology, not an assumed next OwnedPending. -/
theorem ordinary_child_privacy [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right)
    (x : Clock) (hx : x ∉ W) {B C : MixedJ Clock Var} (raw : RawBranch p B)
    {Rb : ClockResetSet Clock} {Lb : List (Local Clock Var)} {Nb : List (MixedJ Clock Var)}
    (hshape : canonicalSyntax Rb [] Lb Nb = some C) (hBC : ACIdem B C)
    (hlen : Nb.length ≤ 1)
    (hBsupport : syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x})
    (hchild : ∀ q ∈ B.currentPredicates, Disjoint (syntaxClocks (.predicate q)) W) :
    privateCurrent (Lb ++ (left ++ right)) ∧
      currentNextSeparate (Lb ++ (left ++ right)) (Nb ++ owned.nextInputs) ∧
      (Nb ++ owned.nextInputs).Pairwise (fun K L => Disjoint (syntaxClocks K) (syntaxClocks L)) := by
  have hsub : ∀ l ∈ left ++ right, l ∈ owned.locals := by
    intro l hl
    rw [hsplit]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hp : Local.predicate p ∈ owned.locals := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hnot : Local.predicate p ∉ left ++ right :=
    not_mem_removed left right _ (hsplit ▸ owned.locals_nodup)
  have hnew : ∀ q, Local.predicate q ∈ Lb → q ∈ B.currentPredicates :=
    fun q hq => branch_local_current hshape hBC hq
  have hpay : ∀ K ∈ Nb, syntaxClocks K ⊆ syntaxClocks (.predicate p) ∪ {x} := by
    intro K hK
    exact (branch_payload_support hshape hBC hK).trans
      ((nextSupport_subset B).trans hBsupport)
  have hcrossCurrent : ∀ q r, Local.predicate q ∈ Lb → Local.predicate r ∈ left ++ right →
      Disjoint (syntaxClocks (.predicate q)) (syntaxClocks (.predicate r)) := by
    intro q r hq hr
    exact (hchild q (hnew q hq)).mono_right (old_local_budget owned (hsub _ hr))
  have hrestNewNext : ∀ q K, Local.predicate q ∈ left ++ right → K ∈ Nb →
      Disjoint (syntaxClocks (.predicate q)) (syntaxClocks K) := by
    intro q K hq hK
    have hqp : q ≠ p := by intro he; subst q; exact hnot hq
    have hd := owned.private_sources q p (hsub _ hq) hp hqp
    apply Set.disjoint_left.2
    intro c hc hcK
    rcases hpay K hK hcK with hcp | hcx
    · exact Set.disjoint_left.1 hd hc hcp
    · have he : c = x := hcx
      subst c
      exact hx (old_local_budget owned (hsub _ hq) hc)
  have hnextCross : ∀ K ∈ Nb, ∀ L ∈ owned.nextInputs, Disjoint (syntaxClocks K) (syntaxClocks L) := by
    intro K hK L hL
    apply Set.disjoint_left.2
    intro c hc hcL
    rcases hpay K hK hc with hcp | hcx
    · exact Set.disjoint_left.1 (owned.source_next p L hp hL) hcp hcL
    · have he : c = x := hcx
      subst c
      exact hx (old_payload_budget owned hL hcL)
  refine ⟨?_,?_,?_⟩
  · intro q r hq hr hqr
    rcases List.mem_append.mp hq with hq | hq <;> rcases List.mem_append.mp hr with hr | hr
    · exact raw.current_private q (hnew q hq) r (hnew r hr) hqr
    · exact hcrossCurrent q r hq hr
    · exact (hcrossCurrent r q hr hq).symm
    · exact owned.private_sources q r (hsub _ hq) (hsub _ hr) hqr
  · intro q K hq hK
    rcases List.mem_append.mp hq with hq | hq <;> rcases List.mem_append.mp hK with hK | hK
    · exact (raw.current_next_private q (hnew q hq)).mono_right
        (branch_payload_support hshape hBC hK)
    · exact (hchild q (hnew q hq)).mono_right (old_payload_budget owned hK)
    · exact hrestNewNext q K hq hK
    · exact owned.source_next q K (hsub _ hq) hK
  · apply List.pairwise_append.mpr
    refine ⟨?_,owned.next_private,?_⟩
    · cases Nb with
      | nil => exact .nil
      | cons K Ks =>
          have hz : Ks.length = 0 := by simp only [List.length_cons] at hlen; omega
          have he : Ks = [] := by simpa using hz
          subst Ks
          exact .cons (by simp) .nil
    · exact hnextCross

/-- Assemble every field of a concrete child OwnedPending from the actually
selected branch and the proved child canonicalization. The only shape/safety
premises concern explicit source syntax; no completed resolver is supplied. -/
theorem construct_ordinary_child_owned [DecidableEq Clock]
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (A : Set Clock) (hA : A ⊆ W)
    (hprotected : protectedActive owned A) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right)
    (x : Clock) (hx : x ∉ W) {B Cb : MixedJ Clock Var} (raw : RawBranch p B)
    (Rb : ClockResetSet Clock) (Lb : List (Local Clock Var)) (Nb : List (MixedJ Clock Var))
    (hbshape : canonicalSyntax Rb [] Lb Nb = some Cb) (hBC : ACIdem B Cb)
    (hlen : Nb.length ≤ 1) (hflat : ∀ K ∈ Nb, noNext K)
    (hbSafe : ∃ Fb, SafeNormalization Cb Fb)
    (hsourceReset : Disjoint Rb.clocks (syntaxClocks (.predicate p)))
    (hreset : Rb.clocks ⊆ resetNames B)
    (hBsupport : syntaxClocks B ⊆ syntaxClocks (.predicate p) ∪ {x})
    (hHistory : Disjoint (resetNames B \ syntaxClocks (.predicate p)) W)
    (Jchild Cchild : MixedJ Clock Var)
    (hcshape : canonicalSyntax (Rb.union (copyActiveResets R (left ++ right))) []
      (PendingCollection.collect (Lb ++ (left ++ right))) (Nb ++ owned.nextInputs) = some Cchild)
    (hregroup : ACIdem Jchild Cchild) (hweight : pendingWeight Cchild ≤ pendingWeight Jchild) :
    ∃ (W' : Set Clock) (child : OwnedPending Jchild
      (Rb.union (copyActiveResets R (left ++ right))) W'),
      W ⊆ W' ∧ protectedActive child (A ∪ syntaxClocks (.predicate p)) ∧
      Disjoint (Rb.union (copyActiveResets R (left ++ right))).clocks
        (A ∪ syntaxClocks (.predicate p)) := by
  have hprivacy := ordinary_child_privacy owned p left right hsplit x hx raw hbshape hBC hlen hBsupport
    (fun q hq => raw.current_child_disjoint_history W hHistory q hq)
  have hnextSafe : ∀ K ∈ Nb ++ owned.nextInputs,
      ∃ N, SafeNormalization K (Section3.TransitionForm.ofState N) := by
    intro K hK
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨Fb,hFb⟩ := hbSafe
      exact canonical_payload_safe hbshape hFb hK
    · obtain ⟨F₀,hF₀⟩ := owned.input_safe
      exact canonical_payload_safe owned.shape hF₀ hK
  obtain ⟨Fc,hFc⟩ := CanonicalSafety.exists_safe_canonical _ [] _ _ _ hcshape hnextSafe hprivacy.2.2
  let Rc := Rb.union (copyActiveResets R (left ++ right))
  let W' := W ∪ ((syntaxClocks Jchild ∪ syntaxClocks Cchild) ∪ Rc.clocks)
  have hfinite : W'.Finite := owned.finite_budget.union
    (((syntaxClocks_finite Jchild).union (syntaxClocks_finite Cchild)).union Rc.finite_domain)
  have hprivate : privateCurrent (PendingCollection.collect (Lb ++ (left ++ right))) := by
    intro q r hq hr hqr
    exact hprivacy.1 q r (PendingCollection.mem_collect _ _ |>.1 hq)
      (PendingCollection.mem_collect _ _ |>.1 hr) hqr
  have hsourceNext : currentNextSeparate (PendingCollection.collect (Lb ++ (left ++ right)))
      (Nb ++ owned.nextInputs) := by
    intro q K hq hK
    exact hprivacy.2.1 q K (PendingCollection.mem_collect _ _ |>.1 hq) hK
  let child : OwnedPending Jchild Rc W' :=
    { guards := []
      locals := PendingCollection.collect (Lb ++ (left ++ right))
      nextInputs := Nb ++ owned.nextInputs
      canonical := Cchild
      shape := hcshape
      regroup := hregroup
      regroup_nonincrease := hweight
      locals_nodup := PendingCollection.collect_nodup _
      private_sources := hprivate
      source_next := hsourceNext
      next_private := hprivacy.2.2
      next_flat := by
        intro K hK
        rcases List.mem_append.mp hK with hK | hK
        · exact hflat K hK
        · exact owned.next_flat K hK
      absent_body_reset := by
        intro hlocals hnext
        have he := hcshape
        rw [hlocals,hnext] at he
        simp only [canonicalSyntax,List.map_nil,List.nil_append,foldCurrent,Option.map_none,
          optionalConj] at he
        cases he
      input_safe := ⟨Fc,hFc⟩
      finite_budget := hfinite
      covers_input := Set.subset_union_right }
  have hp : Local.predicate p ∈ owned.locals := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hAW : A ∪ syntaxClocks (.predicate p) ⊆ W := Set.union_subset hA (old_local_budget owned hp)
  have hRb := canonical_reset_protected Rb W A hHistory hsourceReset hreset hAW
  refine ⟨W',child,Set.subset_union_left,?_,next_current_reset_protected owned A hprotected p left right hsplit Rb hRb⟩
  apply Set.disjoint_left.2
  rintro c ⟨q,hq,hc⟩ hcA
  have hq' := (PendingCollection.mem_collect _ _).1 hq
  rcases List.mem_append.mp hq' with hqB | hqOld
  · have hqRaw := branch_local_current hbshape hBC hqB
    exact Set.disjoint_left.1 (raw.current_child_disjoint_history W hHistory q hqRaw) hc (hAW hcA)
  · exact Set.disjoint_left.1 (remaining_active_protected owned A hprotected p left right hsplit)
      ⟨q,hqOld,hc⟩ hcA

theorem free_subset_syntax (J : MixedJ Clock Var) : J.freeClocks ⊆ syntaxClocks J := by
  induction J with
  | next J ih => exact ih
  | reset R J ih => exact (Set.sdiff_subset.trans ih).trans Set.subset_union_right
  | conj J K ih ig => exact Set.union_subset_union ih ig
  | predicate p => cases p <;> exact Set.Subset.refl _
  | _ => exact Set.Subset.refl _

theorem reset_subset_syntax (J : MixedJ Clock Var) : resetNames J ⊆ syntaxClocks J := by
  induction J with
  | next J ih => exact ih
  | reset R J ih => exact Set.union_subset_union (Set.Subset.refl _) ih
  | conj J K ih ig => exact Set.union_subset_union ih ig
  | _ => exact Set.empty_subset _

private theorem current_predicate_support (J : MixedJ Clock Var) (p : Predicate Clock Var)
    (hp : p ∈ J.currentPredicates) : syntaxClocks (.predicate p) ⊆ syntaxClocks J := by
  induction J with
  | predicate q =>
      have he : p = q := hp
      subst p
      exact Set.Subset.refl _
  | conj J K ih ig =>
      rcases hp with hp | hp
      · exact (ih hp).trans Set.subset_union_left
      · exact (ig hp).trans Set.subset_union_right
  | reset R J ih => exact (ih hp).trans Set.subset_union_right
  | _ => cases hp

theorem branch_canonical_support {B C : MixedJ Clock Var}
    {Rb : ClockResetSet Clock} {Lb : List (Local Clock Var)} {Nb : List (MixedJ Clock Var)}
    (hs : canonicalSyntax Rb [] Lb Nb = some C) (hBC : ACIdem B C)
    (hr : Rb.clocks ⊆ resetNames B) : syntaxClocks C ⊆ syntaxClocks B := by
  cases hb : foldCurrent (Lb.map Local.toJudgement ++ Nb.map Section3.Judgement.next) with
  | none => simp [canonicalSyntax,hb,foldCurrent,optionalConj] at hs
  | some K =>
      have he : .reset Rb K = C := by
        simpa only [canonicalSyntax,List.map_nil,foldCurrent,optionalConj,hb,Option.map_some,Option.some.injEq] using hs
      subst C
      apply Set.union_subset (hr.trans (reset_subset_syntax B))
      apply syntaxClocks_foldCurrent_subset hb
      intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hL
        cases l with
        | predicate q => exact current_predicate_support B q (branch_local_current hs hBC hl)
        | terminal => exact Set.empty_subset _
        | marker => exact Set.empty_subset _
      · obtain ⟨N,hN,rfl⟩ := List.mem_map.mp hL
        exact (branch_payload_support hs hBC hN).trans (nextSupport_subset B)

theorem remaining_body_support {J : MixedJ Clock Var} {R : ClockResetSet Clock}
    {W : Set Clock} (owned : OwnedPending J R W) (p : Predicate Clock Var)
    (left right : List (Local Clock Var)) (hsplit : owned.locals = left ++ .predicate p :: right)
    (Γ : MixedJ Clock Var)
    (hf : foldCurrent ((left ++ right).map Local.toJudgement ++
      owned.nextInputs.map Section3.Judgement.next) = some Γ) :
    syntaxClocks Γ ⊆ W ∧ Disjoint (syntaxClocks (.predicate p)) (syntaxClocks Γ) := by
  have hsub : ∀ l ∈ left ++ right, l ∈ owned.locals := by
    intro l hl
    rw [hsplit]
    simp only [List.mem_append,List.mem_cons] at hl ⊢
    tauto
  have hp : Local.predicate p ∈ owned.locals := by
    rw [hsplit]
    exact List.mem_append_right _ List.mem_cons_self
  have hnot : Local.predicate p ∉ left ++ right := not_mem_removed left right _ (hsplit ▸ owned.locals_nodup)
  have hparts : ∀ K ∈ (left ++ right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next,
      syntaxClocks K ⊆ W ∧ Disjoint (syntaxClocks (.predicate p)) (syntaxClocks K) := by
    intro K hK
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hK
      cases l with
      | terminal => exact ⟨Set.empty_subset _,Set.disjoint_empty _⟩
      | marker => exact ⟨Set.empty_subset _,Set.disjoint_empty _⟩
      | predicate q =>
          have hpq : p ≠ q := by intro he; subst q; exact hnot hl
          exact ⟨old_local_budget owned (hsub _ hl),owned.private_sources p q hp (hsub _ hl) hpq⟩
    · obtain ⟨N,hN,he⟩ := List.mem_map.mp hK
      subst K
      exact ⟨old_payload_budget owned (K := N) hN,owned.source_next p N hp hN⟩
  refine ⟨syntaxClocks_foldCurrent_subset hf (fun K hK => (hparts K hK).1), ?_⟩
  apply Set.disjoint_left.2
  intro c hcp hcΓ
  obtain ⟨K, hK, hcK⟩ := (mem_syntaxClocks_foldCurrent_iff hf c).1 hcΓ
  exact Set.disjoint_left.1 (hparts K hK).2 hcp hcK

end STLTableau.Section4.Finiteness
