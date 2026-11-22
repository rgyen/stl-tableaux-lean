import STLTableaux.Closure.Catalogue.FaithfulContextualCatalogue
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCurrentShape
import STLTableaux.Finiteness.Derivation.Branches.RawBranchCanonical
import STLTableaux.Finiteness.Derivation.Branches.RawBranchUpperShape

namespace STLTableau.Section3.ConcreteContextual
open STLTableau.Section4.Finiteness (RawBranch timedFormula)
open scoped STL
variable {Clock Var : Type*} [DecidableEq Clock]

omit [DecidableEq Clock] in
private theorem reset_ext {Λ Μ : ClockResetSet Clock} (h : Λ.value = Μ.value) : Λ = Μ := by
  cases Λ; cases Μ; cases h; rfl

private theorem reset_rename_singleton (e : Equiv.Perm Clock) (c : Clock) :
    (ClockResetSet.singleton c 0).rename e = ClockResetSet.singleton (e c) 0 := by
  apply reset_ext
  funext d
  have h : e.symm d = c ↔ d = e c := by
    constructor <;> intro h
    · simpa using congrArg e h
    · simp [h]
  simp only [ClockResetSet.rename, ClockResetSet.singleton, h]

omit [DecidableEq Clock] in
private theorem reset_union_empty_right (Λ : ClockResetSet Clock) :
    Λ.union ClockResetSet.empty = Λ := by
  apply reset_ext
  funext x
  simp [ClockResetSet.union, ClockResetSet.empty]
  cases Λ.value x <;> rfl

omit [DecidableEq Clock] in
private theorem reset_union_empty_left (Λ : ClockResetSet Clock) :
    ClockResetSet.empty.union Λ = Λ := by
  apply reset_ext
  rfl

omit [DecidableEq Clock] in
@[simp] theorem underReset_empty_branchwise (F : TransitionForm Clock Var) :
    F.underReset ClockResetSet.empty = F := by
  cases F with
  | mk S N => cases S; simp [TransitionForm.underReset, reset_union_empty_right]

def openingForm (c : Clock) (m : Marker) (k : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) : TransitionForm Clock Var :=
  (TransitionForm.ofState ((StateForm.ofLocal (.predicate (.upper c m k I φ))).union
    (StateForm.ofLocal (.marker m)))).underReset (ClockResetSet.singleton c 0)

@[simp] theorem openingForm_next (c : Clock) (m : Marker) (k : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) : (openingForm c m k I φ).nextPart = none := rfl

@[simp] theorem openingForm_resets (c : Clock) (m : Marker) (k : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (openingForm c m k I φ).current.resets = ClockResetSet.singleton c 0 := by
  change (ClockResetSet.empty.union ClockResetSet.empty).union _ = _
  simp only [reset_union_empty_left]


theorem mixed_opening_branch (c : Clock) (m : Marker) (k : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Λ : ClockResetSet Clock) :
    ConcreteMixed.catalogue.Branch (.plain (timedFormula k I φ)) Λ
      ((openingForm c m k I φ).underReset Λ) := by
  cases I with
  | bounded I =>
    left
    cases k with
    | always =>
      refine ⟨_, _, ⟦c ↦ᶜ 0⟧ ·ⱼ (STLTableau.Judgement.predicate (.upper c m .always I φ) ∧ⱼ lty[m]),
        _, rfl, .openAlways c I φ, ?_, rfl, rfl⟩
      cases m <;> simp [ExpansionRule.openAlways]
    | eventually =>
      refine ⟨_, _, ⟦c ↦ᶜ 0⟧ ·ⱼ (STLTableau.Judgement.predicate (.upper c m .eventually I φ) ∧ⱼ lty[m]),
        _, rfl, .openEventually c I φ, ?_, rfl, rfl⟩
      cases m <;> simp [ExpansionRule.openEventually]
  | unbounded a => exact Or.inr (Or.inr ⟨c, m, k, a, φ, _, by cases k <;> rfl, rfl, rfl⟩)

theorem opening_branch (c : Clock) (m : Marker) (k : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Λ : ClockResetSet Clock) :
    Branch (.plain (timedFormula k I φ)) Λ ((openingForm c m k I φ).underReset Λ) := by
  refine ⟨(openingForm c m k I φ).underReset ClockResetSet.empty, _,
    mixed_opening_branch c m k I φ _, ?_, rfl⟩
  rw [underReset_empty_branchwise]
  exact .refl _

@[simp] theorem openingForm_current_mem (c : Clock) (m : Marker) (k : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (q : Predicate Clock Var) :
    Local.predicate q ∈ (openingForm c m k I φ).current.locals ↔ q = .upper c m k I φ := by
  simp [openingForm, TransitionForm.underReset, TransitionForm.ofState,
    StateForm.union, StateForm.ofLocal]

private theorem mixed_raw {p : Predicate Clock Var} {R : TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) :
    ∃ J, RawBranch p J ∧ TransitionForm.normalize? J = some R := by
  rcases h with h | h | h
  · obtain ⟨p₀, E, J, F, rfl, hE, hJ, hn, rfl⟩ := h
    exact ⟨_, .finite hE hJ, by simpa using hn⟩
  · obtain ⟨p₀, E, J, F, rfl, hE, hJ, hn, rfl⟩ := h
    exact ⟨_, .infinite hE hJ, by simpa using hn⟩
  · obtain ⟨c, m, k, a, φ, F, rfl, hn, rfl⟩ := h
    exact ⟨_, .opening c m k a φ, by simpa using hn⟩

theorem branch_no_bounded_child {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : TransitionForm Clock Var} (h : Branch p Λ B)
    (c d : Clock) (m n : Marker) (k : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    Local.predicate (.bounded c d m n k I φ) ∉ B.current.locals := by
  obtain ⟨R, A, hR, ha, rfl⟩ := h
  obtain ⟨J, hJ, hn⟩ := mixed_raw hR
  let Q : Predicate Clock Var → Prop := fun q => match q with | .bounded .. => False | _ => True
  have hQR : ∀ q, Local.predicate q ∈ R.current.locals → Q q := by
    intro q hq
    cases q with
    | plain | upper => trivial
    | bounded => exact hJ.no_current_bounded _ _ _ _ _ _ _ ((TransitionForm.normalize_currentPredicates J hn _).1 hq)
  have hQA := (ha.current_property Q (by intro e q; cases q <;> rfl)).2 hQR
  exact hQA _

private theorem opening_outer (e : Equiv.Perm Clock) (c : Clock) (m : Marker)
    (k : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (openingForm c m k I φ).alphaOuter e = openingForm (e c) m k I φ := by
  simp [openingForm, TransitionForm.alphaOuter, TransitionForm.underReset, TransitionForm.ofState,
    StateForm.alphaReset, StateForm.rename, StateForm.union, StateForm.ofLocal,
    reset_union_empty_left, Set.image_insert_eq, Local.rename, Predicate.rename,
    reset_rename_singleton]

omit [DecidableEq Clock] in
private theorem alphaOuter_inverse_shape (F : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (F.alphaOuter e).alphaOuter e.symm = F := by
  have hs : ∀ S : StateForm Clock Var, (S.rename e).rename e.symm = S := by
    intro S
    have hl : ∀ l : Local Clock Var, (l.rename e).rename e.symm = l := by
      intro l; cases l with
      | terminal | marker => rfl
      | predicate p => cases p <;> simp [Local.rename, Predicate.rename]
    have hg : ∀ g : Guard Clock, (g.rename e).rename e.symm = g := by
      intro g; cases g; simp [Guard.rename]
    have hr : (S.resets.rename e).rename e.symm = S.resets := by
      apply reset_ext
      funext x
      simp [ClockResetSet.rename]
    cases S
    simp [StateForm.rename, Set.image_image, hl, hg, hr]
  have ha : ∀ S : StateForm Clock Var, (S.alphaReset e).alphaReset e.symm = S := by
    intro S
    have h := hs S
    have hh := congrArg (fun R : StateForm Clock Var =>
      StateForm.mk S.guards S.guards_finite R.resets R.locals R.locals_finite) h
    cases S
    exact hh
  cases F with
  | mk S N => cases N <;> simp [TransitionForm.alphaOuter, ha, hs]

private theorem alpha_opening {F G : TransitionForm Clock Var}
    (h : F.AlphaEquivalent G) (m : Marker) (k : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (∃ c, F = openingForm c m k I φ) ↔ (∃ c, G = openingForm c m k I φ) := by
  induction h with
  | refl => rfl
  | outer F e _ =>
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨e.symm c, ?_⟩
      calc
        F = (F.alphaOuter e).alphaOuter e.symm := (alphaOuter_inverse_shape F e).symm
        _ = _ := by rw [hc, opening_outer]
    · rintro ⟨c, rfl⟩; exact ⟨e c, opening_outer e c m k I φ⟩
  | next F e _ =>
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        F = (F.alphaNext e).alphaNext e.symm := (F.alphaNext_inverse e).symm
        _ = _ := by rw [hc]; rfl
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

theorem branch_upper_child {p : Predicate Clock Var} {Λ : ClockResetSet Clock}
    {B : TransitionForm Clock Var} (h : Branch p Λ B)
    {c : Clock} {m : Marker} {k : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (hq : Local.predicate (.upper c m k I φ) ∈ B.current.locals) :
    p = .plain (timedFormula k I φ) ∧ B = (openingForm c m k I φ).underReset Λ := by
  obtain ⟨R, A, hR, ha, rfl⟩ := h
  obtain ⟨J, hJ, hn⟩ := mixed_raw hR
  let Q : Predicate Clock Var → Prop := fun q => match q with
    | .upper _ m' k' I' φ' => ¬ (m' = m ∧ k' = k ∧ I' = I ∧ φ' = φ)
    | _ => True
  have h : ¬ (∀ q, Local.predicate q ∈ R.current.locals → Q q) := by
    intro h
    exact ((ha.current_property Q (by intro e q; cases q <;> rfl)).2 h) _ hq ⟨rfl,rfl,rfl,rfl⟩
  classical
  push Not at h
  obtain ⟨q, hqR, hq⟩ := h
  cases q with
  | plain | bounded => exact (hq trivial).elim
  | upper c' m' k' I' φ' =>
    have hEq : m' = m ∧ k' = k ∧ I' = I ∧ φ' = φ := by simpa [Q] using hq
    rcases hEq with ⟨hm,hk,hI,hφ⟩
    subst m'; subst k'; subst I'; subst φ'
    obtain ⟨hp, rfl⟩ := hJ.current_upper_opening c' m k I φ
      ((TransitionForm.normalize_currentPredicates J hn _).1 hqR)
    have hR' : openingForm c' m k I φ = R := Option.some.inj hn
    obtain ⟨x, rfl⟩ := (alpha_opening ha m k I φ).2 ⟨c', hR'.symm⟩
    have hc : Predicate.upper c m k I φ = .upper x m k I φ :=
      (openingForm_current_mem x m k I φ _).1 hq
    injection hc with hc
    subst x
    exact ⟨hp, rfl⟩


theorem mixed_current_reset_zero {p : Predicate Clock Var} {R : TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R)
    {c : Clock} {a : NNReal} (hr : R.current.resets.value c = some a) : a = 0 := by
  obtain ⟨J, hJ, hn⟩ := mixed_raw h
  obtain ⟨F, hF, _⟩ := hJ.safe_normalization
  have he : F = R := Option.some.inj (hF.normalizes.symm.trans hn)
  subst R
  obtain ⟨M, L, N, C, hshape, hstruct, hw, hlen, hflat, hm, hsafe, hd, hs, hmap⟩ :=
    hJ.canonical_with_exact_reset_map
  rw [STLTableau.Section4.Finiteness.safe_reset_map hF, ← hmap] at hr
  rcases hm with rfl | ⟨d, rfl⟩
  · cases hr
  · by_cases he : c = d
    · subst c
      have hv : (some (0 : NNReal)) = some a := by
        simpa only [ClockResetSet.singleton, eq_self, if_true] using hr
      exact (Option.some.inj hv).symm
    · have hv : (none : Option NNReal) = some a := by
        simpa only [ClockResetSet.singleton, if_neg he] using hr
      cases hv


theorem alpha_current_reset_zero {p : Predicate Clock Var} {R A : TransitionForm Clock Var}
    (h : ConcreteMixed.catalogue.Branch p ClockResetSet.empty R) (ha : A.AlphaEquivalent R)
    {c : Clock} {a : NNReal} (hr : A.current.resets.value c = some a) : a = 0 := by
  let Q : StateForm Clock Var → Prop := fun S =>
    ∀ c a, S.resets.value c = some a → a = 0
  have hQ : ∀ S e, Q (S.alphaReset e) ↔ Q S := by
    intro S e
    constructor
    · intro h c a hc
      apply h (e c) a
      simpa [StateForm.alphaReset, StateForm.rename, ClockResetSet.rename] using hc
    · intro h c a hc
      exact h (e.symm c) a hc
  have hobs : Q A.current ↔ Q R.current := by
    clear h hr
    induction ha with
    | refl => rfl
    | outer F e _ => exact hQ F.current e
    | next => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih ih' => exact ih.trans ih'
  exact hobs.2 (fun _ _ => mixed_current_reset_zero h) c a hr


end STLTableau.Section3.ConcreteContextual
