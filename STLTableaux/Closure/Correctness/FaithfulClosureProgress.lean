import STLTableaux.Closure.Correctness.MixedConcreteClosure
import STLTableaux.Closure.Subsumption.FaithfulClosureOrder

/-! Syntactic progress for the faithful mixed closure construction. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace FaithfulClosure

/-- Number of current predicate occurrences; next predicates belong to the
successor generator and do not contribute to closure termination here. -/
def currentWidth : Judgement Clock Var → ℕ
  | .predicate _ => 1
  | .conj Ψ Χ => currentWidth Ψ + currentWidth Χ
  | .reset _ Ψ => currentWidth Ψ
  | _ => 0

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem finite_branch_width [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) : currentWidth (Judgement.ofFinite B) ≤ 2 := by
  classical
  open STLTableau.ExpansionRule in
    cases hr <;>
      simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
        upperAlways, boundedAlways, upperEventually, boundedEventually,
        List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlways_defer, upperAlways_check, boundedAlways_defer,
        boundedAlways_check, boundedAlways_finish, upperEventually_defer,
        upperEventually_check, boundedEventually_defer, boundedEventually_check,
        boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
        STLTableau.Judgement.markedGT_eq_clock, Judgement.ofFinite, currentWidth]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem infinite_branch_width [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var}
    (hB : B ∈ Bs) : currentWidth (Judgement.ofUnbounded B) ≤ 2 := by
  classical
  open UnboundedClocked in
    cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        Node.lt, Node.gt, Judgement.ofUnbounded, currentWidth]

@[simp] theorem opening_branch_width [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
    currentWidth (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) = 1 := rfl

noncomputable def currentPredicates (Ψ : Judgement Clock Var) : Finset (Predicate Clock Var) := by
  classical
  exact match Ψ with
    | .predicate p => {p}
    | .conj Ψ Χ => currentPredicates Ψ ∪ currentPredicates Χ
    | .reset _ Ψ => currentPredicates Ψ
    | _ => ∅

@[simp] theorem mem_currentPredicates (Ψ : Judgement Clock Var) (p : Predicate Clock Var) :
    p ∈ currentPredicates Ψ ↔ p ∈ Ψ.currentPredicates := by
  induction Ψ with
  | predicate q => simp [currentPredicates, Judgement.currentPredicates]
  | conj Ψ Χ ihΨ ihΧ => simp [currentPredicates, Judgement.currentPredicates, ihΨ, ihΧ]
  | reset Λ Ψ ih => exact ih
  | _ => simp [currentPredicates, Judgement.currentPredicates]

theorem currentPredicates_card (Ψ : Judgement Clock Var) :
    (currentPredicates Ψ).card ≤ currentWidth Ψ := by
  classical
  induction Ψ with
  | predicate p => simp [currentPredicates, currentWidth]
  | conj Ψ Χ ihΨ ihΧ =>
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add ihΨ ihΧ)
  | reset Λ Ψ ih => exact ih
  | _ => simp [currentPredicates, currentWidth]

noncomputable def statePredicates (S : StateForm Clock Var) : Finset (Predicate Clock Var) := by
  classical
  exact S.locals_finite.toFinset.biUnion (fun l => match l with
    | .predicate p => {p}
    | _ => ∅)

@[simp] theorem mem_statePredicates (S : StateForm Clock Var) (p : Predicate Clock Var) :
    p ∈ statePredicates S ↔ Local.predicate p ∈ S.locals := by
  classical
  simp only [statePredicates, Finset.mem_biUnion, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨l, hl, hp⟩
    cases l with
    | predicate q => simpa using (Finset.mem_singleton.mp hp) ▸ hl
    | terminal => simp at hp
    | marker m => simp at hp
  · intro hp
    exact ⟨.predicate p, hp, Finset.mem_singleton_self p⟩

theorem normalize_statePredicates {Ψ : Judgement Clock Var} {F : TransitionForm Clock Var}
    (he : TransitionForm.normalize? Ψ = some F) :
    statePredicates F.current = currentPredicates Ψ := by
  classical
  ext p
  rw [mem_statePredicates, mem_currentPredicates]
  exact TransitionForm.normalize_currentPredicates Ψ he p

theorem finite_normalized_branch_card [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) {F : TransitionForm Clock Var}
    (he : TransitionForm.normalize? (Judgement.ofFinite B) = some F) :
    (statePredicates F.current).card ≤ 2 := by
  rw [normalize_statePredicates he]
  exact (currentPredicates_card _).trans (finite_branch_width hr hB)

theorem infinite_normalized_branch_card [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var}
    (hB : B ∈ Bs) {F : TransitionForm Clock Var}
    (he : TransitionForm.normalize? (Judgement.ofUnbounded B) = some F) :
    (statePredicates F.current).card ≤ 2 := by
  rw [normalize_statePredicates he]
  exact (currentPredicates_card _).trans (infinite_branch_width hr hB)

theorem opening_normalized_branch_card [DecidableEq Clock]
    (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var)
    {F : TransitionForm Clock Var}
    (he : TransitionForm.normalize?
      (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ)) = some F) :
    (statePredicates F.current).card ≤ 2 := by
  rw [normalize_statePredicates he]
  exact (currentPredicates_card _).trans (by simp)

def currentGuardWidth : Judgement Clock Var → ℕ
  | .clock _ _ _ => 1
  | .conj Ψ Χ => currentGuardWidth Ψ + currentGuardWidth Χ
  | .reset _ Ψ => currentGuardWidth Ψ
  | _ => 0

theorem normalize_currentGuards_empty (Ψ : Judgement Clock Var)
    {F : TransitionForm Clock Var} (hn : TransitionForm.normalize? Ψ = some F)
    (hz : currentGuardWidth Ψ = 0) : F.current.guards = ∅ := by
  induction Ψ generalizing F with
  | terminal => cases hn; rfl
  | clock c r a => simp [currentGuardWidth] at hz
  | marker m => cases hn; rfl
  | predicate p => cases hn; rfl
  | reset Λ Ψ ih =>
      cases he : TransitionForm.normalize? Ψ with
      | none => simp [TransitionForm.normalize?, he] at hn
      | some G =>
          simp only [TransitionForm.normalize?, he, Option.map_some, Option.some.injEq] at hn
          subst F
          exact ih (F := G) he hz
  | conj Ψ Χ ihΨ ihΧ =>
      have hzΨ : currentGuardWidth Ψ = 0 := by simp only [currentGuardWidth] at hz; omega
      have hzΧ : currentGuardWidth Χ = 0 := by simp only [currentGuardWidth] at hz; omega
      cases he : TransitionForm.normalize? Ψ with
      | none => simp [TransitionForm.normalize?, he] at hn
      | some G =>
          cases hf : TransitionForm.normalize? Χ with
          | none => simp [TransitionForm.normalize?, he, hf] at hn
          | some H =>
              simp [TransitionForm.normalize?, he, hf] at hn
              subst F
              change G.current.guards ∪ H.current.guards = ∅
              rw [ihΨ he hzΨ, ihΧ hf hzΧ, Set.union_self]
  | next Ψ ih =>
      cases he : TransitionForm.normalize? Ψ with
      | none => simp [TransitionForm.normalize?, he] at hn
      | some G =>
          cases hn' : G.nextPart with
          | some N => simp [TransitionForm.normalize?, he, hn'] at hn
          | none =>
              simp [TransitionForm.normalize?, he, hn'] at hn
              subst F
              rfl

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem finite_branch_guardWidth [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
    (hB : B ∈ R.branches) : currentGuardWidth (Judgement.ofFinite B) = 0 := by
  classical
  open STLTableau.ExpansionRule in
    cases hr <;>
      simp only [plainAnd, plainOr, plainUntil, plainRelease, openEventually, openAlways,
        upperAlways, boundedAlways, upperEventually, boundedEventually,
        List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlways_defer, upperAlways_check, boundedAlways_defer,
        boundedAlways_check, boundedAlways_finish, upperEventually_defer,
        upperEventually_check, boundedEventually_defer, boundedEventually_check,
        boundedEventually_finish, STLTableau.Judgement.markedLT_eq_clock,
        STLTableau.Judgement.markedGT_eq_clock, Judgement.ofFinite, currentGuardWidth]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
theorem infinite_branch_guardWidth [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var}
    {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var}
    (hB : B ∈ Bs) : currentGuardWidth (Judgement.ofUnbounded B) = 0 := by
  classical
  open UnboundedClocked in
    cases hr <;>
      simp only [upperAlwaysBranches, boundedAlwaysBranches, upperEventuallyBranches,
        boundedEventuallyBranches, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [upperAlwaysDefer, upperAlwaysCheck, boundedAlwaysDefer, boundedAlwaysCheck,
        alwaysWait, alwaysLast, upperEventuallyDefer, upperEventuallyCheck,
        boundedEventuallyDefer, boundedEventuallyCheck, boundedEventuallyFinish,
        Node.lt, Node.gt, Judgement.ofUnbounded, currentGuardWidth]

theorem mixed_branch_currentGuards_empty [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) : B.current.guards = ∅ := by
  rcases hb with h | h | h
  · obtain ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact normalize_currentGuards_empty _ (F := F) hn (finite_branch_guardWidth hr hm)
  · obtain ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact normalize_currentGuards_empty _ (F := F) hn (infinite_branch_guardWidth hr hm)
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := h
    exact normalize_currentGuards_empty _ (F := F) hn rfl

theorem mixed_branch_card [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) : (statePredicates B.current).card ≤ 2 := by
  rcases hb with h | h | h
  · obtain ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    simpa only [statePredicates, TransitionForm.underReset] using
      (finite_normalized_branch_card hr hm (F := F) hn)
  · obtain ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    simpa only [statePredicates, TransitionForm.underReset] using
      (infinite_normalized_branch_card hr hm (F := F) hn)
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := h
    simpa only [statePredicates, TransitionForm.underReset] using
      (opening_normalized_branch_card c m kind a φ (F := F) hn)

theorem mixed_branch_enclosingClocks [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) : Λ.clocks ⊆ B.current.resets.clocks := by
  rcases hb with h | h | h
  all_goals
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
    exact fun _ hc => (ClockResetSet.clocks_union _ _).symm ▸ Or.inr hc

theorem mixed_branch_free_enclosing_disjoint [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) : Disjoint Λ.clocks B.freeClocks := by
  have hg := mixed_branch_currentGuards_empty hb
  have hr := mixed_branch_enclosingClocks hb
  apply Set.disjoint_left.2
  intro c hc hf
  rcases hf with hf | hf
  · obtain ⟨g, hgm, heq⟩ := hf
    rw [hg] at hgm
    exact hgm
  · exact hf.2 (hr hc)

/-- The finite potential used to construct closures. Two new obligations of
strictly smaller complexity cost less than the obligation they replace. -/
noncomputable def potential {ι : Type*} (complexity : ι → ℕ) (s : Finset ι) : ℕ :=
  ∑ p ∈ s, 3 ^ complexity p

theorem potential_small {ι : Type*} (complexity : ι → ℕ) (s : Finset ι) (n : ℕ)
    (hcard : s.card ≤ 2) (hsmall : ∀ p ∈ s, complexity p < n) :
    potential complexity s < 3 ^ n := by
  classical
  cases n with
  | zero =>
      have he : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro p hp
        exact Nat.not_lt_zero _ (hsmall p hp))
      simp [potential, he]
  | succ n =>
      have hsum : potential complexity s ≤ s.card * 3 ^ n := by
        unfold potential
        calc
          ∑ p ∈ s, 3 ^ complexity p ≤ ∑ _p ∈ s, 3 ^ n :=
            Finset.sum_le_sum (fun p hp => Nat.pow_le_pow_right (by omega) (by
              have := hsmall p hp; omega))
          _ = s.card * 3 ^ n := by simp
      have hp : 0 < 3 ^ n := pow_pos (by omega) _
      rw [pow_succ]
      nlinarith

/-- A purely syntactic strict decrease criterion. Old obligations may also
become closed; at most two strictly smaller new obligations are introduced. -/
theorem potential_decrease {ι : Type*} [DecidableEq ι] (complexity : ι → ℕ)
    (A B N : Finset ι) (p : ι) (hp : p ∈ A)
    (hsubset : B ⊆ A.erase p ∪ N) (hcard : N.card ≤ 2)
    (hsmall : ∀ q ∈ N, complexity q < complexity p) :
    potential complexity B < potential complexity A := by
  classical
  have hbound : potential complexity B ≤
      potential complexity (A.erase p) + potential complexity N := by
    calc
      potential complexity B ≤ potential complexity (A.erase p ∪ N) :=
        Finset.sum_le_sum_of_subset hsubset
      _ ≤ potential complexity (A.erase p) + potential complexity N := by
        have he := Finset.sum_union_inter (s₁ := A.erase p) (s₂ := N) (f := fun q => 3 ^ complexity q)
        unfold potential
        omega
  have hsplit : potential complexity A =
      potential complexity (A.erase p) + 3 ^ complexity p := by
    exact (Finset.sum_erase_add A (fun q => 3 ^ complexity q) hp).symm
  have hn := potential_small complexity N (complexity p) hcard hsmall
  omega

/-- Exactly the current predicates for which no represented rule branch has
yet been included in the working transition. -/
noncomputable def openPredicates (E : ClosureCatalogue Clock Var)
    (Φ : TransitionForm Clock Var) : Finset (Predicate Clock Var) := by
  classical
  exact (statePredicates Φ.current).filter (fun p => ¬ E.RuleClosedFor Φ p)

@[simp] theorem mem_openPredicates (E : ClosureCatalogue Clock Var)
    (Φ : TransitionForm Clock Var) (p : Predicate Clock Var) :
    p ∈ openPredicates E Φ ↔
      Local.predicate p ∈ Φ.current.locals ∧ ¬ E.RuleClosedFor Φ p := by
  classical
  simp [openPredicates]

noncomputable def rank (E : ClosureCatalogue Clock Var) (Φ : TransitionForm Clock Var) : ℕ :=
  potential Predicate.complexity (openPredicates E Φ)

/-- Closing p and introducing at most two smaller obligations strictly
decreases the finite closure potential. -/
theorem rank_decrease [DecidableEq (Predicate Clock Var)] (E : ClosureCatalogue Clock Var) (Φ Ψ : TransitionForm Clock Var)
    (p : Predicate Clock Var) (N : Finset (Predicate Clock Var))
    (hp : Local.predicate p ∈ Φ.current.locals) (hopen : ¬ E.RuleClosedFor Φ p)
    (hnew : openPredicates E Ψ ⊆ (openPredicates E Φ).erase p ∪ N)
    (hcard : N.card ≤ 2) (hsmall : ∀ q ∈ N, q.complexity < p.complexity) :
    rank E Ψ < rank E Φ := by
  classical
  exact potential_decrease Predicate.complexity _ _ N p
    ((mem_openPredicates E Φ p).2 ⟨hp, hopen⟩) hnew hcard hsmall

/-- Replacing the enclosing reset by the target's complete reset keeps a
represented branch subsumed. This is the reset-scope step needed when an
already closed predicate is retained in a larger working transition. -/
theorem underReset_target_subsumed (F Ψ : TransitionForm Clock Var)
    (Λ : ClockResetSet Clock) (h : SyntacticallySubsumed (F.underReset Λ) Ψ) :
    SyntacticallySubsumed (F.underReset Ψ.current.resets) Ψ := by
  have hF : ResetIncluded F.current.resets Ψ.current.resets := by
    intro c a hc
    apply h.current.resets c a
    simp only [TransitionForm.underReset, ClockResetSet.union, hc]
  refine ⟨⟨h.current.guards, ?_, h.current.locals⟩, ?_, h.next⟩
  · intro c a hc
    change (F.current.resets.union Ψ.current.resets).value c = some a at hc
    cases hf : F.current.resets.value c with
    | none => simpa only [ClockResetSet.union, hf] using hc
    | some v =>
        have hva : v = a := Option.some.inj (by
          simpa only [ClockResetSet.union, hf] using hc)
        subst v
        exact hF c a hf
  · apply Set.disjoint_left.2
    intro c hc hd
    apply hd.2
    change c ∈ (F.current.resets.union Ψ.current.resets).clocks
    rw [ClockResetSet.clocks_union]
    exact Or.inr hc

theorem mixed_branch_rebase [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B Ψ : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) (hs : SyntacticallySubsumed B Ψ) :
    ∃ C, ConcreteMixed.catalogue.Branch p Ψ.current.resets C ∧
      SyntacticallySubsumed C Ψ := by
  rcases hb with h | h | h
  · obtain ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact ⟨F.underReset Ψ.current.resets,
      Or.inl ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩,
      underReset_target_subsumed F Ψ Λ hs⟩
  · obtain ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact ⟨F.underReset Ψ.current.resets,
      Or.inr (Or.inl ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩),
      underReset_target_subsumed F Ψ Λ hs⟩
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := h
    exact ⟨F.underReset Ψ.current.resets,
      Or.inr (Or.inr ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩),
      underReset_target_subsumed F Ψ Λ hs⟩

theorem mixed_branch_change_reset [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) (Μ : ClockResetSet Clock) :
    ∃ C, ConcreteMixed.catalogue.Branch p Μ C := by
  rcases hb with h | h | h
  · obtain ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact ⟨F.underReset Μ, Or.inl ⟨p₀, R, raw, F, rfl, hr, hm, hn, rfl⟩⟩
  · obtain ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩ := h
    exact ⟨F.underReset Μ, Or.inr (Or.inl ⟨p₀, Bs, raw, F, rfl, hr, hm, hn, rfl⟩)⟩
  · obtain ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩ := h
    exact ⟨F.underReset Μ, Or.inr (Or.inr ⟨c, m, kind, a, φ, F, rfl, hn, rfl⟩)⟩

theorem mixed_ruleClosed_mono [DecidableEq Clock]
    {Φ Ψ : TransitionForm Clock Var} (hs : SyntacticallySubsumed Φ Ψ)
    (p : Predicate Clock Var) (hc : ConcreteMixed.catalogue.RuleClosedFor Φ p) :
    ConcreteMixed.catalogue.RuleClosedFor Ψ p := by
  rcases hc with hn | ⟨B, hb, hB⟩
  · left
    rintro ⟨C, hC⟩
    exact hn (mixed_branch_change_reset hC Φ.current.resets)
  · right
    exact mixed_branch_rebase hb (hB.trans hs)


end FaithfulClosure
end STLTableau.Section3
