import STLTableaux.Finiteness.Derivation.Derivation
import STLTableaux.Closure.Normalization.FaithfulAlphaNormalization

/-! Global permutations of the actual raw mixed syntax. These structural
lemmas do not allocate a finite clock pool or assert a path bound. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def renameJudgement (e : Equiv.Perm Clock) : MixedJ Clock Var → MixedJ Clock Var
  | .terminal => .terminal
  | .marker m => .marker m
  | .clock c op a => .clock (e c) op a
  | .predicate p => .predicate (p.rename e)
  | .next J => .next (renameJudgement e J)
  | .reset R J => .reset (R.rename e) (renameJudgement e J)
  | .conj J K => .conj (renameJudgement e J) (renameJudgement e K)

@[simp] theorem syntaxClocks_renameJudgement (e : Equiv.Perm Clock) (J : MixedJ Clock Var) :
    syntaxClocks (renameJudgement e J) = e '' syntaxClocks J := by
  induction J with
  | predicate p => cases p <;> simp [renameJudgement, Predicate.rename, syntaxClocks,
      Set.image_insert_eq, Set.image_singleton]
  | reset R J ih => simp [renameJudgement, syntaxClocks, ih, Set.image_union]
  | conj J K ih ik => simp [renameJudgement, syntaxClocks, ih, ik, Set.image_union]
  | next J ih => exact ih
  | terminal => simp [renameJudgement, syntaxClocks]
  | marker => simp [renameJudgement, syntaxClocks]
  | clock => simp [renameJudgement, syntaxClocks]

@[simp] theorem resetNames_renameJudgement (e : Equiv.Perm Clock) (J : MixedJ Clock Var) :
    resetNames (renameJudgement e J) = e '' resetNames J := by
  induction J <;> simp [renameJudgement, resetNames, *, Set.image_union]

@[simp] theorem freeClocks_renameJudgement (e : Equiv.Perm Clock) (J : MixedJ Clock Var) :
    (renameJudgement e J).freeClocks = e '' J.freeClocks := by
  induction J with
  | predicate p => cases p <;> simp [renameJudgement, Predicate.rename, Section3.Judgement.freeClocks,
      Set.image_insert_eq, Set.image_singleton]
  | reset R J ih => simp [renameJudgement, Section3.Judgement.freeClocks, ih, Set.image_sdiff e.injective]
  | conj J K ih ik => simp [renameJudgement, Section3.Judgement.freeClocks, ih, ik, Set.image_union]
  | next J ih => exact ih
  | terminal => simp [renameJudgement, Section3.Judgement.freeClocks]
  | marker => simp [renameJudgement, Section3.Judgement.freeClocks]
  | clock => simp [renameJudgement, Section3.Judgement.freeClocks]

private theorem image_disjoint (e : Equiv.Perm Clock) {S T : Set Clock}
    (h : Disjoint S T) : Disjoint (e '' S) (e '' T) := by
  apply Set.disjoint_left.2
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
  exact Set.disjoint_left.1 h hs (e.injective he ▸ ht)

theorem FreshFor.rename (e : Equiv.Perm Clock) {p : Predicate Clock Var} {B Γ : MixedJ Clock Var}
    (h : FreshFor p B Γ) :
    FreshFor (p.rename e) (renameJudgement e B) (renameJudgement e Γ) := by
  change Disjoint (resetNames (renameJudgement e B) \
    syntaxClocks (renameJudgement e (.predicate p)))
    (syntaxClocks (renameJudgement e Γ) ∪ syntaxClocks (renameJudgement e (.predicate p)))
  simp only [resetNames_renameJudgement, syntaxClocks_renameJudgement,
    ← Set.image_sdiff e.injective, ← Set.image_union]
  exact image_disjoint e h

theorem FreshWithoutContext.rename (e : Equiv.Perm Clock) {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (h : FreshWithoutContext p B) :
    FreshWithoutContext (p.rename e) (renameJudgement e B) := by
  change Disjoint (resetNames (renameJudgement e B) \
    syntaxClocks (renameJudgement e (.predicate p)))
    (syntaxClocks (renameJudgement e (.predicate p)))
  simp only [resetNames_renameJudgement, syntaxClocks_renameJudgement,
    ← Set.image_sdiff e.injective]
  exact image_disjoint e h

private theorem reset_rename_union (e : Equiv.Perm Clock) (R S : ClockResetSet Clock) :
    (R.union S).rename e = (R.rename e).union (S.rename e) := rfl

theorem ACIdem.rename (e : Equiv.Perm Clock) {J K : MixedJ Clock Var} (h : ACIdem J K) :
    ACIdem (renameJudgement e J) (renameJudgement e K) := by
  induction h with
  | refl J => exact .refl _
  | symm h ih => exact .symm ih
  | trans h g ih ig => exact .trans ih ig
  | assoc J K L => exact .assoc _ _ _
  | comm J K => exact .comm _ _
  | idem J => exact .idem _
  | conj h g ih ig => exact .conj ih ig
  | reset R h ih => exact .reset _ ih
  | resetDistrib R J K => exact .resetDistrib _ _ _
  | resetUnused R J hd =>
      apply ACIdem.resetUnused
      rw [ClockResetSet.clocks_rename, freeClocks_renameJudgement]
      exact image_disjoint e hd
  | resetNested R S J =>
      simpa only [renameJudgement, reset_rename_union] using
        (ACIdem.resetNested (R.rename e) (S.rename e) (renameJudgement e J))


@[simp] theorem reset_rename_singleton [DecidableEq Clock] (e : Equiv.Perm Clock) (c : Clock) (v : NNReal) :
    (ClockResetSet.singleton c v).rename e = ClockResetSet.singleton (e c) v := by
  have extR : ∀ (A B : ClockResetSet Clock), A.value = B.value → A = B := by
    intro A B h; cases A; cases B; cases h; rfl
  apply extR
  funext d
  simp only [ClockResetSet.rename, ClockResetSet.singleton]
  have he : e.symm d = c ↔ d = e c := by
    constructor
    · intro h; simpa using congrArg e h
    · intro h; subst d; exact e.symm_apply_apply c
  simp only [he]

private theorem rename_ofFinite (e : Equiv.Perm Clock) (J : STLTableau.Judgement Clock Var) :
    renameJudgement e (Judgement.ofFinite J) = Judgement.ofFinite (J.rename e) := by
  induction J with
  | predicate p => cases p <;> rfl
  | next J ih => exact congrArg Section3.Judgement.next ih
  | reset R J ih => exact congrArg (Section3.Judgement.reset (R.rename e)) ih
  | conj J K ih ik => exact congrArg₂ Section3.Judgement.conj ih ik
  | terminal => rfl
  | clock => rfl
  | leftMarker => rfl

private def renameUnboundedPredicate (e : Equiv.Perm Clock) :
    UnboundedClocked.Predicate Clock Var → UnboundedClocked.Predicate Clock Var
  | .upper c b k a φ => .upper (e c) b k a φ
  | .bounded c d b q k a φ => .bounded (e c) (e d) b q k a φ

private def renameUnbounded (e : Equiv.Perm Clock) :
    UnboundedClocked.Node Clock Var → UnboundedClocked.Node Clock Var
  | .terminal => .terminal
  | .clock c op v => .clock (e c) op v
  | .marker m => .marker m
  | .plain φ => .plain φ
  | .predicate p => .predicate (renameUnboundedPredicate e p)
  | .next J => .next (renameUnbounded e J)
  | .reset R J => .reset (R.rename e) (renameUnbounded e J)
  | .conj J K => .conj (renameUnbounded e J) (renameUnbounded e K)

private theorem rename_ofUnbounded (e : Equiv.Perm Clock) (J : UnboundedClocked.Node Clock Var) :
    renameJudgement e (Judgement.ofUnbounded J) = Judgement.ofUnbounded (renameUnbounded e J) := by
  induction J with
  | predicate p => cases p <;> rfl
  | next J ih => exact congrArg Section3.Judgement.next ih
  | reset R J ih => exact congrArg (Section3.Judgement.reset (R.rename e)) ih
  | conj J K ih ik => exact congrArg₂ Section3.Judgement.conj ih ik
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | plain => rfl

/-- Renaming the rule's clocks maps the whole ordered list of finite branches. -/
private theorem rename_finite_rule [DecidableEq Clock] (e : Equiv.Perm Clock)
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) :
    ∃ R' : ExpansionRule Clock Var, STLTableau.ConcreteRule (p.rename e) R' ∧
      R'.branches = R.branches.map (STLTableau.Judgement.rename e) := by
  cases hr with
  | plainAnd φ ψ => exact ⟨_, .plainAnd φ ψ, rfl⟩
  | plainOr φ ψ => exact ⟨_, .plainOr φ ψ, rfl⟩
  | plainUntil φ ψ => exact ⟨_, .plainUntil φ ψ, rfl⟩
  | plainRelease φ ψ => exact ⟨_, .plainRelease φ ψ, rfl⟩
  | openEventually c I φ =>
      refine ⟨_, .openEventually (e c) I φ, ?_⟩
      simp [ExpansionRule.openEventually, STLTableau.Judgement.rename, IntervalPredicate.rename]
  | openAlways c I φ =>
      refine ⟨_, .openAlways (e c) I φ, ?_⟩
      simp [ExpansionRule.openAlways, STLTableau.Judgement.rename, IntervalPredicate.rename]
  | upperAlways c d b I φ hcd =>
      refine ⟨_, .upperAlways (e c) (e d) b I φ (e.injective.ne hcd), ?_⟩
      simp [ExpansionRule.upperAlways, ExpansionRule.upperAlways_defer,
        ExpansionRule.upperAlways_check, STLTableau.Judgement.rename, IntervalPredicate.rename,
        STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock,
        reset_rename_union]
  | boundedAlways c d b q I φ hcd =>
      refine ⟨_, .boundedAlways (e c) (e d) b q I φ (e.injective.ne hcd), ?_⟩
      simp [ExpansionRule.boundedAlways, ExpansionRule.boundedAlways_defer,
        ExpansionRule.boundedAlways_check, ExpansionRule.boundedAlways_finish,
        STLTableau.Judgement.rename, IntervalPredicate.rename,
        STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock]
  | upperEventually c d b I φ hcd =>
      refine ⟨_, .upperEventually (e c) (e d) b I φ (e.injective.ne hcd), ?_⟩
      by_cases hz : I.lower = 0 <;>
        simp [ExpansionRule.upperEventually, ExpansionRule.upperEventually_defer,
          ExpansionRule.upperEventually_check, hz, STLTableau.Judgement.rename,
          IntervalPredicate.rename, STLTableau.Judgement.markedLT_eq_clock,
          STLTableau.Judgement.markedGT_eq_clock, reset_rename_union]
  | boundedEventually c d b q I φ hcd =>
      refine ⟨_, .boundedEventually (e c) (e d) b q I φ (e.injective.ne hcd), ?_⟩
      simp [ExpansionRule.boundedEventually, ExpansionRule.boundedEventually_defer,
        ExpansionRule.boundedEventually_check, ExpansionRule.boundedEventually_finish,
        STLTableau.Judgement.rename, IntervalPredicate.rename,
        STLTableau.Judgement.markedLT_eq_clock, STLTableau.Judgement.markedGT_eq_clock]

open UnboundedClocked in
/-- The corresponding list map preserves the unbounded rule relation. -/
private theorem rename_unbounded_rule [DecidableEq Clock] (e : Equiv.Perm Clock)
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) :
    UnboundedClocked.ConcreteRule (renameUnboundedPredicate e p) (Bs.map (renameUnbounded e)) := by
  cases hr with
  | upperAlways c d b a φ hcd =>
      simpa [upperAlwaysBranches, upperAlwaysDefer, upperAlwaysCheck, alwaysWait, alwaysLast,
        renameUnbounded, renameUnboundedPredicate, Node.lt, Node.gt, reset_rename_union] using
        UnboundedClocked.ConcreteRule.upperAlways (e c) (e d) b a φ (e.injective.ne hcd)
  | boundedAlways c d b q a φ hcd =>
      simpa [boundedAlwaysBranches, boundedAlwaysDefer, boundedAlwaysCheck, alwaysWait, alwaysLast,
        renameUnbounded, renameUnboundedPredicate, Node.lt, Node.gt] using
        UnboundedClocked.ConcreteRule.boundedAlways (e c) (e d) b q a φ (e.injective.ne hcd)
  | upperEventually c d b a φ hcd =>
      by_cases hz : a = 0 <;>
        simpa [upperEventuallyBranches, upperEventuallyDefer, upperEventuallyCheck, hz,
          renameUnbounded, renameUnboundedPredicate, Node.gt, reset_rename_union] using
          UnboundedClocked.ConcreteRule.upperEventually (e c) (e d) b a φ (e.injective.ne hcd)
  | boundedEventually c d b q a φ hcd =>
      simpa [boundedEventuallyBranches, boundedEventuallyDefer, boundedEventuallyCheck,
        boundedEventuallyFinish, renameUnbounded, renameUnboundedPredicate, Node.lt, Node.gt] using
        UnboundedClocked.ConcreteRule.boundedEventually (e c) (e d) b q a φ (e.injective.ne hcd)

private theorem rename_ofFinite_predicate (e : Equiv.Perm Clock) (p : IntervalPredicate Clock Var) :
    (Predicate.ofFinite p).rename e = Predicate.ofFinite (p.rename e) := by
  cases p <;> rfl

private theorem rename_ofUnbounded_predicate (e : Equiv.Perm Clock)
    (p : UnboundedClocked.Predicate Clock Var) :
    (Predicate.ofUnbounded p).rename e = Predicate.ofUnbounded (renameUnboundedPredicate e p) := by
  cases p <;> rfl

theorem RawBranch.rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    RawBranch (p.rename e) (renameJudgement e B) := by
  cases h with
  | finite hr hm =>
      obtain ⟨R', hr', hbranches⟩ := rename_finite_rule e hr
      rw [rename_ofFinite_predicate, rename_ofFinite]
      apply RawBranch.finite hr'
      rw [hbranches]
      exact List.mem_map_of_mem hm
  | infinite hr hm =>
      rw [rename_ofUnbounded_predicate, rename_ofUnbounded]
      exact RawBranch.infinite (rename_unbounded_rule e hr) (List.mem_map_of_mem hm)
  | opening c m kind a φ =>
      simpa [renameJudgement,Predicate.rename,Section3.Judgement.ofUnbounded,
        UnboundedClocked.opening,Predicate.ofUnbounded] using
        (RawBranch.opening (e c) m kind a φ)


theorem Conjunct.rename (e : Equiv.Perm Clock) {J K : MixedJ Clock Var} (h : Conjunct J K) :
    Conjunct (renameJudgement e J) (renameJudgement e K) := by
  induction h with
  | here J => exact .here _
  | left h ih => exact .left ih
  | right h ih => exact .right ih

theorem FrozenOccurrence.rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {N : MixedJ Clock Var} {c d : Clock} {m ℓ : Marker} {kind : TemporalKind}
    {I : TimeInterval} {φ : Formula Var} (h : FrozenOccurrence N c d m ℓ kind I φ) :
    FrozenOccurrence (renameJudgement e N) (e c) (e d) m ℓ kind I φ := by
  cases h with
  | defer h =>
      apply FrozenOccurrence.defer
      simpa only [renameJudgement,Predicate.rename,reset_rename_singleton] using h.rename e
  | check h =>
      apply FrozenOccurrence.check
      simpa only [renameJudgement,Predicate.rename,reset_rename_union,reset_rename_singleton] using h.rename e

def FrozenByUpper.rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {c d : Clock} {m ℓ : Marker} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    (h : FrozenByUpper c d m ℓ kind I φ) : FrozenByUpper (e c) (e d) m ℓ kind I φ where
  distinct := fun he => h.distinct (e.injective he)
  sourceMarker := h.sourceMarker
  branch := renameJudgement e h.branch
  nextBody := renameJudgement e h.nextBody
  actual := h.actual.rename e
  nextOccurrence := h.nextOccurrence.rename e
  frozenOccurrence := h.frozenOccurrence.rename e

private theorem atomic_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).IsAtomic ↔ p.IsAtomic := by
  cases p <;> rfl

private theorem ResolutionLeaf.rename (e : Equiv.Perm Clock) {J : MixedJ Clock Var}
    (h : ResolutionLeaf J) : ResolutionLeaf (renameJudgement e J) := by
  cases h with
  | terminal => exact .terminal
  | clock c r a => exact .clock (e c) r a
  | marker m => exact .marker m
  | atomic p hp => exact .atomic _ ((atomic_rename e p).2 hp)
  | next J => exact .next _

private theorem rename_boundaryGuard (e : Equiv.Perm Clock) (c : Clock) (b : Marker)
    (Γ : MixedJ Clock Var) : renameJudgement e (withBoundaryGuard c b Γ) =
      withBoundaryGuard (e c) b (renameJudgement e Γ) := by
  cases b <;> rfl

private theorem rename_nonmem (e : Equiv.Perm Clock) {d : Clock} {J : MixedJ Clock Var}
    (h : d ∉ J.freeClocks) : e d ∉ (renameJudgement e J).freeClocks := by
  rw [freeClocks_renameJudgement]
  rintro ⟨c,hc,he⟩
  exact h (e.injective he ▸ hc)

/-- Both the full retained output and erased output are transported literally. -/
noncomputable def Resolve.rename [DecidableEq Clock] (e : Equiv.Perm Clock)
    {J H A : MixedJ Clock Var} (D : Resolve J H A) :
    Resolve (renameJudgement e J) (renameJudgement e H) (renameJudgement e A) := by
  induction D with
  | leaf h => exact .leaf (h.rename e)
  | conj D E ih ik => exact .conj ih ik
  | reset R D ih => exact .reset _ ih
  | structural h D ih => exact .structural (h.rename e) ih
  | expandCtx h hn hf D ih =>
      exact .expandCtx (h.rename e) (fun ha => hn ((atomic_rename e _).1 ha)) (hf.rename e) ih
  | expandSolo h hn hf D ih =>
      exact .expandSolo (h.rename e) (fun ha => hn ((atomic_rename e _).1 ha)) (hf.rename e) ih
  | boundaryRequired h hd D ih =>
      simp only [renameJudgement,Predicate.rename,reset_rename_singleton,rename_boundaryGuard] at ih ⊢
      exact .boundaryRequired (h.rename e) (rename_nonmem e hd) ih
  | boundaryOptional h hd D ih =>
      simp only [renameJudgement,Predicate.rename,reset_rename_singleton,rename_boundaryGuard] at ih ⊢
      exact .boundaryOptional (h.rename e) (rename_nonmem e hd) ih
  | unusedReset d v hj hh D ih =>
      simpa only [renameJudgement,reset_rename_singleton] using
        (Resolve.unusedReset (e d) v (rename_nonmem e hj) (rename_nonmem e hh) ih)

end STLTableau.Section4.Finiteness
