import STLTableaux.Closure.Catalogue.FaithfulAlphaCatalogue
import STLTableaux.Closure.Catalogue.FaithfulContextualFreshBranch
import STLTableaux.Closure.Correctness.FaithfulClosureProgress
import STLTableaux.Closure.Subsumption.FaithfulAlphaSubsumption

/-! Actual raw branch alpha representatives, under a fixed enclosing reset.
The inherited reset is outside the alpha conversion of the raw rule branch. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace FaithfulClosure

theorem predicate_rename_injective (e : Equiv.Perm Clock) :
    Function.Injective (Predicate.rename e : Predicate Clock Var → Predicate Clock Var) := by
  have hinv : ∀ p : Predicate Clock Var, (p.rename e).rename e.symm = p := by
    intro p
    cases p <;> simp [Predicate.rename]
  intro p q hpq
  calc
    p = (p.rename e).rename e.symm := (hinv p).symm
    _ = (q.rename e).rename e.symm := congrArg (Predicate.rename e.symm) hpq
    _ = q := hinv q

theorem statePredicates_rename [DecidableEq (Predicate Clock Var)] (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    statePredicates (S.rename e) = (statePredicates S).image (Predicate.rename e) := by
  classical
  ext p
  simp only [mem_statePredicates, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, he⟩
    cases l with
    | terminal => cases he
    | marker m => cases he
    | predicate q => exact ⟨q, hl, Local.predicate.inj he⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨.predicate q, hq, rfl⟩

theorem alpha_current_card {F G : TransitionForm Clock Var}
    (ha : TransitionForm.AlphaEquivalent F G) :
    (statePredicates F.current).card = (statePredicates G.current).card := by
  classical
  induction ha with
  | refl => rfl
  | outer F e hf =>
      change (statePredicates (F.current.rename e)).card = _
      rw [statePredicates_rename, Finset.card_image_of_injective (statePredicates F.current)
        (predicate_rename_injective (Var := Var) e)]
  | next => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

end FaithfulClosure

namespace ConcreteContextual

/-- The raw represented branch is alpha-converted before applying Λ. -/
def Branch [DecidableEq Clock] (p : Predicate Clock Var) (Λ : ClockResetSet Clock)
    (B : TransitionForm Clock Var) : Prop :=
  ∃ R A, ConcreteMixed.catalogue.Branch p ClockResetSet.empty R ∧
    TransitionForm.AlphaEquivalent A R ∧ B = A.underReset Λ

noncomputable def catalogue [DecidableEq Clock] : ClosureCatalogue Clock Var where
  Admitted := ConcreteMixed.catalogue.Admitted
  Branch := Branch
  branch_exists := by
    intro p hp hn Λ
    obtain ⟨R, hR⟩ := ConcreteMixed.catalogue.branch_exists p hp hn ClockResetSet.empty
    exact ⟨R.underReset Λ, R, R, hR, .refl R, rfl⟩
  branch_reduced := by
    rintro p Λ B ⟨R, A, hR, ha, rfl⟩ q hq
    exact ((ha.current_property (fun q => q.complexity < p.complexity)
      (fun e q => by rw [Predicate.complexity_rename])).2
      (ConcreteMixed.catalogue.branch_reduced hR)) q hq
  branch_sound := by
    rintro p Λ B ⟨R, A, hR, ha, rfl⟩ σ P α k hk hi hs
    have hg : A.current.guards = ∅ :=
      ha.current_guards.trans (FaithfulClosure.mixed_branch_currentGuards_empty hR)
    have hsA := (TransitionForm.underReset_holds A Λ hg σ P α k).1 hs
    have hsR := (ha.holds σ P (Λ.apply α) k).1 hsA
    have hp := ConcreteMixed.catalogue.branch_sound hR σ P (Λ.apply α) k hk
      (by simpa only [ClockResetSet.apply_empty] using hi) hsR
    simpa only [ClockResetSet.apply_empty] using hp

theorem branch_rebase [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B Ψ : TransitionForm Clock Var}
    (hb : catalogue.Branch p Λ B) (hs : SyntacticallySubsumed B Ψ) :
    ∃ C, catalogue.Branch p Ψ.current.resets C ∧ SyntacticallySubsumed C Ψ := by
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  exact ⟨A.underReset Ψ.current.resets, ⟨R, A, hR, ha, rfl⟩,
    FaithfulClosure.underReset_target_subsumed A Ψ Λ hs⟩

theorem branch_change_reset [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p Λ B) (Μ : ClockResetSet Clock) :
    ∃ C, catalogue.Branch p Μ C := by
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  exact ⟨A.underReset Μ, R, A, hR, ha, rfl⟩

theorem ruleClosed_mono [DecidableEq Clock]
    {Φ Ψ : TransitionForm Clock Var} (hs : SyntacticallySubsumed Φ Ψ)
    (p : Predicate Clock Var) (hc : catalogue.RuleClosedFor Φ p) :
    catalogue.RuleClosedFor Ψ p := by
  rcases hc with hn | ⟨B, hb, hB⟩
  · left
    rintro ⟨C, hC⟩
    exact hn (branch_change_reset hC Φ.current.resets)
  · right
    exact branch_rebase hb (hB.trans hs)

theorem branch_card [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p Λ B) : (FaithfulClosure.statePredicates B.current).card ≤ 2 := by
  obtain ⟨R, A, hR, ha, rfl⟩ := hb
  change (FaithfulClosure.statePredicates A.current).card ≤ 2
  rw [FaithfulClosure.alpha_current_card ha]
  exact FaithfulClosure.mixed_branch_card hR

theorem ruleClosed_alphaNext [DecidableEq Clock]
    (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hf : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (p : Predicate Clock Var) (hc : catalogue.RuleClosedFor Φ p) :
    catalogue.RuleClosedFor (Φ.alphaNext e) p := by
  rcases hc with hn | ⟨B, hb, hB⟩
  · exact Or.inl hn
  · obtain ⟨R, A, hR, ha, rfl⟩ := hb
    have hfA : ∀ N, A.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c :=
      hB.next_fix_of_subsumed e hf
    refine Or.inr ⟨(A.alphaNext e).underReset Φ.current.resets, ?_, ?_⟩
    · exact ⟨R, A.alphaNext e, hR, (TransitionForm.AlphaEquivalent.next A e hfA).trans ha, rfl⟩
    · exact hB.alphaNext e hf

theorem ruleClosed_alphaNext_iff [DecidableEq Clock]
    (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hf : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (p : Predicate Clock Var) :
    catalogue.RuleClosedFor (Φ.alphaNext e) p ↔ catalogue.RuleClosedFor Φ p := by
  constructor
  · intro hc
    have hh := ruleClosed_alphaNext (Φ.alphaNext e) e.symm (Φ.alphaNext_fix_inverse e hf) p hc
    simpa only [TransitionForm.alphaNext_inverse] using hh
  · exact ruleClosed_alphaNext Φ e hf p

theorem rank_alphaNext [DecidableEq Clock]
    (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hf : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    FaithfulClosure.rank catalogue (Φ.alphaNext e) = FaithfulClosure.rank catalogue Φ := by
  classical
  unfold FaithfulClosure.rank FaithfulClosure.openPredicates
  congr 1
  apply Finset.filter_congr
  intro p hp
  exact not_congr (ruleClosed_alphaNext_iff Φ e hf p)

/-- A compatible branch closes `p` and can add only the
strictly smaller current predicates present in that branch. -/
theorem union_rank_decrease [DecidableEq Clock]
    (Φ B : TransitionForm Clock Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ Φ.current.locals)
    (hopen : ¬ catalogue.RuleClosedFor Φ p)
    (hb : catalogue.Branch p Φ.current.resets B)
    (hcompat : Φ.UnionCompatible B) :
    FaithfulClosure.rank catalogue (Φ.union B) < FaithfulClosure.rank catalogue Φ := by
  classical
  have hpclosed : catalogue.RuleClosedFor (Φ.union B) p :=
    Or.inr (branch_rebase hb hcompat.right)
  apply FaithfulClosure.rank_decrease catalogue Φ (Φ.union B) p
    (FaithfulClosure.statePredicates B.current) hp hopen
  · intro q hq
    obtain ⟨hql, hqo⟩ := (FaithfulClosure.mem_openPredicates catalogue _ q).1 hq
    rw [Finset.mem_union]
    rcases hql with hqΦ | hqB
    · left
      apply Finset.mem_erase.mpr
      refine ⟨?_, (FaithfulClosure.mem_openPredicates catalogue Φ q).2 ⟨hqΦ, ?_⟩⟩
      · intro heq
        subst q
        exact hqo hpclosed
      · intro hclosed
        exact hqo (ruleClosed_mono hcompat.left q hclosed)
    · right
      exact (FaithfulClosure.mem_statePredicates B.current q).2 hqB
  · exact branch_card hb
  · intro q hq
    exact catalogue.branch_reduced hb q
      ((FaithfulClosure.mem_statePredicates B.current q).1 hq)

end ConcreteContextual
end STLTableau.Section3
