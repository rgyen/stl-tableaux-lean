import STLTableaux.Finiteness.Derivation.Branches.RawBranchCompleteness
import STLTableaux.Finiteness.Derivation.DerivationNormalization

/-! Termination of selected CURRENT pending obligations. Retained annotations
and next requirements are excluded. This is not a completion-existence theorem. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

/-- Occurrence-sensitive potential; duplicate pending predicates are counted
until an explicit idempotence collection step removes them. -/
noncomputable def pendingWeight : MixedJ Clock Var → ℕ
  | .predicate p => by classical exact if p.IsAtomic then 0 else 3 ^ p.complexity
  | .conj J K => pendingWeight J + pendingWeight K
  | .reset _ J => pendingWeight J
  | _ => 0

theorem pendingWeight_le_width (J : MixedJ Clock Var) (n : ℕ)
    (h : ∀ p ∈ J.currentPredicates, p.complexity ≤ n) :
    pendingWeight J ≤ FaithfulClosure.currentWidth J * 3 ^ n := by
  induction J with
  | predicate p =>
      have hp := h p (by simp [Section3.Judgement.currentPredicates])
      simp only [pendingWeight,FaithfulClosure.currentWidth,one_mul]
      split
      · exact Nat.zero_le _
      · exact Nat.pow_le_pow_right (by omega) hp
  | conj J K ih ig =>
      have hJ := ih (fun p hp => h p (Or.inl hp))
      have hK := ig (fun p hp => h p (Or.inr hp))
      simp only [pendingWeight,FaithfulClosure.currentWidth,Nat.add_mul]
      exact Nat.add_le_add hJ hK
  | reset R J ih => exact ih h
  | next => exact Nat.zero_le _
  | terminal => exact Nat.zero_le _
  | marker => exact Nat.zero_le _
  | clock => exact Nat.zero_le _

theorem pendingWeight_zero_of_no_current (J : MixedJ Clock Var)
    (h : ∀ p, p ∉ J.currentPredicates) : pendingWeight J = 0 := by
  induction J with
  | predicate p => exact False.elim (h p (by simp [Section3.Judgement.currentPredicates]))
  | conj J K ih ig =>
      simp only [pendingWeight,ih (fun p hp => h p (Or.inl hp)),
        ig (fun p hp => h p (Or.inr hp)),zero_add]
  | reset R J ih => exact ih h
  | _ => rfl

theorem pendingWeight_lt_of_width (J : MixedJ Clock Var) (n : ℕ)
    (hw : FaithfulClosure.currentWidth J ≤ 2)
    (hsmall : ∀ p ∈ J.currentPredicates, p.complexity < n) :
    pendingWeight J < 3 ^ n := by
  cases n with
  | zero =>
      have hz := pendingWeight_zero_of_no_current J
        (fun p hp => Nat.not_lt_zero _ (hsmall p hp))
      simp [hz]
  | succ n =>
      have hb := pendingWeight_le_width J n (fun p hp => by have := hsmall p hp; omega)
      have hpow : 0 < 3 ^ n := pow_pos (by omega) _
      rw [pow_succ]
      nlinarith

theorem RawBranch.current_width [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    FaithfulClosure.currentWidth B ≤ 2 := by
  cases h with
  | finite rule member => exact FaithfulClosure.finite_branch_width rule member
  | infinite rule member => exact FaithfulClosure.infinite_branch_width rule member
  | opening c m kind a φ =>
      simp [UnboundedClocked.opening,Judgement.ofUnbounded,FaithfulClosure.currentWidth]

theorem RawBranch.current_smaller [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (q : Predicate Clock Var) (hq : q ∈ B.currentPredicates) : q.complexity < p.complexity := by
  cases h with
  | @finite p₀ R rule B₀ member =>
      obtain ⟨q₀,rfl,hq₀⟩ := (ConcreteFinite.currentPredicates_ofFinite B₀ q).1 hq
      simpa only [ConcreteFinite.complexity_ofFinite,STLTableau.ConcreteRule.source_eq rule] using
        rule.complexityReduced B₀ member q₀ hq₀
  | infinite rule member => exact ConcreteInfinite.raw_reduced rule member q hq
  | opening c m kind a φ =>
      have he : q = .upper c m kind (.unbounded a) φ := by
        simpa [UnboundedClocked.opening,Judgement.ofUnbounded,Section3.Judgement.currentPredicates,
          Predicate.ofUnbounded] using hq
      subst q
      cases kind <;> simp [Predicate.complexity,Predicate.formulaComplexity,
        UnboundedClocked.formula,Formula.always,Formula.eventually]

/-- Every actual ordinary expansion decreases occurrence potential, including
branch duplicates; source annotations retained afterwards are not pending. -/
theorem RawBranch.pendingWeight_lt_source [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    pendingWeight B < pendingWeight (.predicate p) := by
  classical
  rw [pendingWeight,if_neg h.source_nonatomic]
  exact pendingWeight_lt_of_width B p.complexity h.current_width h.current_smaller

theorem RawBranch.pendingWeight_lt_context [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (Γ : MixedJ Clock Var) :
    pendingWeight (.conj B Γ) < pendingWeight (.conj (.predicate p) Γ) :=
  Nat.add_lt_add_right h.pendingWeight_lt_source _

theorem plain_timed_nonatomic (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    ¬ (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).IsAtomic := by
  cases kind <;> simp [Predicate.IsAtomic,timedFormula,Formula.always,Formula.eventually]

theorem plain_timed_complexity (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) :
    (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity =
      Predicate.formulaComplexity φ + 2 := by
  cases kind <;> simp [Predicate.complexity,Predicate.formulaComplexity,timedFormula,
    Formula.always,Formula.eventually]

theorem pendingWeight_boundaryGuard (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    pendingWeight (withBoundaryGuard c b Γ) = pendingWeight Γ := by
  cases b <;> simp [withBoundaryGuard,pendingWeight]

/-- Required merger strictly decreases current pending weight: it removes a
unclocked temporal predicate and replaces its companion predicate in the `↑↓` form by a
predicate in the `↑` form of equal rank. -/
theorem required_boundary_weight_lt (R : ClockResetSet Clock) (c d : Clock)
    (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    pendingWeight (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) <
    pendingWeight (.reset R (.conj
      (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))) := by
  classical
  have hU : pendingWeight (.predicate (.upper c m kind I φ)) =
      3 ^ (Predicate.formulaComplexity φ + 1) := by
    simp [pendingWeight,Predicate.IsAtomic,Predicate.complexity]
  have hB : pendingWeight (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) =
      3 ^ (Predicate.formulaComplexity φ + 1) := by
    simp [pendingWeight,Predicate.IsAtomic,Predicate.complexity]
  have hT : pendingWeight (Clock := Clock) (.predicate (.plain (timedFormula kind I φ))) =
      3 ^ (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity := by
    rw [pendingWeight,if_neg (plain_timed_nonatomic kind I φ)]
  have hpos : 0 < 3 ^ (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity :=
    pow_pos (by omega) _
  change pendingWeight (.predicate (.upper c m kind I φ)) +
    (0 + pendingWeight (withBoundaryGuard c (Marker.imp ℓ m) Γ)) <
    (pendingWeight (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) +
      pendingWeight (.predicate (.plain (timedFormula kind I φ)))) + (0 + pendingWeight Γ)
  rw [hU,hB,hT,pendingWeight_boundaryGuard]
  omega

/-- A standalone optional extension is weight-preserving, including its
strict boundary guard; it is not by itself a termination step. -/
theorem optional_boundary_weight_eq (R : ClockResetSet Clock) (c d : Clock)
    (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (Γ : MixedJ Clock Var) :
    pendingWeight (.conj (.predicate (.upper c m kind I φ))
      (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) =
    pendingWeight (.reset R (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.conj (.marker ℓ) Γ))) := by
  simp [pendingWeight,pendingWeight_boundaryGuard,Predicate.IsAtomic,Predicate.complexity]

/-- Optional bounded-to-upper alone has equal potential. Its immediately
selected actual upper expansion gives strict descent, so it is one induction
step rather than an unjustified standalone decreasing rewrite. -/
theorem optional_upper_expansion_weight_lt [DecidableEq Clock]
    (R : ClockResetSet Clock) (c d : Clock) (m ℓ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (Γ B : MixedJ Clock Var)
    (h : RawBranch (.upper c m kind I φ) B) :
    pendingWeight (.conj B (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) <
    pendingWeight (.reset R (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
      (.conj (.marker ℓ) Γ))) := by
  have hlt := Nat.add_lt_add_right h.pendingWeight_lt_source (pendingWeight Γ)
  simpa [pendingWeight,pendingWeight_boundaryGuard,Predicate.IsAtomic,Predicate.complexity] using hlt

end STLTableau.Section4.Finiteness
