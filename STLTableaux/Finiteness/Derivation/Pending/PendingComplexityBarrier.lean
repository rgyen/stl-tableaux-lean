import STLTableaux.Finiteness.Derivation.Pending.PendingComplexity

/-! Complexity barrier for new current unclocked temporal predicates. These facts
concern actual raw branch children; old context and boundary fusion are separate. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- An unclocked temporal predicate has rank one above its companion predicate in the `↑` form. -/
theorem plain_timed_above_upper (c : Clock) (m : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (Predicate.upper c m kind I φ).complexity <
      (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity := by
  rw [plain_timed_complexity]
  simp only [Predicate.complexity]
  omega

/-- An unclocked temporal predicate likewise has rank one above its companion predicate in
the `↑↓` form. -/
theorem plain_timed_above_bounded (c d : Clock) (m ℓ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) :
    (Predicate.bounded c d m ℓ kind I φ).complexity <
      (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity := by
  rw [plain_timed_complexity]
  simp only [Predicate.complexity]
  omega

/-- Every actual immediate producer of a current unclocked temporal predicate is
strictly above that demand, and hence above its companion predicate in the `↑` form. -/
theorem RawBranch.plain_timed_producer_above [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hB : RawBranch p B)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Predicate.plain (timedFormula kind I φ) ∈ B.currentPredicates) :
    (Predicate.plain (timedFormula kind I φ) : Predicate Clock Var).complexity < p.complexity ∧
      (Predicate.upper c m kind I φ).complexity < p.complexity := by
  have h := hB.current_smaller _ hq
  exact ⟨h, (plain_timed_above_upper c m kind I φ).trans h⟩

/-- Once selection is at or below an upper demand's rank, an actual raw branch
cannot regenerate the corresponding unclocked predicate among its current children. -/
theorem RawBranch.no_plain_timed_of_le_upper [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hB : RawBranch p B)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hp : p.complexity ≤ (Predicate.upper c m kind I φ).complexity) :
    Predicate.plain (timedFormula kind I φ) ∉ B.currentPredicates := by
  intro hq
  exact (Nat.not_lt_of_ge hp) (hB.plain_timed_producer_above c m kind I φ hq).2


/-- Maximality excludes an old unclocked temporal predicate once the selected source
has reached the rank of its companion predicate in the `↑` form. -/
theorem maximal_no_plain_timed
    (L : List (Local Clock Var)) (p : Predicate Clock Var)
    (hmax : ∀ q, Local.predicate q ∈ L → ¬q.IsAtomic → q.complexity ≤ p.complexity)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hp : p.complexity ≤ (Predicate.upper c m kind I φ).complexity) :
    Local.predicate (Predicate.plain (timedFormula kind I φ)) ∉ L := by
  intro hq
  have hle := (hmax _ hq (plain_timed_nonatomic kind I φ)).trans hp
  exact (Nat.not_lt_of_ge hle) (plain_timed_above_upper c m kind I φ)

/-- Both surviving old locals and actual new current children exclude the plain
companion when a maximal source at or below the upper rank is expanded. -/
theorem maximal_replacement_no_plain_timed [DecidableEq Clock]
    (left right : List (Local Clock Var)) (p : Predicate Clock Var)
    (hmax : ∀ q, Local.predicate q ∈ left ++ Local.predicate p :: right →
      ¬q.IsAtomic → q.complexity ≤ p.complexity)
    {B : MixedJ Clock Var} (hB : RawBranch p B)
    (c : Clock) (m : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hp : p.complexity ≤ (Predicate.upper c m kind I φ).complexity) :
    ¬(Predicate.plain (timedFormula kind I φ) ∈ B.currentPredicates ∨
      Local.predicate (Predicate.plain (timedFormula kind I φ)) ∈ left ++ right) := by
  intro hq
  rcases hq with hnew | hold
  · exact hB.no_plain_timed_of_le_upper c m kind I φ hp hnew
  · apply maximal_no_plain_timed _ p hmax c m kind I φ hp
    simp only [List.mem_append, List.mem_cons] at hold ⊢
    tauto

end STLTableau.Section4.Finiteness
