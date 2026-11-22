import STLTableaux.Finiteness.Inventory.TemporalFamilyInventory
import STLTableaux.Finiteness.Bounds.FullStateClockSupport

/-! Finite signature inventories bound temporal endpoint clocks. Guards and
reset clocks are deliberately excluded; no root confinement is assumed here. -/
namespace STLTableau.Section4.Finiteness.TemporalLocalClockBudget
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

/-- A common local-valued family for finite/infinite F/G bounded labels. -/
def boundedLocals (S : Section3.StateForm Clock Var) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) : Set (Local Clock Var) :=
  {l | l ∈ S.locals ∧ ∃ c d b q, l = .predicate (.bounded c d b q kind I φ)}

omit [DecidableEq Clock] in
theorem boundedLocals_finite (S : Section3.StateForm Clock Var) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) : (boundedLocals S kind I φ).Finite :=
  S.locals_finite.subset (fun _ h => h.1)

omit [DecidableEq Clock] in
theorem boundedLocals_eventual_image (S : Section3.StateForm Clock Var)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    boundedLocals S .eventually (.bounded I) φ =
      Local.predicate '' boundedEventualParents S I φ := by
  ext l
  constructor
  · rintro ⟨hl, c, d, b, q, rfl⟩
    exact ⟨_, ⟨hl, c, d, b, q, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hp, c, d, b, q, rfl⟩, rfl⟩
    exact ⟨hp, c, d, b, q, rfl⟩

omit [DecidableEq Clock] in
theorem boundedLocals_always_image (S : Section3.StateForm Clock Var)
    (I : TimeInterval) (φ : Formula Var) :
    boundedLocals S .always I φ = Local.predicate '' boundedAlwaysParents S I φ := by
  ext l
  constructor
  · rintro ⟨hl, c, d, b, q, rfl⟩
    exact ⟨_, ⟨hl, c, d, b, q, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨hp, c, d, b, q, rfl⟩, rfl⟩
    exact ⟨hp, c, d, b, q, rfl⟩

omit [DecidableEq Clock] in
theorem boundedLocals_eventual_ncard (S : Section3.StateForm Clock Var)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    (boundedLocals S .eventually (.bounded I) φ).ncard = (boundedEventualParents S I φ).ncard := by
  rw [boundedLocals_eventual_image]
  exact Set.ncard_image_of_injective _ (fun _ _ h => Local.predicate.inj h)

omit [DecidableEq Clock] in
theorem boundedLocals_always_ncard (S : Section3.StateForm Clock Var)
    (I : TimeInterval) (φ : Formula Var) :
    (boundedLocals S .always I φ).ncard = (boundedAlwaysParents S I φ).ncard := by
  rw [boundedLocals_always_image]
  exact Set.ncard_image_of_injective _ (fun _ _ h => Local.predicate.inj h)

omit [DecidableEq Clock] in
theorem boundedLocals_unbounded_eventual_eq (S : Section3.StateForm Clock Var)
    (a : NNReal) (φ : Formula Var) :
    boundedLocals S .eventually (.unbounded a) φ = unboundedEventualLocals S a φ := by
  rfl

noncomputable def upperClocks (S : Section3.StateForm Clock Var)
    (s : TemporalKind × TimeInterval × Formula Var) :
    Finset Clock := (upperLocals_finite S s.1 s.2.1 s.2.2).toFinset.biUnion localClockNames

noncomputable def boundedClocks (S : Section3.StateForm Clock Var)
    (s : TemporalKind × TimeInterval × Formula Var) : Finset Clock :=
  (boundedLocals_finite S s.1 s.2.1 s.2.2).toFinset.biUnion localClockNames

theorem upperClocks_card_le (S : Section3.StateForm Clock Var)
    (s : TemporalKind × TimeInterval × Formula Var) :
    (upperClocks S s).card ≤ (upperLocals S s.1 s.2.1 s.2.2).ncard := by
  classical
  calc
    _ ≤ ∑ l ∈ (upperLocals_finite S s.1 s.2.1 s.2.2).toFinset,
        (localClockNames l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ (upperLocals_finite S s.1 s.2.1 s.2.2).toFinset, 1 := by
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨_, c, b, rfl⟩ := (upperLocals_finite S s.1 s.2.1 s.2.2).mem_toFinset.mp hl
      simp [localClockNames]
    _ = _ := by
      rw [Set.ncard_eq_toFinset_card _ (upperLocals_finite S s.1 s.2.1 s.2.2)]
      simp

theorem boundedClocks_card_le (S : Section3.StateForm Clock Var)
    (s : TemporalKind × TimeInterval × Formula Var) :
    (boundedClocks S s).card ≤ 2 * (boundedLocals S s.1 s.2.1 s.2.2).ncard := by
  classical
  calc
    _ ≤ ∑ l ∈ (boundedLocals_finite S s.1 s.2.1 s.2.2).toFinset,
        (localClockNames l).card := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ (boundedLocals_finite S s.1 s.2.1 s.2.2).toFinset, 2 :=
      Finset.sum_le_sum (fun l _ => localClockNames_card_le l)
    _ = _ := by
      rw [Set.ncard_eq_toFinset_card _ (boundedLocals_finite S s.1 s.2.1 s.2.2)]
      simp [Nat.mul_comm]

/-- Signature confinement and family caps give an endpoint-clock bound.
formulas of unclocked predicates and markers contribute no clocks, independently of their count. -/
theorem stateLocalClockNames_card_le_sum (S : Section3.StateForm Clock Var)
    (Ω : Finset (TemporalKind × TimeInterval × Formula Var))
    (upperCap boundedCap : (TemporalKind × TimeInterval × Formula Var) → ℕ)
    (hupper : ∀ c b kind I φ, Local.predicate (.upper c b kind I φ) ∈ S.locals →
      (kind, I, φ) ∈ Ω)
    (hbounded : ∀ c d b q kind I φ, Local.predicate (.bounded c d b q kind I φ) ∈ S.locals →
      (kind, I, φ) ∈ Ω)
    (hu : ∀ s ∈ Ω, (upperLocals S s.1 s.2.1 s.2.2).ncard ≤ upperCap s)
    (hb : ∀ s ∈ Ω, (boundedLocals S s.1 s.2.1 s.2.2).ncard ≤ boundedCap s) :
    (stateLocalClockNames S).card ≤ ∑ s ∈ Ω, (upperCap s + 2 * boundedCap s) := by
  classical
  have hsub : stateLocalClockNames S ⊆
      Ω.biUnion (fun s => upperClocks S s ∪ boundedClocks S s) := by
    intro c hc
    obtain ⟨l, hl, hc⟩ := Finset.mem_biUnion.mp hc
    have hlS := S.locals_finite.mem_toFinset.mp hl
    cases l with
    | terminal => simp [localClockNames] at hc
    | marker m => simp [localClockNames] at hc
    | predicate p =>
      cases p with
      | plain φ => simp [localClockNames] at hc
      | upper d b kind I φ =>
        apply Finset.mem_biUnion.mpr
        refine ⟨(kind, I, φ), hupper d b kind I φ hlS, Finset.mem_union_left _ ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨_, (upperLocals_finite S kind I φ).mem_toFinset.mpr ⟨hlS, d, b, rfl⟩, hc⟩
      | bounded d e b q kind I φ =>
        apply Finset.mem_biUnion.mpr
        refine ⟨(kind, I, φ), hbounded d e b q kind I φ hlS, Finset.mem_union_right _ ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨_, (boundedLocals_finite S kind I φ).mem_toFinset.mpr ⟨hlS, d, e, b, q, rfl⟩, hc⟩
  calc
    _ ≤ (Ω.biUnion (fun s => upperClocks S s ∪ boundedClocks S s)).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Ω, (upperClocks S s ∪ boundedClocks S s).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Ω, (upperCap s + 2 * boundedCap s) := by
      apply Finset.sum_le_sum
      intro s hs
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ((upperClocks_card_le S s).trans (hu s hs))
          ((boundedClocks_card_le S s).trans (Nat.mul_le_mul_left 2 (hb s hs))))

end STLTableau.Section4.Finiteness.TemporalLocalClockBudget
