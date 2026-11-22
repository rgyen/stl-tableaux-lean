import STLTableaux.Finiteness.Derivation.Merging.AlwaysCheckingMerge
import STLTableaux.Syntax.FaithfulNormalizedSyntax

namespace STLTableau.Section4.Finiteness.DirectTracking.Checks
open scoped STL

private def interval23 : BoundedTimeInterval := ⟨2, 3, by norm_num, by norm_num⟩
private def piece : MarkedInterval := ⟨1, 2, ●, ●⟩
private noncomputable def ages : ClockValuation Nat
  | 0 => 1
  | 1 => 9 / 10
  | 2 => 1 / 2
  | _ => 2 / 5

/-- The predicate scopes are separated, while their checking intervals are connected. -/
theorem positive_lower_checks_merge :
    ¬ ((ages 1 : ℝ) <[Marker.disj ● ●] (ages 2 : ℝ)) ∧
    (checking piece ages 0 1 ● ● interval23).carrier ∪
        (checking piece ages 2 3 ● ● interval23).carrier =
      (checking piece ages 0 3 ● ● interval23).carrier := by
  constructor
  · norm_num [ages, MarkedLT, Marker.disj, Marker.Includes]
  · apply checking_union
    all_goals norm_num [ages, interval23, MarkedLT, Marker.imp, Marker.disj,
      Marker.Includes]

/-- A both-open touching cut leaves a real hole in the proposed hull. -/
theorem open_touch_has_hole :
    (1 : ℝ) ∉ (⟨0, 1, ●, ○⟩ : MarkedInterval).carrier ∪
      (⟨1, 2, ○, ●⟩ : MarkedInterval).carrier ∧
    (1 : ℝ) ∈ (⟨0, 2, ●, ●⟩ : MarkedInterval).carrier := by
  norm_num [MarkedInterval.carrier, MarkedInterval.mem_iff, Marker.Includes]

theorem open_touch_not_hull :
    (⟨0, 1, ●, ○⟩ : MarkedInterval).carrier ∪
      (⟨1, 2, ○, ●⟩ : MarkedInterval).carrier ≠
    (⟨0, 2, ●, ●⟩ : MarkedInterval).carrier := by
  intro h
  exact open_touch_has_hole.1 (h.symm ▸ open_touch_has_hole.2)

/-- One closed endpoint suffices at the touching cut. -/
theorem one_closed_touch_merges :
    (⟨0, 1, ●, ○⟩ : MarkedInterval).carrier ∪
      (⟨1, 2, ●, ●⟩ : MarkedInterval).carrier =
    (⟨0, 2, ●, ●⟩ : MarkedInterval).carrier := by
  apply MarkedInterval.carrier_union_connected
  all_goals norm_num [Marker.Includes]

/-- Semantic comparisons allow retaining one clock twice; Ready rejects it. -/
theorem semantic_conditions_do_not_imply_freshness (φ : Formula Nat) :
    let α : ClockValuation Nat := fun _ => 1
    ((α 0 : ℝ) <[Marker.imp ● ●] (α 0 : ℝ)) ∧
    ((α 0 : ℝ) - (α 0 : ℝ) <[Marker.disj ● ●]
      (interval23.upper - interval23.lower)) ∧
    ((α 0 : ℝ) <[Marker.imp ● ●] (α 0 : ℝ)) ∧
    ¬ Section3.Predicate.Ready (.bounded 0 0 ● ● .always (.bounded interval23) φ) := by
  norm_num [interval23, MarkedLT, Marker.imp, Marker.disj, Marker.Includes,
    Section3.Predicate.Ready]

#check positive_lower_checks_merge
#check open_touch_has_hole
#check open_touch_not_hull
#check one_closed_touch_merges
#check semantic_conditions_do_not_imply_freshness
#print axioms positive_lower_checks_merge
#print axioms open_touch_has_hole
#print axioms open_touch_not_hull
#print axioms one_closed_touch_merges
#print axioms semantic_conditions_do_not_imply_freshness
end STLTableau.Section4.Finiteness.DirectTracking.Checks
