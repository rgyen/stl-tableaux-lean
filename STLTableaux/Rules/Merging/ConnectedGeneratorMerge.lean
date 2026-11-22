import STLTableaux.Syntax.TransitionForms
import STLTableaux.Rules.Merging.ConnectedBoundedMerge

/-! Merge predicates in state forms under the scope conditions of Lemma 3.12.
At touching endpoints, at least one marker must include the endpoint. -/
namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace StateForm

/-- Remove two selected predicates and insert their semantic merge. Every
other local, every guard, and every reset assignment stays fixed. -/
def replacePredicatePair (S : StateForm Clock Var) (p q r : Predicate Clock Var) :
    StateForm Clock Var :=
  { S with
    locals := (S.locals \ {Local.predicate p,Local.predicate q}) ∪ {Local.predicate r}
    locals_finite := (S.locals_finite.subset Set.sdiff_subset).union (Set.finite_singleton _) }

/-- Pair equivalence lifts through the generator's actual reset scope. -/
theorem replacePredicatePair_holds (S : StateForm Clock Var) (p q r : Predicate Clock Var)
    (hp : Local.predicate p ∈ S.locals) (hq : Local.predicate q ∈ S.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (he : ((Local.predicate p).holds σ P (S.resets.apply α) k ∧
      (Local.predicate q).holds σ P (S.resets.apply α) k) ↔
      (Local.predicate r).holds σ P (S.resets.apply α) k) :
    S.holds σ P α k ↔ (S.replacePredicatePair p q r).holds σ P α k := by
  constructor
  · intro hs
    refine ⟨hs.1,?_⟩
    intro l hl
    rcases hl with ⟨hl,_⟩ | hl
    · exact hs.2 l hl
    · have hEq : l = .predicate r := hl
      subst l
      exact he.mp ⟨hs.2 _ hp,hs.2 _ hq⟩
  · intro hs
    have hm := hs.2 (.predicate r) (Or.inr rfl)
    obtain ⟨hpH,hqH⟩ := he.mpr hm
    refine ⟨hs.1,?_⟩
    intro l hl
    by_cases hle : l ∈ ({Local.predicate p,Local.predicate q} : Set (Local Clock Var))
    · rcases hle with hle | hle
      · have heq : l = .predicate p := hle
        simpa only [heq] using hpH
      · have heq : l = .predicate q := hle
        simpa only [heq] using hqH
    · exact hs.2 l (Or.inl ⟨hl,hle⟩)

/-- Direct application of the updated Lemma 3.12 to a real generator's
locals. Comparisons are evaluated after the generator's inherited resets. -/
theorem merge_connected_pair_holds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hq : Local.predicate (.upper c₂ b₂ kind I φ) ∈ S.locals)
    (hjoin : (S.resets.apply α d₁ : ℝ) <[Marker.disj q₁ b₂] (S.resets.apply α c₂ : ℝ))
    (hleft : (S.resets.apply α c₂ : ℝ) <[Marker.imp b₂ b₁] (S.resets.apply α c₁ : ℝ)) :
    S.holds σ P α k ↔
      (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
        (.upper c₂ b₂ kind I φ) (.upper c₁ b₁ kind I φ)).holds σ P α k := by
  apply replacePredicatePair_holds S _ _ _ hp hq σ P α k
  simpa only [Local.holds,Local.toJudgement,Judgement.holds,dif_pos hk] using
    Predicate.predicate_merge_connected σ (P.interval ⟨k.1,hk⟩) (S.resets.apply α)
      c₁ d₁ c₂ b₁ q₁ b₂ kind I φ (P.nonempty _) hjoin hleft

end StateForm

/-- A finite ordered family of scopes in the `↑↓` form followed by one in the
`↑` form. The constructors record the endpoint comparisons for the merge. -/
inductive ConnectedPrefix (β : ClockValuation Clock) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var) (lastClock : Clock) (lastMarker : Marker) :
    List (Predicate Clock Var) → Clock → Marker → Prop
  | nil : ConnectedPrefix β kind I φ lastClock lastMarker [] lastClock lastMarker
  | cons {ps c₂ b₂} (c₁ d₁ : Clock) (b₁ q₁ : Marker)
      (tail : ConnectedPrefix β kind I φ lastClock lastMarker ps c₂ b₂)
      (join : (β d₁ : ℝ) <[Marker.disj q₁ b₂] (β c₂ : ℝ))
      (left : (β c₂ : ℝ) <[Marker.imp b₂ b₁] (β c₁ : ℝ)) :
      ConnectedPrefix β kind I φ lastClock lastMarker
        (.bounded c₁ d₁ b₁ q₁ kind I φ :: ps) c₁ b₁

/-- Arbitrarily many connected `↑↓` pieces and one final `↑` piece
compress into a single `↑` predicate, for finite or infinite timing bounds. -/
theorem ConnectedPrefix.holds_iff
    {β : ClockValuation Clock} {kind : TemporalKind} {I : TimeInterval} {φ : Formula Var}
    {lastClock c : Clock} {lastMarker b : Marker} {ps : List (Predicate Clock Var)}
    (h : ConnectedPrefix β kind I φ lastClock lastMarker ps c b)
    (σ : FiniteSignal Var) (J : MarkedInterval) (hne : J.carrier.Nonempty) :
    ((∀ p ∈ ps, p.holds σ J β) ∧
      Predicate.holds σ J β (.upper lastClock lastMarker kind I φ)) ↔
      Predicate.holds σ J β (.upper c b kind I φ) := by
  induction h with
  | nil => simp
  | @cons ps c₂ b₂ c₁ d₁ b₁ q₁ tail hj hl ih =>
      have hm := Predicate.predicate_merge_connected σ J β
        c₁ d₁ c₂ b₁ q₁ b₂ kind I φ hne hj hl
      constructor
      · rintro ⟨hs,hu⟩
        exact hm.mp ⟨hs _ List.mem_cons_self,
          ih.mp ⟨fun p hp => hs p (List.mem_cons_of_mem _ hp),hu⟩⟩
      · intro hs
        obtain ⟨hh,ht⟩ := hm.mpr hs
        obtain ⟨ht,hu⟩ := ih.mpr ht
        refine ⟨?_,hu⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hh
        · exact ht p hp

end STLTableau.Section3

namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace StateForm

/-- Replace a whole finite selected family, retaining all remaining locals
and the literal original guards and reset assignments. -/
def replacePredicates (S : StateForm Clock Var) (ps : List (Predicate Clock Var))
    (r : Predicate Clock Var) : StateForm Clock Var :=
  { S with
    locals := (S.locals \ {l | ∃ p ∈ ps, l = Local.predicate p}) ∪ {Local.predicate r}
    locals_finite := (S.locals_finite.subset Set.sdiff_subset).union (Set.finite_singleton _) }

theorem replacePredicates_holds (S : StateForm Clock Var) (ps : List (Predicate Clock Var))
    (r : Predicate Clock Var) (hp : ∀ p ∈ ps, Local.predicate p ∈ S.locals)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (he : (∀ p ∈ ps, (Local.predicate p).holds σ P (S.resets.apply α) k) ↔
      (Local.predicate r).holds σ P (S.resets.apply α) k) :
    S.holds σ P α k ↔ (S.replacePredicates ps r).holds σ P α k := by
  constructor
  · intro hs
    refine ⟨hs.1,?_⟩
    intro l hl
    rcases hl with ⟨hl,_⟩ | hl
    · exact hs.2 l hl
    · have heq : l = .predicate r := hl
      subst l
      exact he.mp (fun p hp' => hs.2 _ (hp p hp'))
  · intro hs
    have hpH := he.mpr (hs.2 (.predicate r) (Or.inr rfl))
    refine ⟨hs.1,?_⟩
    intro l hl
    by_cases hx : ∃ p ∈ ps, l = Local.predicate p
    · obtain ⟨p,hp,rfl⟩ := hx
      exact hpH p hp
    · exact hs.2 l (Or.inl ⟨hl,hx⟩)

/-- Merging a connected prefix of predicates preserves satisfaction of the
enclosing state form. -/
theorem merge_connected_prefix_holds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (lastClock c : Clock) (lastMarker b : Marker) (ps : List (Predicate Clock Var))
    (hprefix : ConnectedPrefix (S.resets.apply α) kind I φ lastClock lastMarker ps c b)
    (hp : ∀ p ∈ ps ++ [.upper lastClock lastMarker kind I φ],
      Local.predicate p ∈ S.locals) :
    S.holds σ P α k ↔
      (S.replacePredicates (ps ++ [.upper lastClock lastMarker kind I φ])
        (.upper c b kind I φ)).holds σ P α k := by
  apply replacePredicates_holds S _ _ hp σ P α k
  have he := hprefix.holds_iff σ (P.interval ⟨k.1,hk⟩) (P.nonempty _)
  simp only [Local.holds,Local.toJudgement,Judgement.holds,dif_pos hk]
  constructor
  · intro h
    apply he.mp
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
      h _ (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · intro h
    obtain ⟨hs,hu⟩ := he.mpr h
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hs p hp
    · have heq : p = .upper lastClock lastMarker kind I φ := List.mem_singleton.mp hp
      simpa only [heq] using hu

end StateForm
end STLTableau.Section3

namespace STLTableau.Section3
open scoped STL
variable {Clock Var : Type*}
namespace StateForm

/-- The successor-generator application: two connected frozen scopes may be
replaced by the `↑↓` predicate with their outer endpoints. -/
theorem merge_connected_bounded_pair_holds (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size)
    (c₁ d₁ c₂ d₂ : Clock) (b₁ q₁ b₂ q₂ : Marker) (kind : TemporalKind)
    (I : TimeInterval) (φ : Formula Var)
    (hp : Local.predicate (.bounded c₁ d₁ b₁ q₁ kind I φ) ∈ S.locals)
    (hq : Local.predicate (.bounded c₂ d₂ b₂ q₂ kind I φ) ∈ S.locals)
    (hleft : (S.resets.apply α c₂ : ℝ) <[Marker.imp b₂ b₁] (S.resets.apply α c₁ : ℝ))
    (hjoin : (S.resets.apply α d₁ : ℝ) <[Marker.disj q₁ b₂] (S.resets.apply α c₂ : ℝ))
    (hright : (S.resets.apply α d₂ : ℝ) <[Marker.imp q₁ q₂] (S.resets.apply α d₁ : ℝ)) :
    S.holds σ P α k ↔
      (S.replacePredicatePair (.bounded c₁ d₁ b₁ q₁ kind I φ)
        (.bounded c₂ d₂ b₂ q₂ kind I φ) (.bounded c₁ d₂ b₁ q₂ kind I φ)).holds σ P α k := by
  apply replacePredicatePair_holds S _ _ _ hp hq σ P α k
  simpa only [Local.holds,Local.toJudgement,Judgement.holds,dif_pos hk] using
    Predicate.predicate_merge_bounded_connected σ (P.interval ⟨k.1,hk⟩) (S.resets.apply α)
      c₁ d₁ c₂ d₂ b₁ q₁ b₂ q₂ kind I φ hleft hjoin hright

end StateForm
end STLTableau.Section3
