import STLTableaux.Semantics.IntervalSemantics

/-! Section 3: interval-predicate properties under the untruncated interval semantics. -/
namespace STLTableau
open scoped STL
open STLTableau.IntervalPredicate
variable {Clock Var : Type*}

/-- The common temporal interpretation makes the scope dependence explicit. -/
def temporalSatisfies (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (S : Scope) : Prop :=
  match kind with
  | .always => ∀ t : σ.Time, t.1 ∈ alwaysRegion S I → (σ, t) ⊨ φ
  | .eventually => ∀ t : ℝ, t ∈ S →
      ∃ u : σ.Time, u.1 ∈ (I : TimeInterval).translate t ∧ (σ, u) ⊨ φ

@[simp] theorem upper_temporal (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (b : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    predicateSatisfies σ J α (.upper c b kind I φ) ↔
      temporalSatisfies σ kind I φ (scope J α (.upper c b kind I φ)) := by
  cases kind <;> rfl

@[simp] theorem bounded_temporal (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) :
    predicateSatisfies σ J α (.bounded c d b q kind I φ) ↔
      temporalSatisfies σ kind I φ (scope J α (.bounded c d b q kind I φ)) := by
  cases kind <;> rfl

/-- No suffix is present: equal endpoint quadruples give identical meanings
regardless of the intervals on which the predicates are declared. -/
theorem temporal_congr (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) {S T : Scope} (h : S = T) :
    temporalSatisfies σ kind I φ S ↔ temporalSatisfies σ kind I φ T := by rw [h]

/-- Both raw-scope inclusion and shifted-region inclusion suffice uniformly. -/
theorem temporal_mono (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) {S T : Scope}
    (hs : S.carrier ⊆ T.carrier)
    (ha : (alwaysRegion S I).carrier ⊆ (alwaysRegion T I).carrier) :
    temporalSatisfies σ kind I φ T → temporalSatisfies σ kind I φ S := by
  cases kind with
  | always => exact fun h t ht => h t (ha ht)
  | eventually => exact fun h t ht => h t (hs ht)

/-- Scope unions and their shifted analogues distribute temporal obligations. -/
theorem temporal_union (σ : FiniteSignal Var) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) {S T U : Scope}
    (hs : S.carrier ∪ T.carrier = U.carrier)
    (ha : (alwaysRegion S I).carrier ∪ (alwaysRegion T I).carrier =
      (alwaysRegion U I).carrier) :
    (temporalSatisfies σ kind I φ S ∧ temporalSatisfies σ kind I φ T) ↔
      temporalSatisfies σ kind I φ U := by
  cases kind with
  | always =>
      constructor
      · rintro ⟨hS, hT⟩ t ht
        rcases (show t.1 ∈ (alwaysRegion S I).carrier ∪
          (alwaysRegion T I).carrier from ha.symm ▸ ht) with ht | ht
        · exact hS t ht
        · exact hT t ht
      · intro h
        exact ⟨fun t ht => h t (by change t.1 ∈ (alwaysRegion U I).carrier; rw [← ha]; exact Or.inl ht), fun t ht => h t (by change t.1 ∈ (alwaysRegion U I).carrier; rw [← ha]; exact Or.inr ht)⟩
  | eventually =>
      constructor
      · rintro ⟨hS, hT⟩ t ht
        rcases (show t ∈ S.carrier ∪ T.carrier from hs.symm ▸ ht) with ht | ht
        · exact hS t ht
        · exact hT t ht
      · intro h
        exact ⟨fun t ht => h t (by change t ∈ U.carrier; rw [← hs]; exact Or.inl ht), fun t ht => h t (by change t ∈ U.carrier; rw [← hs]; exact Or.inr ht)⟩

/-- Lemma 3.11 (1), both temporal operators. -/
theorem upper_implies_bounded (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c d : Clock) (b q : Marker) (kind : TemporalKind)
    (I : BoundedTimeInterval) (φ : Formula Var) (hne : J.carrier.Nonempty) :
    predicateSatisfies σ J α (.upper c b kind I φ) →
      predicateSatisfies σ J α (.bounded c d b q kind I φ) := by
  rw [upper_temporal, bounded_temporal]
  exact temporal_mono σ kind I φ
    (boundedScope_subset_upperScope J α c d b q hne)
    (by cases kind <;> exact boundedAlwaysRegion_subset_upperAlwaysRegion J α c d b q I hne)

/-- Extended Lemma 3.12: touching endpoints need only one closed side. -/
theorem predicate_merge_connected (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty)
    (hjoin : (α d₁ : ℝ) <[Marker.disj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    (predicateSatisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      predicateSatisfies σ J α (.upper c₂ b₂ kind I φ)) ↔
      predicateSatisfies σ J α (.upper c₁ b₁ kind I φ) := by
  have hl : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)) := by
    simpa only [MarkedLT, Marker.includes_imp] using hleft
  have hj : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes)) := by
    simpa only [MarkedLT, Marker.includes_disj] using hjoin
  rw [bounded_temporal, upper_temporal, upper_temporal]
  apply temporal_union σ kind I φ
  · cases kind <;> exact carrier_union_bounded_upper J α c₁ d₁ c₂ b₁ q₁ b₂ hne hl hj
  · cases kind <;> exact carrier_union_bounded_upper_alwaysRegion J α c₁ d₁ c₂ b₁ q₁ b₂ I hne hl hj

/-- Original overlap specialization of Lemma 3.12, retained for compatibility. -/
theorem predicate_merge (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c₁ d₁ c₂ : Clock) (b₁ q₁ b₂ : Marker)
    (kind : TemporalKind) (I : BoundedTimeInterval) (φ : Formula Var)
    (hne : J.carrier.Nonempty)
    (hjoin : (α d₁ : ℝ) <[Marker.conj q₁ b₂] (α c₂ : ℝ))
    (hleft : (α c₂ : ℝ) <[Marker.imp b₂ b₁] (α c₁ : ℝ)) :
    (predicateSatisfies σ J α (.bounded c₁ d₁ b₁ q₁ kind I φ) ∧
      predicateSatisfies σ J α (.upper c₂ b₂ kind I φ)) ↔
      predicateSatisfies σ J α (.upper c₁ b₁ kind I φ) := by
  have hl : (α c₂ : ℝ) < α c₁ ∨
      ((α c₂ : ℝ) = α c₁ ∧ (b₂.Includes → b₁.Includes)) := by
    simpa only [MarkedLT, Marker.includes_imp] using hleft
  have hj : (α d₁ : ℝ) < α c₂ ∨
      ((α d₁ : ℝ) = α c₂ ∧ (q₁.Includes ∨ b₂.Includes)) := by
    rcases hjoin with h | ⟨h, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl ((Marker.includes_conj _ _).1 hm).1⟩
  rw [bounded_temporal, upper_temporal, upper_temporal]
  apply temporal_union σ kind I φ
  · cases kind <;> exact carrier_union_bounded_upper J α c₁ d₁ c₂ b₁ q₁ b₂ hne hl hj
  · cases kind <;> exact carrier_union_bounded_upper_alwaysRegion J α c₁ d₁ c₂ b₁ q₁ b₂ I hne hl hj

/-- Proposition 3.10 (1), eventuality, with the actual left marker. -/
theorem plain_eventually_iff_upper_zero (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hJ : J.carrier ⊆ σ.domain) :
    predicateSatisfies σ J α (.plain (◇[(I : TimeInterval)] φ)) ↔
      predicateSatisfies σ J α (.upper c J.leftBoundary .eventually I φ) := by
  have he : scope J α (.upper c J.leftBoundary .eventually I φ) =
      Scope.ofMarkedInterval J := by simp [scope, Scope.ofMarkedInterval, hc]
  constructor
  · intro h t ht
    have htJ : t ∈ J := by simpa [he] using ht
    exact (FiniteSignal.satisfies_eventually_iff σ (I : TimeInterval) φ ⟨t, hJ htJ⟩).1
      (h ⟨t, hJ htJ⟩ htJ)
  · intro h t ht
    apply (FiniteSignal.satisfies_eventually_iff σ (I : TimeInterval) φ t).2
    exact h t.1 (by simpa [he] using ht)

/-- Proposition 3.10 (1), always, with all endpoint cases. -/
theorem plain_always_iff_upper_zero (σ : FiniteSignal Var) (J : MarkedInterval)
    (α : ClockValuation Clock) (c : Clock) (I : BoundedTimeInterval) (φ : Formula Var)
    (hc : (α c : ℝ) = 0) (hne : J.carrier.Nonempty) (hJ : J.carrier ⊆ σ.domain) :
    predicateSatisfies σ J α (.plain (□[(I : TimeInterval)] φ)) ↔
      predicateSatisfies σ J α (.upper c J.leftBoundary .always I φ) := by
  constructor
  · intro h t ht
    have he : scope J α (.upper c J.leftBoundary .always I φ) =
        Scope.ofMarkedInterval J := by simp [scope, Scope.ofMarkedInterval, hc]
    have ht' : t.1 ∈ alwaysRegion (Scope.ofMarkedInterval J) I := by simpa [he] using ht
    obtain ⟨u, hu, htu⟩ := exists_mem_and_mem_translate_of_mem_alwaysRegion J I hne ht'
    exact (FiniteSignal.satisfies_always_iff σ (I : TimeInterval) φ ⟨u, hJ hu⟩).1
      (h ⟨u, hJ hu⟩ hu) t htu
  · intro h
    have hlegacy : IntervalPredicate.Satisfies σ J α (.upper c J.leftBoundary .always I φ) :=
      fun t ht _ => h t ht
    exact satisfies_plain_always_of_upper_of_zero σ J α c J.leftBoundary I φ hc rfl hlegacy

end STLTableau
