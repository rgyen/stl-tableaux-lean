import STLTableaux.Semantics.Invariants.Invariants

/-! Numerical and marker kernels for the reachable shape of bounded G.
All ages are evaluated valuations. These lemmas do not yet establish a
whole-path shape theorem or a G label-count bound. -/
namespace STLTableau.Section4.Finiteness.AlwaysAgeShape
open scoped STL
variable {Clock : Type*}

/-- Either the origin endpoints are ordered, or a check has placed the
checking left endpoint exactly at this piece's actual left boundary. -/
def Holds (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b : Marker) (a : NNReal) : Prop :=
  α d ≤ α c ∨ α c = a ∧ b = J.leftBoundary

theorem ordinary_elapse (J : MarkedInterval) (α : ClockValuation Clock)
    (c d : Clock) (b : Marker) (a δ : NNReal) (h : α d ≤ α c) :
    Holds J (ClockResetSet.elapse α δ) c d b a := by
  apply Or.inl
  change α d + δ ≤ α c + δ
  exact add_le_add h le_rfl

/-- A real checked endpoint cannot survive an actual defer guard. The
zero-duration case is excluded by the singleton's complementary markers. -/
theorem checked_defer_impossible {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size) (hn : i.1+1 < P.size)
    (α : ClockValuation Clock) (c : Clock) (b : Marker) (a : NNReal)
    (hc : α c = a) (hb : b = (P.interval i).leftBoundary)
    (hg : ((ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) c : ℝ)
      <[Marker.imp b (P.interval ⟨i.1+1,hn⟩).leftBoundary] (a : ℝ)) : False := by
  have hle : ((ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) c : ℝ) ≤ a :=
    hg.elim le_of_lt (fun h => h.1.le)
  have hd : STLTableau.Judgement.duration P i = 0 := by
    apply NNReal.coe_injective
    have hδ := (STLTableau.Judgement.duration P i).coe_nonneg
    simp only [ClockResetSet.elapse,NNReal.coe_add,hc] at hle
    simp only [NNReal.coe_zero]
    linarith
  have he : (P.interval i).left = (P.interval i).right := by
    have hd' : (P.interval i).right - (P.interval i).left = 0 :=
      congrArg (fun x : NNReal => (x : ℝ)) hd
    linarith
  obtain ⟨x,hx⟩ := P.nonempty i
  have hxl := MarkedInterval.left_le_of_mem hx
  have hxr := MarkedInterval.le_right_of_mem hx
  have hleft : (P.interval i).leftBoundary.Includes := by
    rcases hx.1 with h | ⟨_,h⟩
    · exfalso; linarith
    · exact h
  have hright : (P.interval i).rightBoundary.Includes := by
    rcases hx.2 with h | ⟨_,h⟩
    · exfalso; linarith
    · exact h
  have himp : (Marker.imp b (P.interval ⟨i.1+1,hn⟩).leftBoundary).Includes := by
    simpa [ClockResetSet.elapse,hc,hd,MarkedLT] using hg
  have hnext := (Marker.includes_imp _ _).mp himp (hb ▸ hleft)
  rw [P.adjacent_rightBoundary_eq_complement_leftBoundary i hn] at hright
  exact ((Marker.includes_complement _).mp hright) hnext

/-- Thus actual defer retains the ordinary case of the source shape. -/
theorem defer_preserves {L R : ℝ}
    (P : IntervalPartition (Set.Ico L R)) (i : Fin P.size) (hn : i.1+1 < P.size)
    (α : ClockValuation Clock) (c d : Clock) (b : Marker) (a : NNReal)
    (hs : Holds (P.interval i) α c d b a)
    (hg : ((ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) c : ℝ)
      <[Marker.imp b (P.interval ⟨i.1+1,hn⟩).leftBoundary] (a : ℝ)) :
    Holds (P.interval ⟨i.1+1,hn⟩)
      (ClockResetSet.elapse α (STLTableau.Judgement.duration P i)) c d b a := by
  rcases hs with ho | ⟨hc,hb⟩
  · exact ordinary_elapse _ α c d b a _ ho
  · exact (checked_defer_impossible P i hn α c b a hc hb hg).elim

/-- Scoped alpha/reset transport can use the actual assignment directly. -/
theorem check_assignment_shape
    (J : MarkedInterval) (α : ClockValuation Clock) (Γ : ClockResetSet Clock)
    (c d : Clock) (a : NNReal) (hc : Γ.value c = some a) :
    Holds J (Γ.apply α) c d J.leftBoundary a := by
  apply Or.inr
  exact ⟨by simp only [ClockResetSet.apply,hc],rfl⟩

theorem check_reset_shape [DecidableEq Clock]
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock) (a : NNReal) :
    Holds J ((ClockResetSet.singleton c a).apply α) c d J.leftBoundary a := by
  exact Or.inr ⟨ClockResetSet.apply_singleton_self c a α,rfl⟩

theorem upper_check_reset_shape [DecidableEq Clock]
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock) (a : NNReal) :
    Holds J (((ClockResetSet.singleton c a).union
      (ClockResetSet.singleton d 0)).apply α) c d J.leftBoundary a := by
  apply check_assignment_shape
  simp [ClockResetSet.union,ClockResetSet.singleton]

/-- The defer branch of the `↑` form resets the right clock to zero,
giving ordered origins. -/
theorem upper_defer_reset_shape [DecidableEq Clock]
    (J : MarkedInterval) (α : ClockValuation Clock) (c d : Clock) (b : Marker) (a : NNReal) :
    Holds J ((ClockResetSet.singleton d 0).apply α) c d b a := by
  apply Or.inl
  rw [ClockResetSet.apply_singleton_self]
  exact zero_le

end STLTableau.Section4.Finiteness.AlwaysAgeShape
