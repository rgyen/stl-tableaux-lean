import STLTableaux.Automata.Translation.TypedTableauAutomata
import STLTableaux.Rules.Catalogue.ClockedExpansion

namespace STLTableau.Section4.Tableau

/-- A guard can be advanced slightly along a rate-one flow exactly under
these one-sided conditions. At a lower bound, equality is not enough. -/
def beforeBound : ClockRelation → ℝ → ℝ → Prop
  | .ge | .gt => (· > ·)
  | .eq => fun _ _ => False
  | .lt => (· < ·)
  | .le => (· ≤ ·)

theorem beforeBound_iff (r : ClockRelation) (x b : ℝ) :
    beforeBound r x b ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε → realComparison r (x-δ) b := by
  constructor
  · cases r with
    | ge | gt =>
      intro h
      change b < x at h
      refine ⟨x-b,by linarith,fun δ _ hd => ?_⟩
      simp only [realComparison]
      linarith
    | eq => exact False.elim
    | lt | le =>
      intro h
      simp only [beforeBound] at h
      refine ⟨1,zero_lt_one,fun δ hd _ => ?_⟩
      simp only [realComparison]
      linarith
  · rintro ⟨ε,hε,h⟩
    have h0 := h 0 le_rfl hε
    have hm := h (ε/2) (by linarith) (by linarith)
    cases r <;> simp only [beforeBound,realComparison,sub_zero] at * <;> linarith

theorem guards_before_iff {Clock : Type*} (l : EdgeLabel Clock) (ν : Clock → ℝ) :
    (∀ g ∈ l.guards, beforeBound g.relation (ν g.clock) g.bound) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε →
        ∀ g ∈ l.guards, realComparison g.relation (ν g.clock-δ) g.bound := by
  constructor
  · intro h
    suffices aux : ∀ S : Set (Section3.Guard Clock), S.Finite → S ⊆ l.guards →
        ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ < ε → ∀ g ∈ S,
          realComparison g.relation (ν g.clock-δ) g.bound by
      exact aux _ l.guards_finite Set.Subset.rfl
    intro S hf
    induction S, hf using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1,zero_lt_one,by simp⟩
    | @insert g S hg hs ih =>
      intro sub
      obtain ⟨a,ha,h₁⟩ := (beforeBound_iff _ _ _).mp (h g (sub (Set.mem_insert g S)))
      obtain ⟨b,hb,h₂⟩ := ih (fun _ hx => sub (Set.mem_insert_of_mem _ hx))
      refine ⟨min a b,lt_min ha hb,?_⟩
      intro δ hd hδ k hk
      rcases Set.mem_insert_iff.mp hk with rfl | hk
      · exact h₁ δ hd (hδ.trans_le (min_le_left _ _))
      · exact h₂ δ hd (hδ.trans_le (min_le_right _ _)) k hk
  · rintro ⟨ε,hε,h⟩ g hg
    exact (beforeBound_iff _ _ _).mpr ⟨ε,hε,fun δ hd he => h δ hd he g hg⟩

/-- The γ on a positive residence. The real coordinates are
unconstrained by flow; all three kinds of clock and the type bit are fixed. -/
def forwardCurveValue {Clock Var State : Type*} (T : Tableau Clock Var State)
    (v : T.TypedVar → ℝ) (d : ℝ) (x : T.realVariables → ℝ) : T.TypedVar → ℝ
  | .inl (.inl i) => x i
  | .inl (.inr c) => v (.inl (.inr c)) + d
  | .inr false => v T.dwell + d
  | .inr true => v T.bit

theorem forward_positive_flow {Clock Var State : Type*} (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (a : (T.typedAutomaton h τ).State)
    (r : NNReal) (hr : 0 < r)
    (x : Set.Ico (0 : ℝ) r → T.realVariables → ℝ) (w : T.realVariables → ℝ)
    (hx0 : x ⟨0,le_rfl,hr⟩ = fun i => a.val.2 (.inl (.inl i)))
    (hx : ∀ t, T.atomsAt a.val.1 (T.forwardCurveValue a.val.2 t.val (x t)))
    (hw : T.atomsAt a.val.1 (T.forwardCurveValue a.val.2 r w))
    (hg : a.val.1 ∉ T.terminalModes → a.val.2 (.inl T.globalClock) + r ≤ τ) :
    ∃ (b : (T.typedAutomaton h τ).State)
      (γ : Set.Icc (0 : ℝ) r → T.TypedVar → ℝ),
      (T.typedAutomaton h τ).ContinuousStep a b r γ ∧
      (∀ (t : Set.Icc (0 : ℝ) r) (ht : t.val < (r : ℝ)), ∀ i : T.realVariables,
        γ t (.inl (.inl i)) = x ⟨t.val,t.property.1,ht⟩ i) ∧
      (∀ i : T.realVariables, b.val.2 (.inl (.inl i)) = w i) := by
  let γ (t : Set.Icc (0 : ℝ) r) :=
    T.forwardCurveValue a.val.2 t.val (if ht : t.val < r then x ⟨t.val,t.property.1,ht⟩ else w)
  have inv (t : Set.Icc (0 : ℝ) r) :
      (a.val.1,γ t) ∈ (T.typedAutomaton h τ).invariant := by
    refine ⟨a.property.1,fun hn => ?_,?_,a.property.2.2.2⟩
    · change a.val.2 (.inl T.globalClock) + t.val ≤ τ
      linarith [t.property.2,hg hn]
    · by_cases ht : t.val < r
      · simpa only [γ,dif_pos ht] using hx ⟨t.val,t.property.1,ht⟩
      · have he := le_antisymm t.property.2 (le_of_not_gt ht)
        simpa [γ,he] using hw
  let endTime : Set.Icc (0 : ℝ) r := ⟨r,by simp⟩
  let b : (T.typedAutomaton h τ).State := ⟨(a.val.1,γ endTime),inv endTime⟩
  refine ⟨b,γ,⟨rfl,?_,rfl,?_⟩,?_,?_⟩
  · funext y
    cases y with
    | inl y =>
      cases y with
      | inl i => simpa [γ,forwardCurveValue,hr] using congrFun hx0 i
      | inr c => simp [γ,forwardCurveValue]
    | inr bit => cases bit <;> simp [γ,forwardCurveValue,Tableau.dwell,Tableau.bit]
  · intro t
    exact ⟨⟨fun _ => rfl,rfl,rfl,rfl⟩,inv t⟩
  · intro t ht i
    simp [γ,forwardCurveValue,ht]
  · intro i
    simp [b,γ,endTime,forwardCurveValue]

end STLTableau.Section4.Tableau

namespace STLTableau.ExpansionRule

/-- The finish branch for an eventuality of the `↑↓` form with bounded `I` permits equality
at the lower endpoint.
The next marker is closed. -/
theorem forward_finish_at_lower {Var : Type*} (p : Formula Var) :
    let I : BoundedTimeInterval := ⟨1,2,by norm_num,by norm_num⟩
    boundedEventually_finish (1 : ℕ) ○ ● I p ∈
        (boundedEventually 0 1 ● ○ I p).branches ∧
    boundedEventually_finish (1 : ℕ) ○ ● I p =
      .conj (.predicate (.plain p)) (.next (.conj (.clock 1 .ge 1) (.leftMarker ●))) := by
  exact ⟨by simp [boundedEventually],rfl⟩

end STLTableau.ExpansionRule
