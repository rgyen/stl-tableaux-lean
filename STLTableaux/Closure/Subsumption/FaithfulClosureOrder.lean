import STLTableaux.Closure.Residual.Closure
import STLTableaux.Closure.Normalization.ConcreteNormalization

/-! Minimal rule-closed extensions under syntactic subsumption.
The existence of a closed extension is a separate termination obligation. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

noncomputable def StateForm.componentCount (S : StateForm Clock Var) : ℕ :=
  S.guards.ncard + S.resets.clocks.ncard + S.locals.ncard

noncomputable def TransitionForm.componentCount (Φ : TransitionForm Clock Var) : ℕ :=
  Φ.current.componentCount + match Φ.nextPart with
    | none => 0
    | some N => N.componentCount + 1

theorem StateForm.ext_components {S T : StateForm Clock Var}
    (hg : S.guards = T.guards) (hr : S.resets = T.resets) (hl : S.locals = T.locals) : S = T := by
  cases S; cases T; cases hg; cases hr; cases hl; rfl

theorem StateForm.componentCount_le
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.guards ⊆ S₂.guards)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals) :
    S₁.componentCount ≤ S₂.componentCount := by
  have hCf := Set.ncard_le_ncard hC S₂.guards_finite
  have hΛf : S₂.resets.clocks.Finite := by
    simpa [ClockResetSet.clocks] using S₂.resets.finite_domain
  have hΛc := Set.ncard_le_ncard (ClockResetSet.clocks_mono hΛ) hΛf
  have hLf := Set.ncard_le_ncard hL S₂.locals_finite
  simp only [StateForm.componentCount]
  omega

theorem StateForm.eq_of_componentCount_eq
    {S₁ S₂ : StateForm Clock Var}
    (hC : S₁.guards ⊆ S₂.guards)
    (hΛ : S₁.resets.Subset S₂.resets)
    (hL : S₁.locals ⊆ S₂.locals)
    (hcount : S₁.componentCount = S₂.componentCount) : S₁ = S₂ := by
  have hCf := Set.ncard_le_ncard hC S₂.guards_finite
  have hΛ₂f : S₂.resets.clocks.Finite := by
    simpa [ClockResetSet.clocks] using S₂.resets.finite_domain
  have hΛc := Set.ncard_le_ncard (ClockResetSet.clocks_mono hΛ) hΛ₂f
  have hLf := Set.ncard_le_ncard hL S₂.locals_finite
  have hCcard : S₁.guards.ncard = S₂.guards.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hΛcard : S₁.resets.clocks.ncard = S₂.resets.clocks.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hLcard : S₁.locals.ncard = S₂.locals.ncard := by
    simp only [StateForm.componentCount] at hcount
    omega
  have hCeq := Set.eq_of_subset_of_ncard_le hC hCcard.ge S₂.guards_finite
  have hΛeqClocks := Set.eq_of_subset_of_ncard_le
    (ClockResetSet.clocks_mono hΛ) hΛcard.ge hΛ₂f
  have hΛeq := ClockResetSet.eq_of_subset_of_clocks_eq hΛ hΛeqClocks
  have hLeq := Set.eq_of_subset_of_ncard_le hL hLcard.ge S₂.locals_finite
  exact StateForm.ext_components hCeq hΛeq hLeq


theorem SyntacticallySubsumed.refl (Φ : TransitionForm Clock Var) :
    SyntacticallySubsumed Φ Φ := by
  refine ⟨⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩, ?_, ?_⟩
  · exact Set.disjoint_left.2 (fun _ h hc => hc.2 h)
  · intro N hN
    exact ⟨N, hN, ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩,
      Set.disjoint_left.2 (fun _ h hc => hc.2 h)⟩

theorem SyntacticallySubsumed.componentCount_le {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) : Φ.componentCount ≤ Ψ.componentCount := by
  have hc := StateForm.componentCount_le h.current.guards h.current.resets h.current.locals
  cases hf : Φ.nextPart with
  | none => cases ht : Ψ.nextPart <;> simp [TransitionForm.componentCount, hf, ht] <;> omega
  | some N =>
      obtain ⟨M, hm, hi, _⟩ := h.next N hf
      have hn := StateForm.componentCount_le hi.guards hi.resets hi.locals
      simp only [TransitionForm.componentCount, hf, hm]
      omega

theorem SyntacticallySubsumed.eq_of_componentCount_eq {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (he : Φ.componentCount = Ψ.componentCount) : Φ = Ψ := by
  have hc := StateForm.componentCount_le h.current.guards h.current.resets h.current.locals
  cases hf : Φ.nextPart with
  | none =>
      cases ht : Ψ.nextPart with
      | none =>
          have hec : Φ.current.componentCount = Ψ.current.componentCount := by
            simpa only [TransitionForm.componentCount, hf, ht, Nat.add_zero] using he
          have hcur := StateForm.eq_of_componentCount_eq h.current.guards h.current.resets h.current.locals hec
          cases Φ; cases Ψ; simp_all
      | some M => simp only [TransitionForm.componentCount, hf, ht] at he; omega
  | some N =>
      obtain ⟨M, hm, hi, _⟩ := h.next N hf
      have hn := StateForm.componentCount_le hi.guards hi.resets hi.locals
      have hcur : Φ.current.componentCount = Ψ.current.componentCount := by
        simp only [TransitionForm.componentCount, hf, hm] at he
        omega
      have hnxt : N.componentCount = M.componentCount := by
        simp only [TransitionForm.componentCount, hf, hm] at he
        omega
      have hec := StateForm.eq_of_componentCount_eq h.current.guards h.current.resets h.current.locals hcur
      have hen := StateForm.eq_of_componentCount_eq hi.guards hi.resets hi.locals hnxt
      cases Φ; cases Ψ; simp_all

theorem SyntacticallySubsumed.antisymm {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (hr : SyntacticallySubsumed Ψ Φ) : Φ = Ψ :=
  h.eq_of_componentCount_eq (Nat.le_antisymm h.componentCount_le hr.componentCount_le)

theorem ComponentsIncluded.localClocks_mono {S T : StateForm Clock Var}
    (h : ComponentsIncluded S T) : S.localClocks ⊆ T.localClocks := by
  rintro c ⟨l, hl, hc⟩
  exact ⟨l, h.locals hl, hc⟩

theorem ComponentsIncluded.freeClocks_mono {S T : StateForm Clock Var}
    (h : ComponentsIncluded S T)
    (hfresh : Disjoint T.resets.clocks (S.localClocks \ S.resets.clocks)) :
    S.freeClocks ⊆ T.freeClocks := by
  intro c hc
  rcases hc with ⟨g, hg, hgc⟩ | ⟨hc, hn⟩
  · exact Or.inl ⟨g, h.guards hg, hgc⟩
  · exact Or.inr ⟨h.localClocks_mono hc,
      fun ht => Set.disjoint_left.1 hfresh ht ⟨hc, hn⟩⟩

theorem SyntacticallySubsumed.unboundBody_mono {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) :
    Φ.bodyFreeClocks \ Φ.current.resets.clocks ⊆
      Ψ.bodyFreeClocks \ Ψ.current.resets.clocks := by
  rintro c ⟨hc, hn⟩
  refine ⟨?_, fun ht => Set.disjoint_left.1 h.outerFresh ht ⟨hc, hn⟩⟩
  rcases hc with hc | hc
  · exact Or.inl (h.current.localClocks_mono hc)
  · right
    cases hnxt : Φ.nextPart with
    | none => simp [hnxt] at hc
    | some N =>
        obtain ⟨M, hm, hi, hf⟩ := h.next N hnxt
        have hNM := hi.freeClocks_mono hf
        exact (show c ∈ (match Ψ.nextPart with | none => ∅ | some M => M.freeClocks) from
          by simpa only [hm] using hNM (by simpa only [hnxt] using hc))

theorem SyntacticallySubsumed.trans {Φ Ψ U : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (g : SyntacticallySubsumed Ψ U) :
    SyntacticallySubsumed Φ U := by
  refine ⟨⟨h.current.guards.trans g.current.guards,
    fun c a hc => g.current.resets c a (h.current.resets c a hc),
    h.current.locals.trans g.current.locals⟩, ?_, ?_⟩
  · exact Set.disjoint_left.2 (fun c hc hf =>
      Set.disjoint_left.1 g.outerFresh hc (h.unboundBody_mono hf))
  · intro N hn
    obtain ⟨M, hm, hi, hf⟩ := h.next N hn
    obtain ⟨K, hk, hj, hg⟩ := g.next M hm
    refine ⟨K, hk, ⟨hi.guards.trans hj.guards,
      fun c a hc => hj.resets c a (hi.resets c a hc), hi.locals.trans hj.locals⟩, ?_⟩
    apply Set.disjoint_left.2
    intro c hc hfree
    have hnM : c ∉ M.resets.clocks := fun hM => Set.disjoint_left.1 hf hM hfree
    exact Set.disjoint_left.1 hg hc ⟨hi.localClocks_mono hfree.1, hnM⟩

namespace ClosureCatalogue

/-- Definition 4.8 (closure). A closure is a minimal rule-closed extension. -/
structure IsClosure (E : ClosureCatalogue Clock Var) (Φ U : TransitionForm Clock Var) : Prop where
  extension : SyntacticallySubsumed Φ U
  closed : E.IsClosed U
  minimal : ∀ Θ : TransitionForm Clock Var,
    SyntacticallySubsumed Φ Θ → E.IsClosed Θ → SyntacticallySubsumed Θ U →
      SyntacticallySubsumed U Θ

theorem IsClosure.self {E : ClosureCatalogue Clock Var} {Φ : TransitionForm Clock Var}
    (hc : E.IsClosed Φ) : E.IsClosure Φ Φ :=
  ⟨SyntacticallySubsumed.refl Φ, hc, fun _ hext _ _ => hext⟩

/-- A literal minimal closure of a state form cannot keep a next part when
its current part is already rule-closed without that next part. -/
theorem IsClosure.nextPart_eq_none_of_current_closed
    {E : ClosureCatalogue Clock Var} {N : StateForm Clock Var}
    {F : TransitionForm Clock Var} (hc : E.IsClosure (.ofState N) F)
    (hcurrent : E.IsClosed (.ofState F.current)) : F.nextPart = none := by
  have hlow : SyntacticallySubsumed (.ofState N) (.ofState F.current) :=
    ⟨hc.extension.current, hc.extension.outerFresh, by intro M hm; cases hm⟩
  have href := SyntacticallySubsumed.refl (.ofState F.current)
  have hdrop : SyntacticallySubsumed (.ofState F.current) F :=
    ⟨href.current, href.outerFresh, by intro M hm; cases hm⟩
  have hback := hc.minimal _ hlow hcurrent hdrop
  cases hn : F.nextPart with
  | none => rfl
  | some M =>
      obtain ⟨K, hK, _⟩ := hback.next M hn
      cases hK


/-- A satisfied terminal state form has no interval predicates, so it is
its own literal closure. No interval or invariant at the terminal is invented. -/
theorem terminal_state_is_own_closure (E : ClosureCatalogue Clock Var)
    (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hk : k.1 = P.size) (hs : S.holds σ P α k) :
    E.IsClosure (TransitionForm.ofState S) (TransitionForm.ofState S) := by
  apply IsClosure.self
  intro p hp
  have hf := hs.2 (Local.predicate p) hp
  have hnot : ¬ k.1 < P.size := by omega
  simp only [Local.holds, Local.toJudgement, Judgement.holds, dif_neg hnot] at hf

/-- Finite-component counting turns any nonempty family of closed extensions
into a genuinely minimal closure. This theorem does not assume a closure. -/
theorem exists_minimal_closed_extension (E : ClosureCatalogue Clock Var)
    (Φ : TransitionForm Clock Var)
    (hex : ∃ U, SyntacticallySubsumed Φ U ∧ E.IsClosed U) : ∃ U, E.IsClosure Φ U := by
  classical
  let Q : ℕ → Prop := fun n => ∃ U : TransitionForm Clock Var,
    U.componentCount = n ∧ SyntacticallySubsumed Φ U ∧ E.IsClosed U
  have hQ : ∃ n, Q n := by
    obtain ⟨U, hu, hc⟩ := hex
    exact ⟨U.componentCount, U, rfl, hu, hc⟩
  obtain ⟨U, hn, hu, hc⟩ := Nat.find_spec hQ
  refine ⟨U, hu, hc, ?_⟩
  intro Θ hext hclosed hsub
  have hmin : Nat.find hQ ≤ Θ.componentCount := Nat.find_min' hQ ⟨Θ, rfl, hext, hclosed⟩
  have heq : Θ.componentCount = U.componentCount := by
    have := hsub.componentCount_le
    omega
  have hEq := hsub.eq_of_componentCount_eq heq
  subst Θ
  exact SyntacticallySubsumed.refl U

/-- Minimalization can stay below a given closed extension, so its semantic
truth transfers by syntactic-subsumption soundness. -/
theorem exists_minimal_closed_extension_below (E : ClosureCatalogue Clock Var)
    {Φ U : TransitionForm Clock Var} (hu : SyntacticallySubsumed Φ U) (hc : E.IsClosed U) :
    ∃ V, E.IsClosure Φ V ∧ SyntacticallySubsumed V U := by
  classical
  let Q : ℕ → Prop := fun n => ∃ V : TransitionForm Clock Var,
    V.componentCount = n ∧ SyntacticallySubsumed Φ V ∧ E.IsClosed V ∧ SyntacticallySubsumed V U
  have hQ : ∃ n, Q n := ⟨U.componentCount, U, rfl, hu, hc, SyntacticallySubsumed.refl U⟩
  obtain ⟨V, hn, hv, hcV, hVU⟩ := Nat.find_spec hQ
  refine ⟨V, ⟨hv, hcV, ?_⟩, hVU⟩
  intro Θ hΦΘ hcΘ hΘV
  have hΘU := hΘV.trans hVU
  have hmin : Nat.find hQ ≤ Θ.componentCount :=
    Nat.find_min' hQ ⟨Θ, rfl, hΦΘ, hcΘ, hΘU⟩
  have he : Θ.componentCount = V.componentCount := by
    have := hΘV.componentCount_le
    omega
  have hEq := hΘV.eq_of_componentCount_eq he
  subst Θ
  exact SyntacticallySubsumed.refl V

theorem exists_satisfied_minimal_below (E : ClosureCatalogue Clock Var)
    {Φ U : TransitionForm Clock Var} (hu : SyntacticallySubsumed Φ U) (hc : E.IsClosed U)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : U.holds σ P α k) :
    ∃ V, E.IsClosure Φ V ∧ SyntacticallySubsumed V U ∧ V.holds σ P α k := by
  obtain ⟨V, hV, hVU⟩ := E.exists_minimal_closed_extension_below hu hc
  exact ⟨V, hV, hVU, hVU.sound σ P α k hs⟩

end ClosureCatalogue
end STLTableau.Section3
