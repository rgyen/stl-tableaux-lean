import STLTableaux.Semantics.Stability.Stability

/-! Finite closed-segment form of the standard trajectory conditions in
Lynch--Segala--Vaandrager, Hybrid I/O Automata (2003), Definition 4.1.
Prefix closure follows from the entry-based flow predicate. Suffix and
finite concatenation closure are requirements on that predicate, not
new assumptions of an STL correctness theorem. No composition iff is assumed.
-/
namespace STLTableau.HybridFlow
variable {Mode Var : Type*}

abbrev Curve (Var : Type*) (r : NNReal) := Set.Icc (0 : ℝ) r → Var → ℝ

def Evolves (flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop)
    (inv : Set (Mode × (Var → ℝ))) (q : Mode) {r : NNReal} (γ : Curve Var r) : Prop :=
  ∀ t, flow (q, γ ⟨0, by simp⟩) ⟨t.val, t.property.1⟩ (γ t) ∧ (q, γ t) ∈ inv

def prefixCurve {r : NNReal} (γ : Curve Var r) (s : NNReal) (hs : s ≤ r) : Curve Var s :=
  fun t => γ ⟨t.val, t.property.1, t.property.2.trans hs⟩

def suffixCurve {r : NNReal} (γ : Curve Var r) (s : NNReal) (hs : s ≤ r) : Curve Var (r - s) :=
  fun t => γ ⟨s + t.val, by
    constructor
    · exact add_nonneg s.coe_nonneg t.property.1
    · have bound := t.property.2
      simp only [NNReal.coe_sub hs] at bound
      linarith⟩

noncomputable def concatCurve (r s : NNReal) (γ : Curve Var r) (δ : Curve Var s) :
    Curve Var (r + s) := fun t =>
  if ht : t.val ≤ (r : ℝ) then γ ⟨t.val, t.property.1, ht⟩
  else δ ⟨t.val - r, by
    have := t.property.2
    constructor <;> push_cast at * <;> linarith⟩

/-- The trajectory part of a finite hybrid automaton's well-formedness.
T1 is a theorem below; these are T2 and the finite form of T3. -/
structure Closed (flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop)
    (inv : Set (Mode × (Var → ℝ))) : Prop where
  suffix : ∀ {q r} {γ : Curve Var r}, Evolves flow inv q γ →
    ∀ s (hs : s ≤ r), Evolves flow inv q (HybridFlow.suffixCurve γ s hs)
  concat : ∀ {q r s} {γ : Curve Var r} {δ : Curve Var s},
    Evolves flow inv q γ → Evolves flow inv q δ →
    γ ⟨r, by simp⟩ = δ ⟨0, by simp⟩ → Evolves flow inv q (HybridFlow.concatCurve r s γ δ)

theorem prefix_closed {flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop}
    {inv : Set (Mode × (Var → ℝ))} {q r} {γ : Curve Var r}
    (h : Evolves flow inv q γ) (s : NNReal) (hs : s ≤ r) :
    Evolves flow inv q (prefixCurve γ s hs) := by
  intro t
  exact h ⟨t.val, t.property.1, t.property.2.trans hs⟩

/-- An algebraic sufficient condition useful for concrete clock equations.
The actual automaton interface only requires trajectory closure, not these
stronger pointwise laws. -/
theorem Closed.of_rebase_add
    (flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop)
    (inv : Set (Mode × (Var → ℝ)))
    (rebase : ∀ q v a b r s, flow (q, v) r a → flow (q, v) (r + s) b → flow (q, a) s b)
    (add : ∀ q v a b r s, flow (q, v) r a → flow (q, a) s b → flow (q, v) (r + s) b) :
    Closed flow inv where
  suffix := by
    intro q r γ h s hs t
    let a : Set.Icc (0 : ℝ) r := ⟨s, by simp [hs]⟩
    let b : Set.Icc (0 : ℝ) r := ⟨s + t.val, by
      constructor
      · exact add_nonneg s.coe_nonneg t.property.1
      · have bound := t.property.2
        simp only [NNReal.coe_sub hs] at bound
        linarith⟩
    have time : s + NNReal.mk t.val t.property.1 = NNReal.mk b.val b.property.1 :=
      Subtype.ext rfl
    have atStart : γ a = HybridFlow.suffixCurve γ s hs ⟨0, by simp⟩ := by
      apply congrArg γ
      exact Subtype.ext (by simp [a])
    have hb := (h b).1
    change flow (q, γ ⟨0, by simp⟩) (NNReal.mk b.val b.property.1) (γ b) at hb
    rw [← time] at hb
    have result := rebase q (γ ⟨0, by simp⟩) (γ a) (γ b) s
      ⟨t.val, t.property.1⟩ (h a).1 hb
    exact ⟨atStart ▸ result, (h b).2⟩
  concat := by
    intro q r s γ δ hγ hδ join t
    have initial : HybridFlow.concatCurve r s γ δ ⟨0, le_rfl, (r + s).coe_nonneg⟩ =
        γ ⟨0, by simp⟩ := by
      simp [HybridFlow.concatCurve]
    rw [initial]
    unfold HybridFlow.concatCurve
    split_ifs with ht
    · exact hγ ⟨t.val, t.property.1, ht⟩
    · let u : Set.Icc (0 : ℝ) s := ⟨t.val - r, by
        have := t.property.2
        constructor <;> push_cast at * <;> linarith⟩
      have time : r + NNReal.mk u.val u.property.1 = NNReal.mk t.val t.property.1 := by
        apply Subtype.ext
        dsimp [u]
        ring
      have next : flow (q, γ ⟨r, by simp⟩) ⟨u.val, u.property.1⟩ (δ u) :=
        join.symm ▸ (hδ u).1
      have result := add q _ _ _ r ⟨u.val, u.property.1⟩ (hγ ⟨r, by simp⟩).1 next
      change flow (q, γ ⟨0, by simp⟩) (r + NNReal.mk u.val u.property.1) (δ u) at result
      rw [time] at result
      exact ⟨result, (hδ u).2⟩

/-- Strengthening a pointwise invariant does not change trajectory closure. -/
theorem Closed.strengthen
    {flow : (Mode × (Var → ℝ)) → NNReal → (Var → ℝ) → Prop}
    {inv : Set (Mode × (Var → ℝ))} (h : Closed flow inv)
    (p : Mode × (Var → ℝ) → Prop) : Closed flow {s | s ∈ inv ∧ p s} where
  suffix := by
    intro q r γ e s hs t
    have old := h.suffix (fun u => ⟨(e u).1, (e u).2.1⟩) s hs t
    exact ⟨old.1, old.2, (e _).2.2⟩
  concat := by
    intro q r s γ δ e f join t
    have old := h.concat (fun u => ⟨(e u).1, (e u).2.1⟩)
      (fun u => ⟨(f u).1, (f u).2.1⟩) join t
    refine ⟨old.1, old.2, ?_⟩
    unfold HybridFlow.concatCurve
    split_ifs with ht
    · exact (e _).2.2
    · exact (f _).2.2

theorem concatCurve_map {V W : Type*} (r s : NNReal)
    (γ : Curve V r) (δ : Curve V s) (ι : W → V) :
    (fun t => concatCurve r s γ δ t ∘ ι) =
      concatCurve r s (fun t => γ t ∘ ι) (fun t => δ t ∘ ι) := by
  funext t x
  unfold concatCurve
  split_ifs <;> rfl

/-- Shared-variable product closure. Both components see restrictions of
the same valuation; no disjoint-variable premise is used. -/
theorem Closed.parallel {M₁ M₂ V₁ V₂ V : Type*}
    {f₁ : (M₁ × (V₁ → ℝ)) → NNReal → (V₁ → ℝ) → Prop}
    {f₂ : (M₂ × (V₂ → ℝ)) → NNReal → (V₂ → ℝ) → Prop}
    {i₁ : Set (M₁ × (V₁ → ℝ))} {i₂ : Set (M₂ × (V₂ → ℝ))}
    (h₁ : Closed f₁ i₁) (h₂ : Closed f₂ i₂) (ι₁ : V₁ → V) (ι₂ : V₂ → V) :
    Closed
      (fun (s : (M₁ × M₂) × (V → ℝ)) t v => f₁ (s.1.1, s.2 ∘ ι₁) t (v ∘ ι₁) ∧
        f₂ (s.1.2, s.2 ∘ ι₂) t (v ∘ ι₂))
      {s | (s.1.1, s.2 ∘ ι₁) ∈ i₁ ∧ (s.1.2, s.2 ∘ ι₂) ∈ i₂} where
  suffix := by
    intro q r γ h s hs t
    have l := h₁.suffix (q := q.1) (γ := fun u => γ u ∘ ι₁)
      (fun u => ⟨(h u).1.1, (h u).2.1⟩) s hs t
    have k := h₂.suffix (q := q.2) (γ := fun u => γ u ∘ ι₂)
      (fun u => ⟨(h u).1.2, (h u).2.2⟩) s hs t
    exact ⟨⟨l.1, k.1⟩, l.2, k.2⟩
  concat := by
    intro q r s γ δ hγ hδ join t
    have join₁ : γ ⟨r, by simp⟩ ∘ ι₁ = δ ⟨0, by simp⟩ ∘ ι₁ :=
      congrArg (fun v => v ∘ ι₁) join
    have join₂ : γ ⟨r, by simp⟩ ∘ ι₂ = δ ⟨0, by simp⟩ ∘ ι₂ :=
      congrArg (fun v => v ∘ ι₂) join
    have left := h₁.concat (q := q.1)
      (γ := fun u => γ u ∘ ι₁) (δ := fun u => δ u ∘ ι₁)
      (fun u => ⟨(hγ u).1.1, (hγ u).2.1⟩)
      (fun u => ⟨(hδ u).1.1, (hδ u).2.1⟩) join₁
    have right := h₂.concat (q := q.2)
      (γ := fun u => γ u ∘ ι₂) (δ := fun u => δ u ∘ ι₂)
      (fun u => ⟨(hγ u).1.2, (hγ u).2.2⟩)
      (fun u => ⟨(hδ u).1.2, (hδ u).2.2⟩) join₂
    rw [← concatCurve_map] at left right
    exact ⟨⟨(left t).1, (right t).1⟩, (left t).2, (right t).2⟩

theorem Closed.constant (inv : Set (Mode × (Var → ℝ))) :
    Closed (fun s _ v => v = s.2) inv := by
  apply Closed.of_rebase_add
  · intro q v a b r s first total
    exact total.trans first.symm
  · intro q v a b r s first second
    exact second.trans first

theorem Closed.unconstrained (inv : Set (Mode × (Var → ℝ))) :
    Closed (fun _ _ _ => True) inv :=
  Closed.of_rebase_add _ _ (by intros; trivial) (by intros; trivial)

run_elab do
  for n in #[``prefix_closed, ``Closed.of_rebase_add, ``Closed.strengthen,
      ``Closed.parallel, ``Closed.constant, ``Closed.unconstrained] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.HybridFlow
