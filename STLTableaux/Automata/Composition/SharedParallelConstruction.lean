import STLTableaux.Automata.Composition.SharedParallelComposition

/-! The two-way, local transition characterization of shared-variable
parallel composition. These are proved from its definition; no execution
or trace-composition equivalence is introduced as an axiom. -/
namespace STLTableau.HybridAutomaton
variable {M₁ L₁ V₁ M₂ L₂ V₂ Name : Type*}
variable (H₁ : HybridAutomaton M₁ L₁ V₁) (H₂ : HybridAutomaton M₂ L₂ V₂)
variable (ι₁ : V₁ ↪ Name) (ι₂ : V₂ ↪ Name)
local notation "P" => H₁.parallelOn H₂ ι₁ ι₂
local notation "left" => H₁.leftStateOn H₂ ι₁ ι₂
local notation "right" => H₁.rightStateOn H₂ ι₁ ι₂

theorem parallelOn_initial_iff (s : (P).State) :
    s.val ∈ (P).initial ↔ (left s).val ∈ H₁.initial ∧ (right s).val ∈ H₂.initial :=
  Iff.rfl

theorem parallelOn_continuous_iff {a b : (P).State} {r : NNReal}
    {γ : HybridFlow.Curve (JoinedVar ι₁ ι₂) r} :
    (P).ContinuousStep a b r γ ↔
      H₁.ContinuousStep (left a) (left b) r (fun t x => γ t (leftVar ι₁ ι₂ x)) ∧
      H₂.ContinuousStep (right a) (right b) r (fun t x => γ t (rightVar ι₁ ι₂ x)) := by
  constructor
  · intro step
    exact ⟨H₁.parallelOn_continuous_left H₂ ι₁ ι₂ step,
      H₁.parallelOn_continuous_right H₂ ι₁ ι₂ step⟩
  · rintro ⟨l, k⟩
    refine ⟨Prod.ext l.1 k.1, ?_, ?_, ?_⟩
    · funext x
      rcases every_joined_variable ι₁ ι₂ x with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact congrFun l.2.1 v
      · exact congrFun k.2.1 v
    · funext x
      rcases every_joined_variable ι₁ ι₂ x with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · exact congrFun l.2.2.1 v
      · exact congrFun k.2.2.1 v
    · intro t
      exact ⟨⟨(l.2.2.2 t).1, (k.2.2.2 t).1⟩,
        (l.2.2.2 t).2, (k.2.2.2 t).2⟩

/-- Includes one-sided idle transitions and simultaneous transitions,
and excludes a step in which both components are idle. -/
theorem parallelOn_discrete_iff (a b : (P).State) :
    (P).DiscreteStep a b ↔
      ∃ l₁ l₂, (l₁, l₂) ≠ (none, none) ∧
        H₁.IdleEdge (left a).val.1 l₁ (left b).val.1 ∧
        H₂.IdleEdge (right a).val.1 l₂ (right b).val.1 ∧
        H₁.IdleJump l₁ (left a).val (left b).val ∧
        H₂.IdleJump l₂ (right a).val (right b).val := by
  constructor
  · rintro ⟨⟨⟨q, l, q'⟩, he⟩, hs, ht, jump⟩
    dsimp only at hs ht he jump
    subst q
    subst q'
    exact ⟨l.1, l.2, he.1, he.2.1, he.2.2, jump.1, jump.2⟩
  · rintro ⟨l₁, l₂, live, edge₁, edge₂, jump₁, jump₂⟩
    exact ⟨⟨(a.val.1, (l₁, l₂), b.val.1), live, edge₁, edge₂⟩,
      rfl, rfl, jump₁, jump₂⟩

run_elab do
  for n in #[``parallelOn_initial_iff, ``parallelOn_continuous_iff,
      ``parallelOn_discrete_iff] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{n} uses unexpected axiom {ax}"

end STLTableau.HybridAutomaton
