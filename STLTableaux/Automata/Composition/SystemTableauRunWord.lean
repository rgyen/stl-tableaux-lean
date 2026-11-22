import STLTableaux.Automata.Composition.SystemTableauProjectedCell

/-! A constructed finite prefix consists of actual product flows and
jumps over the original physical signal. The goal belongs to its last
closed flow endpoint; no final jump or value at the signal horizon is used. -/
namespace STLTableau.Section4.Tableau
open HybridAutomaton
variable {Clock Var State Mode Label : Type*} (T : Tableau Clock Var State)

def SystemGoalWord (H : HybridAutomaton Mode Label Var) (h : T.TranslationReady)
    (σ : FiniteSignal Var) (s : (T.systemTableauAutomaton H h σ.horizon).State)
    (time : ℝ) : Prop :=
  ∃ (a b : (T.systemTableauAutomaton H h σ.horizon).State) (stop : ℝ),
    Relation.ReflTransGen (T.systemTableauAutomaton H h σ.horizon).DiscreteStep s a ∧
      Nonempty (ProjectedFlowWord (T.systemTableauAutomaton H h σ.horizon)
        σ T.systemCoordinate a time b stop) ∧
      stop ≤ σ.horizon ∧ b ∈ T.systemTableauGoal H h σ.horizon

namespace SystemGoalWord
variable {T} {H : HybridAutomaton Mode Label Var} {h : T.TranslationReady}
variable {σ : FiniteSignal Var}
local notation "B" => T.systemTableauAutomaton H h σ.horizon

theorem of_piece (p : ProjectedFlowPiece B σ T.systemCoordinate)
    (stop : p.left + (p.duration : ℝ) ≤ σ.horizon)
    (goal : p.finish ∈ T.systemTableauGoal H h σ.horizon) :
    T.SystemGoalWord H h σ p.start p.left :=
  ⟨p.start, p.finish, _, .refl, ⟨.last p⟩, stop, goal⟩

theorem prepend (p : ProjectedFlowPiece B σ T.systemCoordinate)
    {s : (B).State} (jump : (B).DiscreteStep p.finish s)
    (tail : T.SystemGoalWord H h σ s (p.left + p.duration)) :
    T.SystemGoalWord H h σ p.start p.left := by
  obtain ⟨a, b, stop, lead, ⟨word⟩, bound, goal⟩ := tail
  exact ⟨p.start, b, stop, .refl, ⟨.cons p (lead.head jump) word⟩, bound, goal⟩

theorem prepend_jump {a b : (B).State} {time : ℝ} (jump : (B).DiscreteStep a b)
    (tail : T.SystemGoalWord H h σ b time) : T.SystemGoalWord H h σ a time := by
  obtain ⟨s, t, stop, lead, word, bound, goal⟩ := tail
  exact ⟨s, t, stop, lead.head jump, word, bound, goal⟩

end SystemGoalWord

end STLTableau.Section4.Tableau
