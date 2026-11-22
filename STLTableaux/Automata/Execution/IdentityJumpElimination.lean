import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence
import STLTableaux.Automata.Recognition.TableauJumpPath

/-! Safe elimination of a repeated mode with an identity reset. This is not
an erasure rule for arbitrary intermediate modes or arbitrary trace positions. -/
namespace STLTableau.Section4
variable {Clock Var State : Type*}

namespace Path

def withFirstIncoming (l : EdgeLabel Clock) : Path Clock State → Path Clock State
  | .last _ s => .last l s
  | .step _ s p => .step l s p

@[simp] theorem withFirstIncoming_firstState (l : EdgeLabel Clock) (p : Path Clock State) :
    (p.withFirstIncoming l).firstState = p.firstState := by cases p <;> rfl

@[simp] theorem withFirstIncoming_firstIncoming (l : EdgeLabel Clock) (p : Path Clock State) :
    (p.withFirstIncoming l).firstIncoming = l := by cases p <;> rfl

@[simp] theorem withFirstIncoming_lastState (l : EdgeLabel Clock) (p : Path Clock State) :
    (p.withFirstIncoming l).lastState = p.lastState := by cases p <;> rfl

theorem withFirstIncoming_valid (T : Tableau Clock Var State)
    (l : EdgeLabel Clock) (p : Path Clock State) :
    (p.withFirstIncoming l).valid T ↔ p.valid T := by cases p <;> rfl

/-- Remove the first of two equal consecutive states while retaining its
incoming label. All later edges and the final state are unchanged. -/
theorem drop_duplicate_run (T : Tableau Clock Var State)
    (l : EdgeLabel Clock) (s : State) (p : Path Clock State)
    (heq : p.firstState = s) (hr : (Path.step l s p).run T) :
    (p.withFirstIncoming l).run T := by
  refine ⟨(withFirstIncoming_valid T l p).mpr hr.1.2.1, ?_⟩
  rw [withFirstIncoming_firstIncoming, withFirstIncoming_firstState, heq]
  exact hr.2

theorem drop_duplicate_accepting (T : Tableau Clock Var State)
    (l : EdgeLabel Clock) (s : State) (p : Path Clock State)
    (ha : (Path.step l s p).accepting T) : (p.withFirstIncoming l).accepting T := by
  exact ⟨(withFirstIncoming_valid T l p).mpr ha.1.2.1,
    (withFirstIncoming_lastState l p).symm ▸ ha.2⟩

/-- Incoming entry has already happened in a jump-block witness. Replacing
that first incoming label does not reapply its reset. -/
@[simp] theorem withFirstIncoming_jumpGuardsHold
    (l : EdgeLabel Clock) (p : Path Clock State) (α β : ClockValuation Clock) :
    (p.withFirstIncoming l).JumpGuardsHold α β ↔ p.JumpGuardsHold α β := by
  cases p <;> rfl

/-- Dropping an enabled zero-time step preserves every subsequent guard and
reset when its reset fixes the actual current valuation. Empty reset is only
one sufficient case; a nonempty reset to the existing value also qualifies. -/
theorem drop_first_jump_guards
    (l : EdgeLabel Clock) (s : State) (p : Path Clock State)
    (α β : ClockValuation Clock)
    (hr : p.firstIncoming.resets.apply α = α)
    (hg : (Path.step l s p).JumpGuardsHold α β) :
    (p.withFirstIncoming l).JumpGuardsHold α β := by
  rw [withFirstIncoming_jumpGuardsHold]
  exact hr ▸ hg.2

/-- A repeated mode can be removed while retaining both accepting-run
structure and the SAME guarded valuation witness. No partition/trace-next
equivalence follows from this jump-block theorem. -/
theorem drop_duplicate_guarded_run (T : Tableau Clock Var State)
    (l : EdgeLabel Clock) (s : State) (p : Path Clock State)
    (α β : ClockValuation Clock)
    (heq : p.firstState = s)
    (hr : (Path.step l s p).run T) (ha : (Path.step l s p).accepting T)
    (hreset : p.firstIncoming.resets.apply α = α)
    (hg : (Path.step l s p).JumpGuardsHold α β) :
    (p.withFirstIncoming l).run T ∧ (p.withFirstIncoming l).accepting T ∧
      (p.withFirstIncoming l).JumpGuardsHold α β :=
  ⟨drop_duplicate_run T l s p heq hr, drop_duplicate_accepting T l s p ha,
    drop_first_jump_guards l s p α β hreset hg⟩

end Path

namespace Tableau

@[simp] theorem reset_empty (T : Tableau Clock Var State) (v : T.HAVar → ℝ) :
    T.reset ClockResetSet.empty v = v := by
  funext x
  rcases x with x | c
  · rfl
  · rcases c with c | u <;> rfl

/-- For an actual enabled jump, empty reset and equal modes imply equal
semantic states. Merely ignoring its signal observation would not suffice. -/
theorem identity_jump_endpoints (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    (s s' : (T.toAutomaton h τ hτ).State) (l : EdgeLabel Clock)
    (hm : s.val.1 = s'.val.1) (hr : l.resets = ClockResetSet.empty)
    (hv : s'.val.2 = T.reset l.resets s.val.2) : s = s' := by
  apply Subtype.ext
  apply Prod.ext hm
  rw [hr, T.reset_empty] at hv
  exact hv.symm

/-- Fixing the compatible clock valuation fixes the whole automaton valuation:
tableau resets already preserve real variables and the global clock. -/
theorem reset_fixes_of_clockCompatible (T : Tableau Clock Var State)
    (Λ : ClockResetSet Clock) {v : T.HAVar → ℝ} {α : ClockValuation Clock}
    (hv : T.ClockCompatible v α) (hfix : Λ.apply α = α) : T.reset Λ v = v := by
  funext x
  cases x with
  | inl => rfl
  | inr x =>
    cases x with
    | inr => rfl
    | inl c =>
      have hc := T.reset_clockCompatible Λ hv c
      rw [hfix] at hc
      exact hc.trans (hv c).symm

theorem fixed_reset_jump_endpoints (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    (s s' : (T.toAutomaton h τ hτ).State) (l : EdgeLabel Clock)
    (α : ClockValuation Clock) (hc : T.ClockCompatible s.val.2 α)
    (hm : s.val.1 = s'.val.1) (hfix : l.resets.apply α = α)
    (hv : s'.val.2 = T.reset l.resets s.val.2) : s = s' := by
  apply Subtype.ext
  apply Prod.ext hm
  rw [T.reset_fixes_of_clockCompatible l.resets hc hfix] at hv
  exact hv.symm

theorem jump_block_erase_identity (T : Tableau Clock Var State)
    (h : T.TranslationReady) (τ : ℝ) (hτ : 0 < τ)
    {a s s' b : (T.toAutomaton h τ hτ).State} (l : EdgeLabel Clock)
    (hpre : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep a s)
    (hpost : Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep s' b)
    (hm : s.val.1 = s'.val.1) (hr : l.resets = ClockResetSet.empty)
    (hv : s'.val.2 = T.reset l.resets s.val.2) :
    Relation.ReflTransGen (T.toAutomaton h τ hτ).DiscreteStep a b := by
  have heq := T.identity_jump_endpoints h τ hτ s s' l hm hr hv
  subst s'
  exact hpre.trans hpost

end Tableau
end STLTableau.Section4
