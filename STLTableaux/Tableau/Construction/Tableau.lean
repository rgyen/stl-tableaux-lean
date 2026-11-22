import STLTableaux.Closure.Correctness.ClosureSoundness

/-! Tableaux, paths, traces and recognition (Definitions 4.23–4.27). -/
namespace STLTableau.Section4
open Section3
variable {Clock Var State : Type*}

structure EdgeLabel (Clock : Type*) where
  guards : Set (Guard Clock)
  guards_finite : guards.Finite
  resets : ClockResetSet Clock

/-- Definition 4.23 (tableau). State labels contain atomic judgements. -/
structure Tableau (Clock Var State : Type*) where
  realVariables : Set Var
  clocks : Set Clock
  states : Set State
  edges : Set (State × EdgeLabel Clock × State)
  initial : Set (EdgeLabel Clock × State)
  final : Set State
  label : State → Set (Local Clock Var)
  label_atomic : ∀ s l, l ∈ label s → Section3.TransitionForm.KeepAtomic l

/-- A finite trace has a last frame with no successor trace. -/
inductive Trace (Clock Var : Type*) where
  | last (frame : Section3.StateForm Clock Var)
  | step (frame : Section3.StateForm Clock Var) (tail : Trace Clock Var)

namespace Trace

def holdsWith (labels : Section3.StateForm Clock Var → Set (Local Clock Var))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Trace Clock Var → Prop
  | .last S => (∀ g ∈ S.guards, g.holds α) ∧
      ∀ l ∈ labels S, l.holds σ P (S.resets.apply α) k
  | .step S t => ((∀ g ∈ S.guards, g.holds α) ∧
      ∀ l ∈ labels S, l.holds σ P (S.resets.apply α) k) ∧
      if hk : k.1 < P.size then
        holdsWith labels σ P
          (ClockResetSet.elapse (S.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1, hk⟩)) ⟨k.1+1, by omega⟩ t
      else False

def holds := @holdsWith Clock Var Section3.StateForm.locals

def length : Trace Clock Var → ℕ
  | .last _ => 1
  | .step _ t => t.length + 1

def freeClocks : Trace Clock Var → Set Clock
  | .last S => S.freeClocks
  | .step S t => S.guardClocks ∪ ((S.localClocks ∪ t.freeClocks) \ S.resets.clocks)

/-- Initial valuations matter only at free occurrences, including across next. -/
theorem holds_congr_of_agree (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ t.freeClocks, α c = β c) :
    t.holds σ P α k ↔ t.holds σ P β k := by
  induction t generalizing α β k with
  | last S => exact S.holds_congr_of_agree σ P α β k hagree
  | step S t ih =>
      have hs : ∀ c ∈ S.freeClocks, α c = β c := by
        intro c hc
        apply hagree c
        rcases hc with hc | ⟨hc, hn⟩
        · exact Or.inl hc
        · exact Or.inr ⟨Or.inl hc, hn⟩
      simp only [holds, holdsWith]
      apply and_congr (S.holds_congr_of_agree σ P α β k hs)
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk]
        apply ih
        intro c hc
        have he : S.resets.apply α c = S.resets.apply β c := by
          cases hr : S.resets.value c with
          | some a => simp [ClockResetSet.apply, hr]
          | none =>
              have hn : c ∉ S.resets.clocks := by
                rintro ⟨a, ha⟩
                rw [hr] at ha
                cases ha
              have ha := hagree c (Or.inr ⟨Or.inr hc, hn⟩)
              simp [ClockResetSet.apply, hr, ha]
        simpa only [ClockResetSet.elapse] using congrArg
          (fun x => x + STLTableau.Judgement.duration P ⟨k.1, hk⟩) he
      · simp only [dif_neg hk]

theorem holds_independent_of_initial_clocks (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (t : Trace Clock Var) (hclosed : t.freeClocks = ∅)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    t.holds σ P α k ↔ t.holds σ P β k :=
  t.holds_congr_of_agree σ P α β k (by simp [hclosed])

theorem length_pos (t : Trace Clock Var) : 0 < t.length := by
  cases t <;> simp [length]

/-- A satisfied trace cannot take next steps beyond the terminal position. -/
theorem length_le_remaining (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (t : Trace Clock Var) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : t.holds σ P α k) :
    k.1 + t.length ≤ P.size + 1 := by
  induction t generalizing α k with
  | last S => have hk := k.isLt; simp only [length]; omega
  | step S t ih =>
      change _ ∧ (if hk : k.1 < P.size then _ else False) at hs
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs
        have h := ih _ _ hs.2
        change (k.1 + 1) + t.length ≤ P.size + 1 at h
        simp only [length]
        omega
      · simp only [dif_neg hk] at hs
        exact hs.2.elim

/-- A satisfied trace remains satisfied when local judgements are removed. -/
theorem holdsWith_mono {labels more : Section3.StateForm Clock Var → Set (Local Clock Var)}
    (hsub : ∀ S, labels S ⊆ more S)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (t : Trace Clock Var) :
    t.holdsWith more σ P α k → t.holdsWith labels σ P α k := by
  induction t generalizing α k with
  | last S =>
      simp only [holdsWith]
      exact fun h => ⟨h.1, fun l hl => h.2 l (hsub S hl)⟩
  | step S t ih =>
      simp only [holdsWith]
      intro h
      refine ⟨⟨h.1.1, fun l hl => h.1.2 l (hsub S hl)⟩, ?_⟩
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk]
        exact ih _ _ (by simpa only [dif_pos hk] using h.2)
      · simpa only [dif_neg hk] using h.2

/-- Semantic label equivalence lifts without changing guards or clock bindings. -/
theorem holdsWith_congr {labels more : Section3.StateForm Clock Var → Set (Local Clock Var)}
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (heq : ∀ S α k,
      (∀ l ∈ labels S, l.holds σ P α k) ↔ (∀ l ∈ more S, l.holds σ P α k))
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (t : Trace Clock Var) :
    t.holdsWith labels σ P α k ↔ t.holdsWith more σ P α k := by
  induction t generalizing α k with
  | last S =>
      simp only [holdsWith]
      exact and_congr Iff.rfl (heq S _ _)
  | step S t ih =>
      simp only [holdsWith]
      apply and_congr (and_congr Iff.rfl (heq S _ _))
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk]
        exact ih _ _
      · simp only [dif_neg hk]

end Trace

/-- A sequence of incoming transition labels and states. `valid` checks the
transitions required by Definition 4.24 (path). -/
inductive Path (Clock State : Type*) where
  | last (incoming : EdgeLabel Clock) (state : State)
  | step (incoming : EdgeLabel Clock) (state : State) (tail : Path Clock State)

namespace Path
def firstState : Path Clock State → State
  | .last _ s | .step _ s _ => s
def firstIncoming : Path Clock State → EdgeLabel Clock
  | .last e _ | .step e _ _ => e
def lastState : Path Clock State → State
  | .last _ s => s
  | .step _ _ t => t.lastState

def valid (T : Tableau Clock Var State) : Path Clock State → Prop
  | .last _ s => s ∈ T.states
  | .step _ s t => s ∈ T.states ∧ t.valid T ∧
      (s, t.firstIncoming, t.firstState) ∈ T.edges

def accepting (p : Path Clock State) (T : Tableau Clock Var State) : Prop :=
  p.valid T ∧ p.lastState ∈ T.final

def run (p : Path Clock State) (T : Tableau Clock Var State) : Prop :=
  p.valid T ∧ (p.firstIncoming, p.firstState) ∈ T.initial

/-- Definition 4.25 (trace). The incoming clock reset scopes the state label
and the next trace, if present. -/
def trace (labels : State → Set (Local Clock Var))
    (hfinite : ∀ s, (labels s).Finite) : Path Clock State → Trace Clock Var
  | .last e s => .last ⟨e.guards, e.guards_finite, e.resets, labels s, hfinite s⟩
  | .step e s t => .step ⟨e.guards, e.guards_finite, e.resets, labels s, hfinite s⟩
      (t.trace labels hfinite)
end Path

/-- Definition 4.27 (recognition). The signal satisfies the trace of one
accepting run at position zero for every initial clock valuation. -/
def Tableau.recognizes (T : Tableau Clock Var State)
    (hfinite : ∀ s, (T.label s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) : Prop :=
  ∃ p : Path Clock State, p.run T ∧ p.accepting T ∧
    ∀ α : ClockValuation Clock,
      (p.trace T.label hfinite).holds σ P α ⟨0, by omega⟩

/-- An accepting run with a satisfied trace and no free clocks witnesses
recognition for every initial clock valuation. -/
theorem Tableau.recognizes_of_closed_trace (T : Tableau Clock Var State)
    (hfinite : ∀ s, (T.label s).Finite)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (p : Path Clock State) (hr : p.run T) (ha : p.accepting T)
    (hclosed : (p.trace T.label hfinite).freeClocks = ∅)
    (α : ClockValuation Clock)
    (hs : (p.trace T.label hfinite).holds σ P α ⟨0, by omega⟩) :
    T.recognizes hfinite σ P := by
  refine ⟨p, hr, ha, ?_⟩
  intro β
  exact ((p.trace T.label hfinite).holds_independent_of_initial_clocks
    σ P hclosed α β ⟨0, by omega⟩).1 hs

end STLTableau.Section4
