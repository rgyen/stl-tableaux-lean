import STLTableaux.Automata.Translation.CanonicalTableauExecution
import STLTableaux.Automata.Recognition.ForwardVisits
import STLTableaux.Tableau.Traces.TracePrefixTransport
import STLTableaux.Automata.Recognition.PrelimBoundedPartition
import STLTableaux.Automata.Composition.SystemTableauFlowLift
import STLTableaux.Automata.Composition.CanonicalTableauComposition

/-! Realize the accepting path of a recognizing partition. The standalone
translation uses its original boundary times; the synchronized construction
also certifies compatibility with the induced partition. -/

namespace STLTableau.IntervalPartition

/-- Keep every earlier interval unchanged and extend only a last, unconstrained
singleton to a positive flow.  No canonical marker rule on preceding pieces. -/
private theorem exists_extend_singleton_to_horizon {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (k : Fin P.size)
    (hsingle : (P.interval k).left = (P.interval k).right) :
    ∃ Q : IntervalPartition σ.domain, ∃ hn : k.val+1 = Q.size,
      (∀ j : Fin P.size, (hj : j.val < k.val) →
        Q.interval ⟨j.val, by omega⟩ = P.interval j) ∧
      Q.interval ⟨k.val, by omega⟩ = ⟨(P.interval k).left, σ.horizon, ●, ○⟩ := by
  classical
  let n := k.val+1
  let J (i : Fin n) : MarkedInterval :=
    if hi : i.val < k.val then P.interval ⟨i.val,hi.trans k.isLt⟩
    else ⟨(P.interval k).left,σ.horizon,●,○⟩
  have member (i : Fin P.size) {x : ℝ} (hx : x ∈ P.interval i) : x ∈ σ.domain := by
    rw [← P.covers]
    exact Set.mem_iUnion.mpr ⟨i,hx⟩
  have point : (P.interval k).left ∈ P.interval k := by
    have hs := P.carrier_eq_singleton_of_endpoints_eq k hsingle.symm
    change (P.interval k).left ∈ (P.interval k).carrier
    rw [hs]
    exact Set.mem_singleton _
  have ends := member k point
  let Q : IntervalPartition σ.domain := {
    size := n
    interval := J
    nonempty := by
      intro i
      unfold J
      split
      · exact P.nonempty _
      · rw [MarkedInterval.carrier_eq]
        exact Set.nonempty_Ico.mpr ends.2
    pairwiseDisjoint := by
      intro i j hne
      apply Set.disjoint_left.mpr
      intro x hx hy
      change x ∈ (J i).carrier at hx
      change x ∈ (J j).carrier at hy
      unfold J at hx hy
      split at hx <;> split at hy
      next hi hj =>
        apply Set.disjoint_left.mp (P.pairwiseDisjoint (i := ⟨i.val,hi.trans k.isLt⟩)
          (j := ⟨j.val,hj.trans k.isLt⟩) (fun he => hne (Fin.ext
            (congrArg (fun a : Fin P.size => a.val) he)))) hx hy
      next hi hj =>
        have hi' := P.ordered (show (⟨i.val, hi.trans k.isLt⟩ : Fin P.size) < k from hi)
        have hy' : (P.interval k).left ≤ x := MarkedInterval.left_le_of_mem
          (I := ⟨(P.interval k).left,σ.horizon,●,○⟩) hy
        have he : x = (P.interval k).left := le_antisymm
          ((MarkedInterval.le_right_of_mem hx).trans hi') hy'
        exact Set.disjoint_left.mp (P.pairwiseDisjoint (ne_of_lt hi)) (he ▸ hx) point
      next hi hj =>
        have hj' := P.ordered (show (⟨j.val, hj.trans k.isLt⟩ : Fin P.size) < k from hj)
        have hx' : (P.interval k).left ≤ x := MarkedInterval.left_le_of_mem
          (I := ⟨(P.interval k).left,σ.horizon,●,○⟩) hx
        have he : x = (P.interval k).left := le_antisymm
          ((MarkedInterval.le_right_of_mem hy).trans hj') hx'
        exact Set.disjoint_left.mp (P.pairwiseDisjoint (ne_of_lt hj)) (he ▸ hy) point
      next hi hj => exact hne (Fin.ext (by dsimp [n] at i j; omega))
    covers := by
      ext x
      rw [Set.mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        change x ∈ (J i).carrier at hi
        unfold J at hi
        split at hi
        · exact member _ hi
        · rw [MarkedInterval.carrier_eq] at hi
          exact ⟨ends.1.trans hi.1,hi.2⟩
      · intro hx
        by_cases hleft : x < (P.interval k).left
        · have xmem := hx
          rw [← P.covers, Set.mem_iUnion] at xmem
          obtain ⟨i,hi⟩ := xmem
          have hbefore : i.val < k.val := by
            by_contra! he
            rcases lt_or_eq_of_le he with gt | eq
            · exact hleft.not_ge ((hsingle.le.trans (P.ordered (show k < i from gt))).trans
                (MarkedInterval.left_le_of_mem hi))
            · exact hleft.not_ge ((Fin.ext eq.symm : i = k) ▸ MarkedInterval.left_le_of_mem hi)
          refine ⟨⟨i.val,by dsimp [n]; omega⟩,?_⟩
          simpa only [J,dif_pos hbefore] using hi
        · refine ⟨⟨k.val,by dsimp [n]; omega⟩,?_⟩
          simpa only [J,dif_neg (lt_irrefl k.val),MarkedInterval.carrier_eq]
            using (show x ∈ Set.Ico (P.interval k).left σ.horizon from ⟨le_of_not_gt hleft,hx.2⟩)
    ordered := by
      intro i j hij
      unfold J
      have hv : i.val < j.val := hij
      split_ifs with hi hj
      · exact P.ordered hv
      · exact P.ordered hi
      · omega
      · have hj' := j.isLt
        dsimp [n] at hj'
        omega }
  refine ⟨Q,rfl,?_,?_⟩
  · intro j hj
    simp only [Q,J,dif_pos hj]
  · simp only [Q,J,dif_neg (lt_irrefl k.val)]

end STLTableau.IntervalPartition

namespace STLTableau.Section4
open Section3
variable {Clock Var State : Type*}

namespace Path

def edgesCount : Path Clock State → ℕ
  | .last _ _ => 0
  | .step _ _ tail => tail.edgesCount + 1

private def incomingAt : (p : Path Clock State) → Fin (p.edgesCount+1) → EdgeLabel Clock
  | .last l _, _ => l
  | .step l _ p, i => Fin.cases l p.incomingAt i

private def stateAt : (p : Path Clock State) → Fin (p.edgesCount+1) → State
  | .last _ q, _ => q
  | .step _ q p, i => Fin.cases q p.stateAt i

private theorem ofIndexed_self (p : Path Clock State) :
    Path.ofIndexed p.edgesCount p.incomingAt p.stateAt = p := by
  induction p with
  | last => rfl
  | step l q p ih =>
    change Path.step l q (Path.ofIndexed p.edgesCount p.incomingAt p.stateAt) = _
    rw [ih]

private theorem valid_stateAt {T : Tableau Clock Var State} (p : Path Clock State)
    (hv : p.valid T) (i : Fin (p.edgesCount+1)) : p.stateAt i ∈ T.states := by
  induction p with
  | last => exact hv
  | step l q p ih =>
    exact Fin.cases (motive := fun j => (Path.step l q p).stateAt j ∈ T.states)
      hv.1 (fun j => ih hv.2.1 j) i

private theorem incoming_zero (p : Path Clock State) : p.incomingAt 0 = p.firstIncoming := by
  cases p <;> rfl

private theorem state_zero (p : Path Clock State) : p.stateAt 0 = p.firstState := by
  cases p <;> rfl

private theorem state_last (p : Path Clock State) : p.stateAt (Fin.last p.edgesCount) = p.lastState := by
  rw [← Path.ofIndexed_lastState p.edgesCount p.incomingAt p.stateAt, p.ofIndexed_self]

private theorem valid_edgeAt {T : Tableau Clock Var State} (p : Path Clock State)
    (hv : p.valid T) (i : Fin p.edgesCount) :
    (p.stateAt i.castSucc,p.incomingAt i.succ,p.stateAt i.succ) ∈ T.edges := by
  induction p with
  | last => exact Fin.elim0 i
  | step l q p ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (q,p.incomingAt 0,p.stateAt 0) ∈ T.edges
      simpa only [p.incoming_zero,p.state_zero] using hv.2.2
    · exact ih hv.2.1 j

private theorem trace_length (p : Path Clock State) (T : Tableau Clock Var State)
    (hf : ∀ s, (T.label s).Finite) : (p.trace T.label hf).length = p.edgesCount+1 := by
  have hh := Path.ofIndexed_trace_length T.label hf p.edgesCount p.incomingAt p.stateAt
  rw [p.ofIndexed_self] at hh
  exact hh

private theorem trace_schedule {T : Tableau Clock Var State} (p : Path Clock State)
    (hf : ∀ s, (T.label s).Finite) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (sat : (p.trace T.label hf).holds σ P α k) :
    ∃ ν : Fin (p.edgesCount+1) → ClockValuation Clock,
      ∃ length : k.val + p.edgesCount ≤ P.size, ν 0 = α ∧
      (∀ i, ∀ g ∈ (p.incomingAt i).guards, g.holds (ν i)) ∧
      (∀ i, ∀ l ∈ T.label (p.stateAt i),
        l.holds σ P ((p.incomingAt i).resets.apply (ν i)) ⟨k.val+i.val,by
          have := i.isLt; omega⟩) ∧
      (∀ i : Fin p.edgesCount, ν i.succ = ClockResetSet.elapse
        ((p.incomingAt i.castSucc).resets.apply (ν i.castSucc))
        (STLTableau.Judgement.duration P ⟨k.val+i.val,by have := i.isLt; omega⟩)) := by
  induction p generalizing α k with
  | last l q =>
    have length : k.val + (Path.last l q).edgesCount ≤ P.size := by
      have := k.isLt
      change k.val + 0 ≤ P.size
      omega
    refine ⟨fun _ => α,length,rfl,fun _ => sat.1,?_,?_⟩
    · intro i
      have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      change ∀ a ∈ T.label q, a.holds σ P (l.resets.apply α) ⟨k.val+i.val,_⟩
      simpa only [hi,Nat.add_zero] using sat.2
    · intro i; exact Fin.elim0 i
  | step l q p ih =>
    have hk : k.val < P.size := by
      by_contra hn
      have hbad := sat.2
      simp only [dif_neg hn] at hbad
    let next := ClockResetSet.elapse (l.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val,hk⟩)
    have ht : (p.trace T.label hf).holds σ P next ⟨k.val+1,by omega⟩ := by
      have tail := sat.2
      rw [dif_pos hk] at tail
      exact tail
    obtain ⟨ν,hlen,ν0,hg,hl,hn⟩ := ih next ⟨k.val+1,by omega⟩ ht
    have length : k.val + (Path.step l q p).edgesCount ≤ P.size := by
      change k.val + 1 + p.edgesCount ≤ P.size at hlen
      change k.val + (p.edgesCount + 1) ≤ P.size
      omega
    refine ⟨Fin.cases α ν,length,rfl,?_,?_,?_⟩
    · intro i
      refine Fin.cases sat.1.1 (fun j => hg j) i
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change ∀ a ∈ T.label q, a.holds σ P (l.resets.apply α) ⟨k.val+0,_⟩
        simpa only [Nat.add_zero] using sat.1.2
      · change ∀ a ∈ T.label (p.stateAt j), a.holds σ P
          ((p.incomingAt j).resets.apply (ν j)) ⟨k.val+(j.val+1),_⟩
        simpa only [Nat.add_assoc,Nat.add_comm 1 j.val] using hl j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change ν 0 = ClockResetSet.elapse (l.resets.apply α) (STLTableau.Judgement.duration P ⟨k.val+0,_⟩)
        simpa only [Nat.add_zero] using ν0
      · change ν j.succ = ClockResetSet.elapse ((p.incomingAt j.castSucc).resets.apply (ν j.castSucc))
          (STLTableau.Judgement.duration P ⟨k.val+(j.val+1),_⟩)
        simpa only [Nat.add_assoc,Nat.add_comm 1 j.val] using hn j

end Path

namespace Tableau
open HybridAutomaton
variable (T : Tableau Clock Var State) (h : T.TranslationReady)
variable (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
local notation "A" => T.canonicalAutomaton h σ.horizon

/-- A positive interval starts open precisely when the preceding piece is
a singleton. The first piece is closed by ordinary partition geometry. -/
def CanonicalBoundaryForms : Prop :=
  ∀ i : Fin (P.size-1),
    (P.interval ⟨i.val+1,by have := i.isLt; omega⟩).leftBoundary =
      if (P.interval ⟨i.val,by have := i.isLt; omega⟩).left =
          (P.interval ⟨i.val,by have := i.isLt; omega⟩).right then ○ else ●

private def visitValue (t : ℝ) (α : ClockValuation Clock) (x : Var → ℝ) : T.HAVar → ℝ
  | .inl v => x v.val
  | .inr (.inl c) => α c.val
  | .inr (.inr ()) => t

private def curveValue (s : T.HAVar → ℝ) (u : ℝ) (x : T.realVariables → ℝ) : T.HAVar → ℝ
  | .inl v => x v
  | .inr c => s (.inr c) + u

private theorem invariant_of_atoms (q : T.states) (v : T.HAVar → ℝ)
    (bound : v T.globalClock ≤ σ.horizon)
    (atoms : ∀ a, Local.predicate (.plain (.atom a)) ∈ T.label q.val → T.atomHolds a v) :
    (q,v) ∈ (A).invariant := ⟨atoms,fun _ => bound⟩

private structure Schedule where
  n : ℕ
  nonempty : 0 < n
  count : n ≤ P.size
  last_positive : 0 < STLTableau.Judgement.duration P ⟨n-1,by omega⟩
  q : Fin n → T.states
  incoming : Fin n → EdgeLabel Clock
  ν : Fin n → ClockValuation Clock
  initial : (incoming ⟨0,nonempty⟩,(q ⟨0,nonempty⟩).val) ∈ T.initial
  edge : ∀ j : Fin (n-1),
    ((q ⟨j.val,by have := j.isLt; omega⟩).val,
      incoming ⟨j.val+1,by have := j.isLt; omega⟩,
      (q ⟨j.val+1,by have := j.isLt; omega⟩).val) ∈ T.edges
  guards : ∀ i, ∀ g ∈ (incoming i).guards, g.holds (ν i)
  labels : ∀ i, ∀ l ∈ T.label (q i).val,
    l.holds σ P ((incoming i).resets.apply (ν i)) ⟨i.val,by have := i.isLt; omega⟩
  clock_step : ∀ j : Fin (n-1), ν ⟨j.val+1,by have := j.isLt; omega⟩ =
    ClockResetSet.elapse ((incoming ⟨j.val,by have := j.isLt; omega⟩).resets.apply
      (ν ⟨j.val,by have := j.isLt; omega⟩))
      (STLTableau.Judgement.duration P ⟨j.val,by have := j.isLt; omega⟩)
  final : q ⟨n-1,by omega⟩ ∈ T.goalModes ∨ n = P.size ∧ ∃ (l : EdgeLabel Clock) (s : T.states),
    ((q ⟨n-1,by omega⟩).val,l,s.val) ∈ T.edges ∧ T.EndGoal s ∧
    ∀ g ∈ l.guards, g.holds (ClockResetSet.elapse
      ((incoming ⟨n-1,by omega⟩).resets.apply (ν ⟨n-1,by omega⟩))
      (STLTableau.Judgement.duration P ⟨n-1,by omega⟩))

/-- A last empty-labelled visit need not remain a singleton: it can observe
the following positive piece without an extra jump. Only its (unused) right
endpoint changes; all earlier guards still use their original durations. -/
private theorem empty_last_schedule (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (run : p.run T) (acc : p.accepting T)
    (sat : (p.trace T.label hf).holds σ P (fun _ => 0) ⟨0,by omega⟩)
    (canonical : CanonicalBoundaryForms σ P) (hi : p.edgesCount < P.size)
    (empty : T.states) (heLab : T.label empty.val = ∅) (lastEmpty : p.lastState = empty.val)
    (stop : ℝ) (hstop : (P.interval ⟨p.edgesCount,hi⟩).left < stop)
    (hle : stop ≤ σ.horizon) :
    ∃ (Q : IntervalPartition σ.domain) (s : Schedule T σ Q), CanonicalBoundaryForms σ Q ∧
      s.n = p.edgesCount+1 ∧
      (∀ (i : Fin s.n) (before : i.val < p.edgesCount),
        Q.interval ⟨i.val,i.isLt.trans_le s.count⟩ = P.interval ⟨i.val,before.trans hi⟩) ∧
      ∀ (i : Fin s.n), i.val = p.edgesCount →
        (Q.interval ⟨i.val,i.isLt.trans_le s.count⟩).left = (P.interval ⟨p.edgesCount,hi⟩).left ∧
        (Q.interval ⟨i.val,i.isLt.trans_le s.count⟩).right = stop := by
  classical
  let k := p.edgesCount
  have hk : k < P.size := hi
  have boundary (i : Fin k) (hi' : i.val+1 < P.size) :
      (P.interval ⟨i.val+1,hi'⟩).leftBoundary =
        if (P.interval ⟨i.val,by omega⟩).left = (P.interval ⟨i.val,by omega⟩).right then ○ else ● := by
    exact canonical ⟨i.val,by omega⟩
  let b (i : Fin (k+2)) : ℝ := Fin.lastCases (motive := fun _ => ℝ) stop
    (fun j => (P.interval ⟨j.val,by have := j.isLt; omega⟩).left) i
  have left (i : Fin (k+1)) : b i.castSucc = (P.interval ⟨i.val,by have := i.isLt; omega⟩).left := by
    simp [b]
  have right (i : Fin k) : b i.castSucc.succ = (P.interval ⟨i.val,by omega⟩).right := by
    change b i.succ.castSucc = _
    rw [left]
    exact (P.adjacent_right_eq_left ⟨i.val,by omega⟩ (show i.val+1 < P.size by omega)).symm
  have b0 : b 0 = 0 := (left 0).trans (P.first_left_eq_domain_left (by omega) σ.horizon_pos)
  have bend : b (Fin.last (k+1)) = stop := by simp [b]
  have pos : b (Fin.last k).castSucc < stop := (left (Fin.last k)).symm ▸ hstop
  have mono : Monotone b := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [show (Fin.last k).succ = Fin.last (k+1) from rfl,bend]
      exact pos.le
    · rw [left,right]
      exact P.left_le_right _
  have isolated : IntervalPartition.IsolatedSingletons b := by
    intro i hi' hz hz'
    let j : Fin (k+1) := ⟨i.val+1,hi'⟩
    by_cases hj : j.val < k
    · have hjk : i.val+1 < k := hj
      let a : Fin k := ⟨i.val,by omega⟩
      let c : Fin k := ⟨j.val,hj⟩
      have hP : i.val+1 < P.size := hjk.trans hk
      have z : (P.interval ⟨i.val,by omega⟩).right = (P.interval ⟨i.val,by omega⟩).left :=
        (right a).symm.trans (hz.symm.trans (left i))
      have z' : (P.interval ⟨i.val+1,hP⟩).right = (P.interval ⟨i.val+1,hP⟩).left :=
        (right c).symm.trans (hz'.symm.trans (left j))
      exact P.adjacent_not_both_zero_width ⟨i.val,by omega⟩ hP z z'
    · have hj' : j = Fin.last k := Fin.ext (by
        change ¬ i.val+1 < k at hj
        change i.val+1 = k
        omega)
      change b j.castSucc = b j.succ at hz'
      rw [hj',show (Fin.last k).succ = Fin.last (k+1) from rfl,bend] at hz'
      exact pos.ne hz'
  have lastPos : ∀ i : Fin (k+1), i.val+1 = k+1 → b i.castSucc ≠ b i.succ := by
    intro i hi'
    have he : i = Fin.last k := Fin.ext (by simp; omega)
    rw [he,show (Fin.last k).succ = Fin.last (k+1) from rfl,bend]
    exact pos.ne
  obtain ⟨R,counts,pieces,all,suffix⟩ := IntervalPartition.completeVisitBounds b mono
    (IntervalPartition.singletonMarkers b) (IntervalPartition.singletonMarkers_compatible b isolated)
    (IntervalPartition.singletonMarkers_first b) (IntervalPartition.singletonMarkers_last b lastPos)
    (bend.symm ▸ hle)
  let Q : IntervalPartition σ.domain := { R with
    covers := by
      rw [R.covers]
      change Set.Ico (b 0) σ.horizon = Set.Ico 0 σ.horizon
      rw [b0] }
  let jQ (i : Fin (k+1)) : Fin Q.size := ⟨i.val,i.isLt.trans_le counts⟩
  have geometry (i : Fin (k+1)) : Q.interval (jQ i) =
      IntervalPartition.markedBoundaryPiece b (IntervalPartition.singletonMarkers b) i := pieces i
  have duration (i : Fin k) : STLTableau.Judgement.duration Q (jQ i.castSucc) =
      STLTableau.Judgement.duration P ⟨i.val,by have := i.isLt; omega⟩ := by
    apply Subtype.ext
    change (Q.interval (jQ i.castSucc)).right - (Q.interval (jQ i.castSucc)).left = _
    rw [geometry]
    change b i.castSucc.succ - b i.castSucc.castSucc = _
    rw [left,right]
    rfl
  have same (i : Fin k) : Q.interval (jQ i.castSucc) = P.interval ⟨i.val,by have := i.isLt; omega⟩ := by
    have leftMark (j : Fin (k+1)) : (Q.interval (jQ j)).leftBoundary = (P.interval ⟨j.val,by omega⟩).leftBoundary := by
      rw [geometry]
      obtain ⟨n,hn⟩ := j
      cases n with
      | zero =>
        exact (IntervalPartition.singletonMarkers_first b).trans
          (P.first_leftBoundary_closed (by omega) σ.horizon_pos).symm
      | succ n =>
        let i : Fin k := ⟨n,by omega⟩
        change IntervalPartition.singletonMarkers b ⟨i.castSucc.val+1,by omega⟩ = _
        rw [IntervalPartition.singletonMarkers_succ b i.castSucc]
        change (if b i.castSucc.castSucc = b i.castSucc.succ then ○ else ●) = _
        rw [left,right]
        exact (boundary i (by omega)).symm
    have rightMark : (Q.interval (jQ i.castSucc)).rightBoundary =
        (P.interval ⟨i.val,by have := i.isLt; omega⟩).rightBoundary := by
      have hQ : i.castSucc.val+1 < Q.size := (Nat.succ_lt_succ i.isLt).trans_le counts
      have hP : i.val+1 < P.size := (Nat.succ_le_of_lt i.isLt).trans_lt hk
      rw [Q.adjacent_rightBoundary_eq_complement_leftBoundary (jQ i.castSucc) hQ,
        P.adjacent_rightBoundary_eq_complement_leftBoundary ⟨i.val,by omega⟩ hP]
      exact congrArg Marker.complement (leftMark i.succ)
    cases hq : Q.interval (jQ i.castSucc)
    cases hp : P.interval ⟨i.val,by have := i.isLt; omega⟩
    have hl : (Q.interval (jQ i.castSucc)).left = (P.interval ⟨i.val,by omega⟩).left := by
      rw [geometry]; exact left i.castSucc
    have hr := right i
    have hr' : (Q.interval (jQ i.castSucc)).right = (P.interval ⟨i.val,by omega⟩).right := by
      rw [geometry]
      exact hr
    have hm : (Q.interval (jQ i.castSucc)).leftBoundary =
        (P.interval ⟨i.val,by omega⟩).leftBoundary := leftMark i.castSucc
    simp only [hq,hp] at hl hr' hm rightMark
    congr
  obtain ⟨ν,_,_,guards,labels,step⟩ := p.trace_schedule hf σ P (fun _ => 0) ⟨0,by omega⟩ sat
  refine ⟨Q,{
    n := k+1
    nonempty := Nat.succ_pos _
    count := counts
    last_positive := ?_
    q := fun i => ⟨p.stateAt i,p.valid_stateAt run.1 i⟩
    incoming := p.incomingAt
    ν := ν
    initial := ?_
    edge := ?_
    guards := guards
    labels := ?_
    clock_step := ?_
    final := ?_ },?_,rfl,?_,?_⟩
  · change 0 < STLTableau.Judgement.duration Q (jQ (Fin.last k))
    have realPos : 0 < (STLTableau.Judgement.duration Q (jQ (Fin.last k)) : ℝ) := by
      change 0 < (Q.interval (jQ (Fin.last k))).right - (Q.interval (jQ (Fin.last k))).left
      rw [geometry (Fin.last k)]
      change 0 < b (Fin.last (k+1)) - b (Fin.last k).castSucc
      rw [bend]
      exact sub_pos.mpr pos
    exact realPos
  · change (p.incomingAt 0,p.stateAt 0) ∈ T.initial
    rw [p.incoming_zero,p.state_zero]
    exact run.2
  · intro i; exact p.valid_edgeAt run.1 ⟨i.val,by have := i.isLt; change i.val < k+1-1 at this; omega⟩
  · intro i l hl
    by_cases hi' : i.val < k
    · let j : Fin k := ⟨i.val,hi'⟩
      have hp : i.val < P.size := by omega
      apply (local_holds_of_same_interval σ P Q _ ⟨i.val,by omega⟩
        ⟨i.val, Nat.lt_succ_of_lt (i.isLt.trans_le counts)⟩ hp
        (i.isLt.trans_le counts) (same j).symm l).1
      have hs := labels i l hl
      simpa only [Fin.val_zero,Nat.zero_add] using hs
    · have he : i = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
      change l ∈ T.label (p.stateAt i) at hl
      rw [he,p.state_last,lastEmpty,heLab] at hl
      exact hl.elim
  · intro i
    let j : Fin k := ⟨i.val,by have := i.isLt; change i.val < k+1-1 at this; omega⟩
    have hd := duration j
    change STLTableau.Judgement.duration Q ⟨i.val,(Nat.lt_of_lt_of_le j.isLt
      (Nat.le_succ k)).trans_le counts⟩ = _ at hd
    rw [hd]
    have hs := step j
    simp only [Nat.zero_add] at hs
    exact hs
  · exact Or.inl (by change p.stateAt (Fin.last k) ∈ T.final; rw [p.state_last]; exact acc.2)
  · intro i
    have h_i : i.val+1 < Q.size := by have := i.isLt; omega
    by_cases hj : i.val+1 < k+1
    · let j : Fin (k+1) := ⟨i.val,by omega⟩
      let next : Fin (k+1) := ⟨i.val+1,hj⟩
      change (Q.interval (jQ next)).leftBoundary = _
      rw [geometry next]
      change IntervalPartition.singletonMarkers b ⟨j.val+1,by omega⟩ = _
      rw [show Q.interval ⟨i.val,by omega⟩ = Q.interval (jQ j) from rfl, geometry j]
      exact IntervalPartition.singletonMarkers_succ b j
    · change i.val+1 < R.size at h_i
      have lt : stop < σ.horizon := by
        by_contra! notLt
        have count := all (bend.trans (le_antisymm hle notLt))
        omega
      obtain ⟨idx,count,lastPiece⟩ := suffix (bend.trans_lt lt)
      have lastIdx : i.val = k := by omega
      let j : Fin (k+1) := ⟨i.val,by omega⟩
      have bound : (Q.interval (jQ j)).left ≠ (Q.interval (jQ j)).right := by
        rw [geometry j]
        exact lastPos j (by dsimp [j]; omega)
      change (Q.interval ⟨i.val+1,h_i⟩).leftBoundary =
        if (Q.interval (jQ j)).left = (Q.interval (jQ j)).right then ○ else ●
      rw [if_neg bound,show Q.interval ⟨i.val+1,h_i⟩ = R.interval ⟨k+1,idx⟩ from
        congrArg R.interval (Fin.ext (by change i.val+1 = k+1; omega)),lastPiece]
  · intro i before
    exact same ⟨i.val,before⟩
  · intro i hi'
    rw [geometry i]
    have eq : i = Fin.last k := Fin.ext hi'
    exact ⟨eq ▸ left (Fin.last k),by rw [eq]; exact bend⟩

/-- Only the endpoint of the last empty-labelled singleton changes. -/
private theorem empty_last_raw_schedule (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (run : p.run T) (acc : p.accepting T)
    (sat : (p.trace T.label hf).holds σ P (fun _ => 0) ⟨0,by omega⟩)
    (hi : p.edgesCount < P.size)
    (single : (P.interval ⟨p.edgesCount,hi⟩).left = (P.interval ⟨p.edgesCount,hi⟩).right)
    (empty : T.states) (heLab : T.label empty.val = ∅) (lastEmpty : p.lastState = empty.val) :
    ∃ Q : IntervalPartition σ.domain, Nonempty (Schedule T σ Q) := by
  let k := p.edgesCount
  let iLast : Fin P.size := ⟨k,hi⟩
  obtain ⟨Q,hQ,hOld,hNew⟩ := P.exists_extend_singleton_to_horizon σ iLast single
  dsimp only [iLast] at hQ hOld hNew
  have count : k+1 ≤ Q.size := hQ.le
  obtain ⟨ν,_,_,guards,labels,step⟩ := p.trace_schedule hf σ P (fun _ => 0) ⟨0,by omega⟩ sat
  refine ⟨Q,⟨{
    n := k+1, nonempty := Nat.succ_pos _, count := count,
    last_positive := ?_, q := fun i => ⟨p.stateAt i,p.valid_stateAt run.1 i⟩,
    incoming := p.incomingAt, ν := ν, initial := ?_, edge := ?_, guards := guards,
    labels := ?_, clock_step := ?_, final := ?_ }⟩⟩
  · change 0 < (Q.interval ⟨k,_⟩).right - (Q.interval ⟨k,_⟩).left
    rw [hNew]
    exact sub_pos.mpr (pieceEntry σ P iLast).property.2
  · change (p.incomingAt 0,p.stateAt 0) ∈ T.initial
    rw [p.incoming_zero,p.state_zero]
    exact run.2
  · intro i
    exact p.valid_edgeAt run.1 ⟨i.val,by have := i.isLt; omega⟩
  · intro i l hl
    by_cases before : i.val < k
    · have hP := before.trans hi
      apply (local_holds_of_same_interval σ P Q _ ⟨i.val,by omega⟩
        ⟨i.val, Nat.lt_succ_of_lt (i.isLt.trans_le count)⟩ hP
        (i.isLt.trans_le count) (hOld ⟨i.val,hP⟩ before).symm l).1
      simpa only [Fin.val_zero,Nat.zero_add] using labels i l hl
    · have he : i = Fin.last k := Fin.ext (by have := i.isLt; simp; omega)
      change l ∈ T.label (p.stateAt i) at hl
      rw [he,p.state_last,lastEmpty,heLab] at hl
      exact hl.elim
  · intro i
    let j : Fin k := ⟨i.val,by have := i.isLt; change i.val < k+1-1 at this; omega⟩
    have hP := j.isLt.trans hi
    have eq := hOld ⟨i.val,hP⟩ j.isLt
    change ν j.succ = ClockResetSet.elapse ((p.incomingAt j.castSucc).resets.apply (ν j.castSucc))
      (STLTableau.Judgement.duration Q ⟨i.val,by omega⟩)
    have dur : STLTableau.Judgement.duration Q ⟨i.val,by omega⟩ =
        STLTableau.Judgement.duration P ⟨i.val,hP⟩ := by
      apply Subtype.ext
      change (Q.interval _).right - (Q.interval _).left = _
      rw [eq]
      rfl
    rw [dur]
    simpa only [Nat.zero_add] using step j
  · left
    change p.stateAt ⟨k,_⟩ ∈ T.final
    exact (p.state_last).symm ▸ acc.2

private theorem path_schedule (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (run : p.run T) (acc : p.accepting T)
    (sat : (p.trace T.label hf).holds σ P (fun _ => 0) ⟨0,by omega⟩)
    (positive_final : ∀ hi : p.edgesCount < P.size,
      0 < STLTableau.Judgement.duration P ⟨p.edgesCount,hi⟩) : Nonempty (Schedule T σ P) := by
  obtain ⟨ν,hlen,_,guards,labels,clock_step⟩ := p.trace_schedule hf σ P (fun _ => 0) ⟨0,by omega⟩ sat
  have hle : p.edgesCount ≤ P.size := by simpa only [Fin.val_zero,Nat.zero_add] using hlen
  have final : p.stateAt (Fin.last p.edgesCount) ∈ T.final := by
    rw [p.state_last]; exact acc.2
  have init : (p.incomingAt 0,p.stateAt 0) ∈ T.initial := by
    rw [p.incoming_zero,p.state_zero]; exact run.2
  by_cases hi : p.edgesCount < P.size
  · let n := p.edgesCount+1
    have last : (⟨n-1,by dsimp [n]; omega⟩ : Fin (p.edgesCount+1)) = Fin.last p.edgesCount :=
      Fin.ext (by simp [n])
    refine ⟨{ n := n
              nonempty := Nat.succ_pos _
              count := Nat.succ_le_of_lt hi
              last_positive := by simpa [n] using positive_final hi
              q := fun i => ⟨p.stateAt i,p.valid_stateAt run.1 i⟩
              incoming := p.incomingAt
              ν := ν
              initial := init
              edge := ?_
              guards := guards
              labels := ?_
              clock_step := ?_
              final := ?_ }⟩
    · intro j; exact p.valid_edgeAt run.1 ⟨j.val,by have := j.isLt; dsimp [n] at *; omega⟩
    · intro i; simpa only [Fin.val_zero,Nat.zero_add] using labels i
    · intro j
      have hh := clock_step ⟨j.val,by have := j.isLt; dsimp [n] at *; omega⟩
      simp only [Nat.zero_add] at hh
      exact hh
    · exact Or.inl (by change p.stateAt ⟨n-1,_⟩ ∈ T.final; rw [last]; exact final)
  · have size : p.edgesCount = P.size := by omega
    have nz : 0 < p.edgesCount := size.symm ▸ P.size_pos_of_domain_nonempty
      (show σ.domain.Nonempty from ⟨0,le_rfl,σ.horizon_pos⟩)
    let n := p.edgesCount
    let last : Fin n := ⟨n-1,by dsimp [n]; omega⟩
    let target : T.states := ⟨p.stateAt (Fin.last n),p.valid_stateAt run.1 _⟩
    have endpoint : T.EndGoal target := (T.endGoal_iff target σ P
        ((p.incomingAt (Fin.last n)).resets.apply (ν (Fin.last n)))).2
      ⟨final,by
        intro l hl
        have hh := labels (Fin.last n) l hl
        have he : (⟨0 + (Fin.last n).val,by dsimp [n]; omega⟩ : STLTableau.Judgement.Position P) =
            ⟨P.size,by omega⟩ := Fin.ext (by simpa only [Nat.zero_add,Fin.val_last] using size)
        exact he ▸ hh⟩
    refine ⟨{ n := n
              nonempty := nz
              count := hle
              last_positive := ?_
              q := fun i => ⟨p.stateAt i.castSucc,p.valid_stateAt run.1 i.castSucc⟩
              incoming := fun i => p.incomingAt i.castSucc
              ν := fun i => ν i.castSucc
              initial := init
              edge := ?_
              guards := fun i => guards i.castSucc
              labels := ?_
              clock_step := ?_
              final := ?_ }⟩
    · exact last_piece_positive σ P ⟨n-1,by dsimp [n]; omega⟩
        (by change n-1+1 = P.size; dsimp [n]; omega)
    · intro j; exact p.valid_edgeAt run.1 ⟨j.val,by have := j.isLt; dsimp [n] at *; omega⟩
    · intro i; simpa only [Fin.val_zero,Nat.zero_add,Fin.val_castSucc] using labels i.castSucc
    · intro j
      have hh := clock_step ⟨j.val,by have := j.isLt; dsimp [n] at *; omega⟩
      simp only [Nat.zero_add] at hh
      exact hh
    · have he : last.succ = Fin.last n := Fin.ext (by change n-1+1=n; omega)
      refine Or.inr ⟨size,p.incomingAt (Fin.last n),target,?_,endpoint,?_⟩
      · simpa only [he] using p.valid_edgeAt run.1 last
      · intro g hg
        have hg' := guards (Fin.last n) g hg
        have hn := clock_step last
        rw [he] at hn
        rw [hn] at hg'
        simpa only [Fin.val_zero,Nat.zero_add] using hg'

private theorem extend_singleton_schedule (hf : ∀ s, (T.label s).Finite) (p : Path Clock State)
    (run : p.run T) (acc : p.accepting T)
    (sat : (p.trace T.label hf).holds σ P (fun _ => 0) ⟨0,by omega⟩)
    (hi : p.edgesCount < P.size) (zero : STLTableau.Judgement.duration P ⟨p.edgesCount,hi⟩ = 0)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ T.edges ∧ l.guards = ∅)
    (notEmpty : p.lastState ≠ empty.val) :
    Nonempty (Schedule T σ P) := by
  obtain ⟨ν,hlen,_,guards,labels,clock_step⟩ := p.trace_schedule hf σ P (fun _ => 0) ⟨0,by omega⟩ sat
  let k := p.edgesCount
  have hk : k < P.size := hi
  have nxt : k+1 < P.size := by
    by_contra! hn
    have hp := last_piece_positive σ P ⟨k,hk⟩ (by change k+1 = P.size; omega)
    rw [zero,NNReal.coe_zero] at hp
    exact lt_irrefl _ hp
  have hpos : 0 < STLTableau.Judgement.duration P ⟨k+1,nxt⟩ := by
    by_contra! hn
    have z' : STLTableau.Judgement.duration P ⟨k+1,nxt⟩ = 0 := le_antisymm hn bot_le
    have diff := P.adjacent_not_both_zero_width ⟨k,hi⟩ nxt
    have a := congrArg (fun r : NNReal => (r : ℝ)) zero
    have b := congrArg (fun r : NNReal => (r : ℝ)) z'
    change (P.interval ⟨k,hi⟩).right - (P.interval ⟨k,hi⟩).left = 0 at a
    change (P.interval ⟨k+1,nxt⟩).right - (P.interval ⟨k+1,nxt⟩).left = 0 at b
    exact diff (by linarith) (by linarith)
  let f : T.states := ⟨p.stateAt (Fin.last k),p.valid_stateAt run.1 _⟩
  have hfGoal : f ∈ T.goalModes := by change p.stateAt (Fin.last k) ∈ T.final; rw [p.state_last]; exact acc.2
  have init : (p.incomingAt 0,p.stateAt 0) ∈ T.initial := by
    rw [p.incoming_zero,p.state_zero]; exact run.2
  have he : f ≠ empty := by
    intro eq
    exact notEmpty (p.state_last.symm.trans (congrArg Subtype.val eq))
  obtain ⟨l,edge,noGuard⟩ := continuation f hfGoal he
  let n := k+2
  let ν' := ClockResetSet.elapse ((p.incomingAt (Fin.last k)).resets.apply (ν (Fin.last k)))
    (STLTableau.Judgement.duration P ⟨k,hi⟩)
  let modes (i : Fin n) : T.states := if h : i.val < k+1 then
    ⟨p.stateAt ⟨i.val,h⟩,p.valid_stateAt run.1 _⟩ else empty
  let incoming (i : Fin n) := if h : i.val < k+1 then p.incomingAt ⟨i.val,h⟩ else l
  let clock (i : Fin n) := if h : i.val < k+1 then ν ⟨i.val,h⟩ else ν'
  have lastVal : n-1 = k+1 := by dsimp [n]
  refine ⟨{ n := n
            nonempty := Nat.succ_pos _
            count := nxt
            last_positive := by simpa only [lastVal] using hpos
            q := modes
            incoming := incoming
            ν := clock
            initial := ?_
            edge := ?_
            guards := ?_
            labels := ?_
            clock_step := ?_
            final := ?_ }⟩
  · simpa [incoming,modes] using init
  · intro j
    have hj : j.val < k+1 := by have := j.isLt; dsimp [n] at this; omega
    by_cases hb : j.val+1 < k+1
    · simp only [incoming,modes,dif_pos hj,dif_pos hb]
      exact p.valid_edgeAt run.1 ⟨j.val,by omega⟩
    · have hlast : j.val = k := by omega
      simp only [incoming,modes,dif_pos hj,dif_neg hb]
      have eq : (⟨j.val,hj⟩ : Fin (k+1)) = Fin.last k := Fin.ext hlast
      rw [eq]
      exact edge
  · intro i g hg
    by_cases hb : i.val < k+1
    · simpa only [incoming,clock,dif_pos hb] using
        guards ⟨i.val,hb⟩ g (by simpa only [incoming,dif_pos hb] using hg)
    · simp only [incoming,dif_neg hb,noGuard] at hg
      exact hg.elim
  · intro i a ha
    by_cases hb : i.val < k+1
    · simp only [modes,dif_pos hb] at ha
      simpa only [incoming,clock,dif_pos hb,Fin.val_zero,Nat.zero_add] using labels ⟨i.val,hb⟩ a ha
    · simp only [modes,dif_neg hb,heLab] at ha
      exact ha.elim
  · intro j
    have hj : j.val < k+1 := by have := j.isLt; dsimp [n] at this; omega
    by_cases hb : j.val+1 < k+1
    · simp only [clock,incoming,dif_pos hj,dif_pos hb]
      have hh := clock_step ⟨j.val,by omega⟩
      simp only [Nat.zero_add] at hh
      exact hh
    · have hlast : j.val = k := by omega
      simp only [clock,incoming,dif_pos hj,dif_neg hb]
      have eq : (⟨j.val,hj⟩ : Fin (k+1)) = Fin.last k := Fin.ext hlast
      rw [eq]
      have same : (⟨j.val,by omega⟩ : Fin P.size) = ⟨k,hi⟩ := Fin.ext hlast
      rw [same]
  · exact Or.inl (by simpa [modes,lastVal] using heGoal)

private theorem build_execution
    (s : Schedule T σ P)
    (sample : ∀ i : Fin P.size, (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i)) →
      Var → ℝ)
    (entry : ∀ i, sample i ⟨0,by simp⟩ = σ.value (pieceEntry σ P i))
    (observed : ∀ i (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i))
      (hu : u.val < STLTableau.Judgement.duration P i),
      sample i u = σ.value (pieceTime σ P i ⟨u.val,u.property.1,hu⟩))
    (safe : ∀ (i : Fin s.n) (u : Set.Icc (0 : ℝ)
      (STLTableau.Judgement.duration P ⟨i.val,i.isLt.trans_le s.count⟩)) a,
      Local.predicate (.plain (.atom a)) ∈ T.label (s.q i).val →
      a.Holds (sample ⟨i.val,i.isLt.trans_le s.count⟩ u)) :
    ∃ e : T.TableauExecution h σ.horizon σ, e.goal ∧ e.n = s.n ∧
      ∃ count : e.n ≤ P.size,
        (∀ i : Fin e.n, (P.interval ⟨i.val,i.isLt.trans_le count⟩).left = e.time i.castSucc ∧
          (P.interval ⟨i.val,i.isLt.trans_le count⟩).right = e.time i.succ) ∧
        (∀ (i : Fin e.n) (u : Set.Icc (0 : ℝ) (e.duration i)) (x : T.realVariables),
          ∃ v : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P ⟨i.val,i.isLt.trans_le count⟩),
            v.val = u.val ∧ e.curve i u (.inl x) = sample ⟨i.val,i.isLt.trans_le count⟩ v x.val) ∧
        (CanonicalBoundaryForms σ P → e.BoundaryCompatible) := by
  classical
  let j (i : Fin s.n) : Fin P.size := ⟨i.val,i.isLt.trans_le s.count⟩
  let last : Fin s.n := ⟨s.n-1,by have := s.nonempty; omega⟩
  let b (i : Fin (s.n+1)) : ℝ := Fin.lastCases (motive := fun _ => ℝ) (P.interval (j last)).right
    (fun i => (P.interval (j i)).left) i
  have bl (i : Fin s.n) : b i.castSucc = (P.interval (j i)).left := by simp [b]
  have br (i : Fin s.n) : b i.succ = (P.interval (j i)).right := by
    by_cases hi : i.val+1 < s.n
    · let k : Fin s.n := ⟨i.val+1,hi⟩
      have he : i.succ = k.castSucc := rfl
      rw [he,bl]
      exact (P.adjacent_right_eq_left (j i) (hi.trans_le s.count)).symm
    · have he : i = last := Fin.ext (by change i.val = s.n-1; have := i.isLt; omega)
      have hs : i.succ = Fin.last s.n := Fin.ext (by have := i.isLt; simp; omega)
      rw [he]
      simpa [b,he] using congrArg b hs
  have b0 : b 0 = 0 := by
    exact (bl ⟨0,s.nonempty⟩).trans
      (P.first_left_eq_domain_left (s.nonempty.trans_le s.count) σ.horizon_pos)
  have bm : Monotone b := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    rw [bl,br]
    exact P.left_le_right (j i)
  have bisol : IntervalPartition.IsolatedSingletons b := by
    intro i hi hz hn
    have z : (P.interval (j i)).right = (P.interval (j i)).left := by
      rw [← bl,← br]; exact hz.symm
    let k : Fin s.n := ⟨i.val+1,hi⟩
    have z' : (P.interval (j k)).right = (P.interval (j k)).left := by
      rw [← bl,← br]; exact hn.symm
    exact P.adjacent_not_both_zero_width (j i) (hi.trans_le s.count) z z'
  have bend : ∀ i : Fin s.n, i.val+1 = s.n → b i.castSucc ≠ b i.succ := by
    intro i hi he
    have eq : i = last := Fin.ext (by change i.val = s.n-1; omega)
    have pos := s.last_positive
    change 0 < (P.interval (j last)).right - (P.interval (j last)).left at pos
    rw [eq,bl,br] at he
    linarith
  let seed (i : Fin s.n) := T.visitValue (P.interval (j i)).left
    ((s.incoming i).resets.apply (s.ν i)) (σ.value (pieceEntry σ P (j i)))
  let γ (i : Fin s.n) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P (j i))) :=
    T.curveValue (seed i) u.val (fun x => sample (j i) u x.val)
  have inv (i : Fin s.n) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P (j i))) :
      (s.q i,γ i u) ∈ (A).invariant := by
    apply T.invariant_of_atoms h σ (s.q i) _
    · change (P.interval (j i)).left + u.val ≤ σ.horizon
      have upper := u.property.2
      change u.val ≤ (P.interval (j i)).right - (P.interval (j i)).left at upper
      linarith [P.right_le_domain_right (j i)]
    · intro a ha
      exact (T.atomHolds_iff a _ (sample (j i) u) (h.atom_variables _ (s.q i).property a ha)
        (fun _ => rfl)).2 (safe i u a ha)
  let a (i : Fin s.n) : (A).State := ⟨(s.q i,γ i ⟨0,by simp⟩),inv _ _⟩
  let f (i : Fin s.n) : (A).State :=
    ⟨(s.q i,γ i ⟨STLTableau.Judgement.duration P (j i),by simp⟩),inv _ _⟩
  have hstart (i : Fin s.n) : (a i).val = (s.q i,seed i) := by
    refine Prod.ext rfl ?_
    funext x
    rcases x with x | x
    · exact congrFun (entry (j i)) x.val
    · simp [a,γ,curveValue]
  have hf (i : Fin s.n) : (A).ContinuousStep (a i) (f i)
      (STLTableau.Judgement.duration P (j i)) (γ i) := by
    refine ⟨rfl,rfl,rfl,?_⟩
    intro u
    refine ⟨⟨fun c => ?_,?_⟩,inv i u⟩
    · rw [hstart i]; rfl
    · rw [hstart i]; rfl
  have hobs (i : Fin s.n) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P (j i)))
      (hu : u.val < STLTableau.Judgement.duration P (j i)) (x : T.realVariables) :
      γ i u (.inl x) = σ.value (pieceTime σ P (j i) ⟨u.val,u.property.1,hu⟩) x.val :=
    congrFun (observed _ _ hu) _
  have hx (i : Fin s.n) (x : T.realVariables)
      (zero : STLTableau.Judgement.duration P (j i) = 0) :
      (f i).val.2 (.inl x) = (a i).val.2 (.inl x) := by
    change γ i ⟨(STLTableau.Judgement.duration P (j i) : ℝ),by simp⟩ (.inl x) =
      γ i ⟨0,by simp⟩ (.inl x)
    have eq : (⟨(STLTableau.Judgement.duration P (j i) : ℝ),by simp⟩ :
        Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P (j i))) = ⟨0,by simp⟩ :=
      Subtype.ext (by simp [zero])
    rw [eq]
  have endClock (i : Fin s.n) (c : T.clocks) : (f i).val.2 (.inr (.inl c)) =
      (ClockResetSet.elapse ((s.incoming i).resets.apply (s.ν i))
        (STLTableau.Judgement.duration P (j i)) c.val : ℝ) := by
    have eq := ((hf i).2.2.2 ⟨STLTableau.Judgement.duration P (j i),by simp⟩).1.1 c
    rw [(hf i).2.2.1,hstart i] at eq
    exact eq
  have endGlobal (i : Fin s.n) : (f i).val.2 T.globalClock = (P.interval (j i)).right := by
    have eq := ((hf i).2.2.2 ⟨STLTableau.Judgement.duration P (j i),by simp⟩).1.2
    rw [(hf i).2.2.1,hstart i] at eq
    change (f i).val.2 T.globalClock = (P.interval (j i)).left +
      ((P.interval (j i)).right - (P.interval (j i)).left) at eq
    linarith
  have entryMode (i : Fin s.n) : (a i).val.1 = s.q i := congrArg Prod.fst (hstart i)
  have exitMode (i : Fin s.n) : (f i).val.1 = s.q i := ((hf i).1).symm.trans (entryMode i)
  let v0 := T.visitValue 0 (s.ν ⟨0,s.nonempty⟩) (σ.value ⟨0,le_rfl,σ.horizon_pos⟩)
  let i0 : Fin s.n := ⟨0,s.nonempty⟩
  have firstTime : (P.interval (j i0)).left = 0 := (bl i0).symm.trans b0
  have firstSample : pieceEntry σ P (j i0) = ⟨0,le_rfl,σ.horizon_pos⟩ := Subtype.ext firstTime
  have initReset : (a i0).val.2 = T.initialReset (s.incoming i0).resets v0 := by
    rw [hstart i0]
    dsimp only [seed]
    rw [firstTime,firstSample]
    funext x
    rcases x with x | (c | ⟨⟩)
    · rfl
    · exact (T.reset_clock_agrees _ _ _ (fun _ => rfl) c).symm
    · rfl
  have initEdge : (s.incoming i0,(a i0).val.1.val) ∈ T.initial := by
    rw [entryMode]; exact s.initial
  have initGuard : T.guardsHold (s.incoming i0) v0 :=
    (T.guardsHold_iff _ _ _ (h.initial_guards _ initEdge) (fun _ => rfl)).2 (s.guards i0)
  let e : T.TableauExecution h σ.horizon σ := {
    n := s.n
    nonempty := s.nonempty
    time := b
    first_zero := b0
    monotone := bm
    isolated := bisol
    last_positive := bend
    stop_le := by simpa [b] using P.right_le_domain_right (j last)
    horizon := rfl
    start := a
    finish := f
    initial := ⟨_,initEdge,v0,initGuard,initReset⟩
    initialLabel := s.incoming i0
    initialValue := v0
    initial_edge := initEdge
    initial_guard := initGuard
    initial_reset := initReset
    initial_observation := by
      intro x
      rw [hstart i0]
      dsimp only [seed]
      rw [firstSample]
      rfl
    duration := fun i => STLTableau.Judgement.duration P (j i)
    duration_eq := by intro i; rw [bl,br]; rfl
    curve := γ
    flow := hf
    jump := by
      intro k
      let i : Fin s.n := ⟨k.val,by have := k.isLt; omega⟩
      let i' : Fin s.n := ⟨k.val+1,by have := k.isLt; omega⟩
      have edge := s.edge k
      have clk : s.ν i' = ClockResetSet.elapse ((s.incoming i).resets.apply (s.ν i))
          (STLTableau.Judgement.duration P (j i)) := s.clock_step k
      have he : ((f i).val.1.val,s.incoming i',(a i').val.1.val) ∈ T.edges := by
        rw [exitMode,entryMode]; exact edge
      refine ⟨s.incoming i',he,?_,?_,?_,?_⟩
      · apply (T.guardsHold_iff _ _ (s.ν i') (h.edge_guards _ he) ?_).2 (s.guards i')
        intro c; rw [clk]; exact endClock i c
      · intro c
        have clocks (c : T.clocks) : (f i).val.2 (.inr (.inl c)) = (s.ν i' c.val : ℝ) := by
          rw [clk]; exact endClock i c
        rw [T.reset_clock_agrees _ _ _ clocks c]
        change (a i').val.2 (.inr (.inl c)) = _
        rw [hstart i']; rfl
      · change (a i').val.2 T.globalClock = (f i).val.2 T.globalClock
        rw [hstart i',endGlobal i]
        exact (P.adjacent_right_eq_left (j i) (j i').isLt).symm
      · intro terminal
        change (a i').val.1 ∈ T.terminalModes at terminal
        rw [entryMode] at terminal
        have impossible : (j i').val = P.size := s.labels i' .terminal terminal
        exact ((j i').isLt.ne impossible).elim
    singleton_exit := by
      intro k x zero
      let i : Fin s.n := ⟨k.val,by have := k.isLt; omega⟩
      let i' : Fin s.n := ⟨k.val+1,by have := k.isLt; omega⟩
      change (f i).val.2 (.inl x) = (a i').val.2 (.inl x)
      rw [hx i x zero,hstart i,hstart i']
      change σ.value (pieceEntry σ P (j i)) x.val = σ.value (pieceEntry σ P (j i')) x.val
      apply congrArg (fun t : σ.Time => σ.value t x.val)
      apply Subtype.ext
      have hz := congrArg (fun r : NNReal => (r : ℝ)) zero
      have adj := P.adjacent_right_eq_left (j i) (j i').isLt
      change (P.interval (j i)).right - (P.interval (j i)).left = 0 at hz
      change (P.interval (j i)).left = (P.interval (j i')).left
      linarith
    observes := by
      intro i t ht _ x
      have duration : (STLTableau.Judgement.duration P (j i) : ℝ) = b i.succ - b i.castSucc := by
        rw [br,bl]; rfl
      let u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P (j i)) :=
        ⟨t.val-b i.castSucc,by constructor <;> linarith [ht.1,ht.2,duration]⟩
      have hu : u.val < (STLTableau.Judgement.duration P (j i) : ℝ) := by
        dsimp [u]; linarith [ht.2,duration]
      have he : pieceTime σ P (j i) ⟨u.val,u.property.1,hu⟩ = t :=
        Subtype.ext (by change (P.interval (j i)).left + (t.val-b i.castSucc) = t.val; rw [bl]; ring)
      exact ((hobs i u hu x).trans (congrArg (fun z : σ.Time => σ.value z x.val) he)).symm }
  refine ⟨e,?_,rfl,s.count,fun i => ⟨(bl i).symm,(br i).symm⟩,?_,?_⟩
  · rcases s.final with ordinary | ⟨full,l,q,edge,endGoal,guards⟩
    · left
      change (f last).val.1 ∈ T.goalModes
      rwa [exitMode last]
    · have t : (P.interval (j last)).right = σ.horizon :=
        P.last_right_eq_domain_right (j last) (by
          change s.n-1+1 = P.size; have := s.nonempty; omega)
      have cut : e.cut = σ.horizon := by
        change b (Fin.last s.n) = σ.horizon
        simpa only [b,Fin.lastCases_last] using t
      have edge' : ((f last).val.1.val,l,q.val) ∈ T.edges := by
        simpa only [exitMode last] using edge
      have guard := (T.guardsHold_iff _ _ _ (h.edge_guards _ edge) (endClock last)).2 guards
      obtain ⟨target,step,mode,_⟩ :=
        T.horizon_entry h σ.horizon (f last) ((endGlobal last).trans t) l q edge' guard endGoal
      have final : target ∈ T.canonicalGoal h σ.horizon := by
        change target.val.1 ∈ T.goalModes
        rw [mode]
        exact endGoal.1
      exact Or.inr ⟨cut,target,final,step⟩
  · intro i u x
    exact ⟨u,rfl,rfl⟩
  · intro canonical
    have marker (i : Fin s.n) :
        IntervalPartition.singletonMarkers b i.castSucc = (P.interval (j i)).leftBoundary := by
      obtain ⟨k,hk⟩ := i
      cases k with
      | zero =>
        exact (IntervalPartition.singletonMarkers_first b).trans
          (P.first_leftBoundary_closed (s.nonempty.trans_le s.count) σ.horizon_pos).symm
      | succ k =>
        let prev : Fin s.n := ⟨k,by omega⟩
        have eq : (⟨k+1,hk⟩ : Fin s.n).castSucc = ⟨prev.val+1,by omega⟩ := rfl
        rw [eq,IntervalPartition.singletonMarkers_succ b prev]
        change (if b prev.castSucc = b prev.succ then ○ else ●) = _
        rw [bl,br]
        exact (canonical ⟨k,by have := s.count; omega⟩).symm
    intro i m hm
    change Local.marker m ∈ T.label (a i).val.1.val at hm
    rw [entryMode] at hm
    exact (T.piece_entry_markers σ P (j i) (s.q i) _ (s.labels i) m hm).trans (marker i).symm

/-- Used in Lemma 5.5(1). Follow the given partition boundaries and execute
the accepting path's guards and resets. A final singleton can be followed
by a positive flow to complete the execution. -/
theorem forward_of_recognized (φ : Formula Var) (hw : SignalAtomRightContinuous σ φ)
    (hf : ∀ s, (T.label s).Finite)
    (recognized : T.recognizes hf σ P)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Formula.IsSubformula (.atom a) φ)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ T.edges ∧ l.guards = ∅) :
    ∃ e : T.TableauExecution h σ.horizon σ, e.goal := by
  obtain ⟨p,run,acc,sat⟩ := recognized
  have schedule : ∃ Q : IntervalPartition σ.domain, Nonempty (Schedule T σ Q) := by
    by_cases positive : ∀ hi : p.edgesCount < P.size,
        0 < STLTableau.Judgement.duration P ⟨p.edgesCount,hi⟩
    · exact ⟨P,T.path_schedule σ P hf p run acc (sat _) positive⟩
    · push Not at positive
      obtain ⟨hi,hz⟩ := positive
      have zero : STLTableau.Judgement.duration P ⟨p.edgesCount,hi⟩ = 0 :=
        le_antisymm hz bot_le
      by_cases lastEmpty : p.lastState = empty.val
      · have single : (P.interval ⟨p.edgesCount,hi⟩).left =
            (P.interval ⟨p.edgesCount,hi⟩).right := by
          have ht := congrArg NNReal.toReal zero
          change (P.interval ⟨p.edgesCount,hi⟩).right -
            (P.interval ⟨p.edgesCount,hi⟩).left = 0 at ht
          linarith
        exact T.empty_last_raw_schedule σ P hf p run acc (sat _) hi single empty heLab lastEmpty
      · exact ⟨P,T.extend_singleton_schedule σ P hf p run acc (sat _) hi
          zero empty heGoal heLab continuation lastEmpty⟩
  obtain ⟨Q,⟨s⟩⟩ := schedule
  classical
  let sample (i : Fin Q.size) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration Q i)) :
      Var → ℝ :=
    if hu : u.val < STLTableau.Judgement.duration Q i then
      σ.value (pieceTime σ Q i ⟨u.val,u.property.1,hu⟩)
    else σ.value (flowSample σ Q i)
  have entry (i : Fin Q.size) : sample i ⟨0,by simp⟩ = σ.value (pieceEntry σ Q i) := by
    unfold sample
    split
    · congr 1
      exact Subtype.ext (by change (Q.interval i).left + 0 = (Q.interval i).left; ring)
    · rename_i hz
      by_cases hc : (Q.interval i).rightBoundary.Includes
      · apply congrArg σ.value
        apply Subtype.ext
        rw [flowSample_owned σ Q i hc]
        change ¬ 0 < (Q.interval i).right - (Q.interval i).left at hz
        change (Q.interval i).right = (Q.interval i).left
        linarith [Q.left_le_right i]
      · simp [flowSample,hc]
  have observed (i : Fin Q.size) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration Q i))
      (hu : u.val < STLTableau.Judgement.duration Q i) :
      sample i u = σ.value (pieceTime σ Q i ⟨u.val,u.property.1,hu⟩) := dif_pos hu
  have safe (i : Fin s.n) (u : Set.Icc (0 : ℝ)
      (STLTableau.Judgement.duration Q ⟨i.val,i.isLt.trans_le s.count⟩)) a
      (ha : Local.predicate (.plain (.atom a)) ∈ T.label (s.q i).val) :
      a.Holds (sample ⟨i.val,i.isLt.trans_le s.count⟩ u) := by
    let j : Fin Q.size := ⟨i.val,i.isLt.trans_le s.count⟩
    have atoms := T.piece_entry_atoms σ φ hw Q j (s.q i) _ (s.labels i) (input _)
    by_cases zero : u.val = 0
    · have same : u = ⟨0,by simp⟩ := Subtype.ext zero
      rw [same,entry]
      exact atoms _ ha
    have holds := s.labels i _ ha
    simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,
      dif_pos (show i.val < Q.size from j.isLt),
      Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] at holds
    by_cases hu : u.val < STLTableau.Judgement.duration Q j
    · rw [observed j u hu]
      apply holds
      change (Q.interval j).left + u.val ∈ Q.interval j
      have positive : 0 < u.val := lt_of_le_of_ne u.property.1 (Ne.symm zero)
      exact ⟨Or.inl (by linarith),Or.inl (by
        change u.val < (Q.interval j).right - (Q.interval j).left at hu
        linarith)⟩
    · rw [show sample j u = σ.value (flowSample σ Q j) from dif_neg hu]
      by_cases hc : (Q.interval j).rightBoundary.Includes
      · apply holds
        rw [flowSample_owned σ Q j hc]
        exact (Q.interval j).right_mem (Q.nonempty j) hc
      · simpa only [flowSample,dif_neg hc] using atoms _ ha
  obtain ⟨e,goal,_⟩ := T.build_execution h σ Q s sample entry observed safe
  exact ⟨e,goal⟩

/-- Apply the clock schedule to slices of a single full system execution.
The system and property use the same physical values even at the closed
flow endpoints. No marker coordinate is added to the product. -/
private theorem build_over_system {Mode Label : Type*} {H : HybridAutomaton Mode Label Var}
    (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0,sys.nonempty⟩)
    (single : ∀ (k : Fin sys.count) (live : k.val+1 < sys.count),
      H.DiscreteStep (sys.finish k) (sys.start ⟨k.val+1,live⟩))
    (flows : H.ContinuousFlows) (canonical : CanonicalBoundaryForms σ P)
    (s : Schedule T σ P)
    (owner : ∀ (i : Fin s.n),
      let J := P.interval ⟨i.val,i.isLt.trans_le s.count⟩
      ∃ k : Fin sys.count, sys.boundary k.castSucc ≤ J.left ∧
        J.left < sys.boundary k.succ ∧ J.right ≤ sys.boundary k.succ)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Continuous a.function) :
    ∃ e : T.CanonicalExecution h σ.horizon σ, e.goal ∧
      Nonempty (CanonicalSynchronization H h σ.horizon e) := by
  classical
  have bounded (i : Fin P.size) (live : i.val < s.n) :
      ∃ k : Fin sys.count, sys.boundary k.castSucc ≤ (P.interval i).left ∧
        (P.interval i).left < sys.boundary k.succ ∧ (P.interval i).right ≤ sys.boundary k.succ :=
    owner ⟨i.val,live⟩
  choose k kb using bounded
  let fallback (i : Fin P.size) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i)) :
      Var → ℝ :=
    if hu : u.val < STLTableau.Judgement.duration P i then
      σ.value (pieceTime σ P i ⟨u.val,u.property.1,hu⟩)
    else σ.value (pieceEntry σ P i)
  let sampleAt (i : Fin P.size) (live : i.val < s.n)
      (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i)) : Var → ℝ :=
    sys.curve (k i live) ⟨(P.interval i).left - sys.boundary (k i live).castSucc + u.val, by
      have h := kb i live
      have hd : (sys.duration (k i live) : ℝ) =
        sys.boundary (k i live).succ - sys.boundary (k i live).castSucc := sys.duration_eq _
      have up : u.val ≤ (P.interval i).right - (P.interval i).left := u.property.2
      constructor <;> linarith [h.1,h.2.2,u.property.1]⟩
  let sample (i : Fin P.size) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i)) :
      Var → ℝ :=
    if live : i.val < s.n then sampleAt i live u else fallback i u
  have observeAt (i : Fin P.size) (live : i.val < s.n)
      (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i))
      (t : σ.Time) (eq : t.val = (P.interval i).left + u.val)
      (inside : t.val < sys.boundary (k i live).succ) : sampleAt i live u = σ.value t := by
    have low : sys.boundary (k i live).castSucc ≤ t.val := by
      linarith [(kb i live).1,u.property.1]
    have obs := sys.signal_eq (k i live) t ⟨low,inside⟩
    refine Eq.trans ?_ obs.symm
    apply congrArg (sys.curve (k i live))
    apply Subtype.ext
    change (P.interval i).left - sys.boundary (k i live).castSucc + u.val =
      t.val - sys.boundary (k i live).castSucc
    linarith
  have entry (i : Fin P.size) : sample i ⟨0,by simp⟩ = σ.value (pieceEntry σ P i) := by
    unfold sample
    split_ifs with live
    · exact observeAt i live _ _ (by change (P.interval i).left = _ + 0; ring) (kb i live).2.1
    · unfold fallback
      split
      · congr 1
        exact Subtype.ext (by change (P.interval i).left + 0 = (P.interval i).left; ring)
      · rfl
  have observed (i : Fin P.size) (u : Set.Icc (0 : ℝ) (STLTableau.Judgement.duration P i))
      (hu : u.val < STLTableau.Judgement.duration P i) :
      sample i u = σ.value (pieceTime σ P i ⟨u.val,u.property.1,hu⟩) := by
    unfold sample
    split_ifs with live
    · apply observeAt i live _ _ rfl
      change (P.interval i).left + u.val < _
      have hd : (STLTableau.Judgement.duration P i : ℝ) =
        (P.interval i).right - (P.interval i).left := rfl
      linarith [(kb i live).2.2]
    · exact dif_pos hu
  have safe (i : Fin s.n) (u : Set.Icc (0 : ℝ)
      (STLTableau.Judgement.duration P ⟨i.val,i.isLt.trans_le s.count⟩)) a
      (ha : Local.predicate (.plain (.atom a)) ∈ T.label (s.q i).val) :
      a.Holds (sample ⟨i.val,i.isLt.trans_le s.count⟩ u) := by
    let j : Fin P.size := ⟨i.val,i.isLt.trans_le s.count⟩
    have atom (t : σ.Time) (ht : t.val ∈ P.interval j) : a.Holds (σ.value t) := by
      have hh := s.labels i _ ha
      simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,
        dif_pos (show i.val < P.size from j.isLt),Predicate.holds,predicateSatisfies,FiniteSignal.Satisfies] at hh
      exact hh t ht
    by_cases hp : 0 < (STLTableau.Judgement.duration P j : ℝ)
    · have continuous : Continuous (sample j) := by
        simp only [sample,dif_pos (show j.val < s.n from i.isLt)]
        change Continuous (fun v => sys.curve (k j i.isLt) _)
        exact (flows _ (sys.continuousStep (k j i.isLt)).evolves).comp
          ((continuous_const.add continuous_subtype_val).subtype_mk _)
      apply atom_on_closed_curve_of_interior (sample j) hp continuous a (input _ a ha).1 (input _ a ha).2 _ u
      intro v pos before
      rw [observed j v before]
      apply atom
      change (P.interval j).left + v.val ∈ P.interval j
      have hh : (STLTableau.Judgement.duration P j : ℝ) = (P.interval j).right - (P.interval j).left := rfl
      exact ⟨Or.inl (by linarith),Or.inl (by linarith)⟩
    · have zero : (STLTableau.Judgement.duration P j : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hp) (STLTableau.Judgement.duration P j).coe_nonneg
      have uz : u = ⟨0,by simp⟩ := Subtype.ext (by linarith [u.property.1,u.property.2])
      rw [uz,entry]
      apply atom
      change (P.interval j).left ∈ P.interval j
      have eql : (P.interval j).right = (P.interval j).left := by
        change (P.interval j).right - (P.interval j).left = 0 at zero
        linarith
      rw [← MarkedInterval.mem_carrier, P.carrier_eq_singleton_of_endpoints_eq j eql]
      exact Set.mem_singleton _
  obtain ⟨raw,goal,countN,count,bounds,curve,compatible⟩ :=
    T.build_execution h σ P s sample entry observed safe
  let e : T.CanonicalExecution h σ.horizon σ := ⟨raw,compatible canonical⟩
  let j (i : Fin e.n) : Fin P.size := ⟨i.val,i.isLt.trans_le count⟩
  have nEq : e.n = s.n := countN
  refine ⟨e,goal,⟨{
    system := sys
    full := full
    direct := direct
    owner := fun i => k (j i) (nEq ▸ i.isLt)
    bounds := ?_
    singleJump := single
    shared := ?_ }⟩⟩
  · intro i
    have hb := kb (j i) (nEq ▸ i.isLt)
    exact ⟨hb.1.trans_eq (bounds i).1, (bounds i).1.symm.trans_lt hb.2.1,
      (bounds i).2.symm.le.trans hb.2.2⟩
  · intro i u x
    obtain ⟨v,hv,hx⟩ := curve i u x
    let live : (j i).val < s.n := nEq ▸ i.isLt
    let z : Set.Icc (0 : ℝ) (sys.duration (k (j i) live)) :=
      ⟨(P.interval (j i)).left - sys.boundary (k (j i) live).castSucc + v.val, by
        have hh := kb (j i) live
        have hd : (sys.duration (k (j i) live) : ℝ) =
            sys.boundary (k (j i) live).succ - sys.boundary (k (j i) live).castSucc := sys.duration_eq _
        have up : v.val ≤ (P.interval (j i)).right - (P.interval (j i)).left := v.property.2
        constructor <;> linarith [hh.1,hh.2.2,v.property.1]⟩
    refine ⟨z,by change (P.interval (j i)).left - _ + v.val = _; rw [bounds i |>.1,hv],?_⟩
    have live' : i.val < s.n := live
    simpa only [sample,dif_pos live',sampleAt] using hx

/-- The forward path construction for the composed automaton. The original
partition refines the actual system flows. A final empty singleton can
continue only to the end of its containing system flow. -/
theorem canonical_forward_with_system {Mode Label : Type*} {H : HybridAutomaton Mode Label Var}
    (sys : H.PrelimExecution σ) (full : sys.ReachesHorizon)
    (direct : sys.initialState = sys.start ⟨0,sys.nonempty⟩)
    (single : ∀ (k : Fin sys.count) (live : k.val+1 < sys.count),
      H.DiscreteStep (sys.finish k) (sys.start ⟨k.val+1,live⟩))
    (flows : H.ContinuousFlows) (fine : P.FinerThan (sys.fullFlowPartition full))
    (canonical : CanonicalBoundaryForms σ P) (hf : ∀ q, (T.label q).Finite)
    (recognized : T.recognizes hf σ P)
    (input : ∀ (q : T.states) a, Local.predicate (.plain (.atom a)) ∈ T.label q.val →
      a.relation = .ge ∧ Continuous a.function)
    (empty : T.states) (heGoal : empty ∈ T.goalModes) (heLab : T.label empty.val = ∅)
    (continuation : ∀ f : T.states, f ∈ T.goalModes → f ≠ empty →
      ∃ l : EdgeLabel Clock, (f.val,l,empty.val) ∈ T.edges ∧ l.guards = ∅) :
    ∃ e : T.CanonicalExecution h σ.horizon σ, e.goal ∧
      Nonempty (CanonicalSynchronization H h σ.horizon e) := by
  obtain ⟨p,run,acc,sat⟩ := recognized
  have owner (i : Fin P.size) : ∃ k : Fin sys.count,
      sys.boundary k.castSucc ≤ (P.interval i).left ∧
      (P.interval i).left < sys.boundary k.succ ∧ (P.interval i).right ≤ sys.boundary k.succ :=
    ⟨sys.cellOwner full P fine i,(sys.cell_bounds full P fine i).1,
      sys.cell_entry_lt full P fine i,(sys.cell_bounds full P fine i).2.2⟩
  by_cases positive : ∀ hi : p.edgesCount < P.size,
      0 < STLTableau.Judgement.duration P ⟨p.edgesCount,hi⟩
  · obtain ⟨s⟩ := T.path_schedule σ P hf p run acc (sat _) positive
    exact T.build_over_system h σ P sys full direct single flows canonical s
      (fun i => owner ⟨i.val,i.isLt.trans_le s.count⟩) input
  · push Not at positive
    obtain ⟨hi,hz⟩ := positive
    by_cases lastEmpty : p.lastState = empty.val
    · obtain ⟨k,lo,before,_⟩ := owner ⟨p.edgesCount,hi⟩
      have le : sys.boundary k.succ ≤ σ.horizon :=
        (sys.increasing.monotone (Fin.le_last _)).trans sys.last_le_horizon
      obtain ⟨Q,s,form,hn,prev,last⟩ := T.empty_last_schedule σ P hf p run acc (sat _) canonical
        hi empty heLab lastEmpty (sys.boundary k.succ) before le
      apply T.build_over_system h σ Q sys full direct single flows form s ?_ input
      intro i
      by_cases old : i.val < p.edgesCount
      · dsimp only
        rw [prev i old]
        exact owner _
      · have eq : i.val = p.edgesCount := by have := i.isLt; omega
        have endpoints := last i eq
        exact ⟨k,endpoints.1 ▸ lo,endpoints.1 ▸ before,endpoints.2.le⟩
    · obtain ⟨s⟩ := T.extend_singleton_schedule σ P hf p run acc (sat _) hi
        (le_antisymm hz bot_le) empty heGoal heLab continuation lastEmpty
      exact T.build_over_system h σ P sys full direct single flows canonical s
        (fun i => owner ⟨i.val,i.isLt.trans_le s.count⟩) input

end Tableau

namespace Tableau.TableauExecution
open HybridAutomaton
variable {Clock Var State : Type*} {T : Tableau Clock Var State}
variable {h : T.TranslationReady} {τ : ℝ} {σ : FiniteSignal Var}
variable (e : T.TableauExecution h τ σ)
local notation "A" => T.canonicalAutomaton h τ

private theorem flowPiece (i : Fin e.n) (pos : 0 < e.duration i) :
    ∃ p : ProjectedFlowPiece (A) (σ.reindex Subtype.val) (Sum.inl : T.realVariables → T.HAVar),
      p.start = e.start i ∧ p.finish = e.finish i ∧ p.left = e.time i.castSucc ∧
        p.left + (p.duration : ℝ) = e.time i.succ := by
  let p : ProjectedFlowPiece (A) (σ.reindex Subtype.val) (Sum.inl : T.realVariables → T.HAVar) := {
    left := e.time i.castSucc
    duration := e.duration i
    positive := pos
    start := e.start i
    finish := e.finish i
    curve := e.curve i
    step := e.flow i
    observe := by
      intro t u hu hd x
      by_cases hp : 0 < t.val
      · have hb : e.time i.castSucc ≤ t.val ∧ t.val < e.time i.succ := by
          constructor <;> linarith [u.property.1,e.duration_eq i]
        let v : Set.Icc (0 : ℝ) (e.duration i) := ⟨t.val - e.time i.castSucc, by
          constructor <;> linarith [hb.1,hb.2,e.duration_eq i]⟩
        have heq : v = u := Subtype.ext (by change t.val - e.time i.castSucc = u.val; linarith)
        have same := (e.observes i (⟨t.val,t.property⟩ : σ.Time) hb hp x).symm
        change e.curve i v (.inl x) = (σ.reindex Subtype.val).value t x at same
        rw [heq] at same
        exact same
      · have ht : t.val = 0 := le_antisymm (le_of_not_gt hp) t.property.1
        have htime : ∀ j : Fin (e.n+1), j ≤ i.castSucc → e.time j = 0 := by
          intro j hj
          have up := e.monotone hj
          have low := e.monotone (Fin.zero_le j)
          rw [e.first_zero] at low
          linarith [u.property.1]
        have u0 : u = ⟨0,by simp⟩ := Subtype.ext (by
          rw [htime i.castSucc le_rfl,ht,zero_add] at hu
          exact hu)
        have t0 : (⟨t.val,t.property⟩ : σ.Time) = ⟨0,le_rfl,σ.horizon_pos⟩ := Subtype.ext ht
        rw [u0,(e.flow _).2.1]
        change (e.start i).val.2 (.inl x) = σ.value ⟨t.val,t.property⟩ x.val
        rw [t0]
        have all (k : ℕ) (hk : k ≤ i.val) :
            (e.start ⟨k,hk.trans_lt i.isLt⟩).val.2 (.inl x) =
              σ.value ⟨0,le_rfl,σ.horizon_pos⟩ x.val := by
          induction k with
          | zero => exact (e.initial_observation x).symm
          | succ k ih =>
            let j : Fin e.n := ⟨k,by have := i.isLt; omega⟩
            let edge : Fin (e.n-1) := ⟨k,by have := i.isLt; omega⟩
            have hz : e.duration j = 0 :=
              (e.duration_zero_iff j).2 ((htime j.castSucc (by change k ≤ i.val; omega)).trans
                (htime j.succ (by change k+1 ≤ i.val; omega)).symm)
            have same := e.singleton_exit edge x hz
            change (e.finish j).val.2 (.inl x) = _ at same
            rw [← e.start_eq_finish_of_zero j hz] at same
            exact same.symm.trans (ih (by omega))
        exact all i.val le_rfl }
  refine ⟨p,rfl,rfl,rfl,?_⟩
  change e.time i.castSucc + (e.duration i : ℝ) = e.time i.succ
  rw [e.duration_eq]
  ring

/-- Construct the execution prefix by grouping the jumps around zero-time
visits into discrete blocks. A terminal goal jump starts from the last
flow endpoint. -/
theorem prelim_goal (goal : e.goal) :
    ∃ aug : FiniteSignal T.HAVar,
      aug.reindex (Sum.inl : T.realVariables → T.HAVar) = σ.reindex Subtype.val ∧
      (A).PrelimReachesStateOrFinalJump aug (T.canonicalGoal h τ) := by
  let i : Fin e.n := ⟨0,e.nonempty⟩
  have assembled : ∃ a, Relation.ReflTransGen (A).DiscreteStep (e.start i) a ∧
      Nonempty (ProjectedFlowWord (A) (σ.reindex Subtype.val) (Sum.inl : T.realVariables → T.HAVar)
        a (e.time 0) (e.finish e.last) e.cut) := by
    refine ProjectedFlowWord.ofVisits e.nonempty e.start e.finish e.time ?_ ?_ ?_ e.last_positive
    · intro j live
      exact e.discreteStep ⟨j.val,by omega⟩
    · intro j same
      exact e.start_eq_finish_of_zero j ((e.duration_zero_iff j).2 same)
    · intro j different
      exact e.flowPiece j
        (pos_iff_ne_zero.2 (fun zero => different ((e.duration_zero_iff j).1 zero)))
  obtain ⟨a,lead,⟨word⟩⟩ := assembled
  let extend (v : T.realVariables → ℝ) : T.HAVar → ℝ := Sum.elim v (fun _ => 0)
  obtain ⟨aug,out,horizon,projects,_,_,final,boundary,_,_⟩ := word.toExecution
    extend (fun _ _ => rfl) (e.start i) e.initial
    e.first_zero lead (e.horizon.symm ▸ e.stop_le)
  have same : aug.reindex (Sum.inl : T.realVariables → T.HAVar) = σ.reindex Subtype.val := by
    rcases aug with ⟨r,pr,val⟩
    rcases σ with ⟨s,ps,signal⟩
    dsimp only [FiniteSignal.reindex] at horizon
    subst r
    dsimp only [FiniteSignal.reindex]
    congr 1
    funext t x
    exact projects t t rfl x
  refine ⟨aug,same,out.reaches_of_goalAtEnd ?_⟩
  rcases goal with here | ⟨atHorizon,target,mem,step⟩
  · exact Or.inl (final.symm ▸ here)
  · have stop : out.ReachesHorizon :=
      boundary.trans (atHorizon.trans (e.horizon.symm.trans horizon.symm))
    exact Or.inr ⟨stop,target,mem,by simpa only [final] using step⟩

end Tableau.TableauExecution

end STLTableau.Section4
