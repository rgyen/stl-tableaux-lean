import STLTableaux.Automata.Execution.ObservedFlowExecution

namespace STLTableau.HybridAutomaton
variable {Mode Label V X : Type*}
variable (H : HybridAutomaton Mode Label V) (ρ : FiniteSignal X) (ι : X → V)

/-- An actual positive flow, observing only the supplied physical coordinates. -/
structure ProjectedFlowPiece where
  left : ℝ
  duration : NNReal
  positive : 0 < duration
  start : H.State
  finish : H.State
  curve : HybridFlow.Curve V duration
  step : H.ContinuousStep start finish duration curve
  observe : ∀ (t : ρ.Time) (u : Set.Icc (0 : ℝ) duration),
    left + u.val = t.val → u.val < duration →
    ∀ x, curve u (ι x) = ρ.value t x

namespace ProjectedFlowPiece
variable {H ρ ι}
def VisitsState (p : ProjectedFlowPiece H ρ ι) (s : H.State) : Prop :=
  ∃ u, s.val = (p.start.val.1, p.curve u)
def Realizes (p : ProjectedFlowPiece H ρ ι) (values : ρ.Time → V → ℝ) : Prop :=
  ∀ (t : ρ.Time) (u : Set.Icc (0 : ℝ) p.duration),
    p.left + u.val = t.val → u.val < p.duration →
    values t = p.curve u
end ProjectedFlowPiece

inductive ProjectedFlowWord : H.State → ℝ → H.State → ℝ → Type _ where
  | last (p : ProjectedFlowPiece H ρ ι) :
      ProjectedFlowWord p.start p.left p.finish (p.left + p.duration)
  | cons (p : ProjectedFlowPiece H ρ ι) {a b z}
      (jumps : Relation.ReflTransGen H.DiscreteStep p.finish a)
      (tail : ProjectedFlowWord a (p.left + p.duration) b z) :
      ProjectedFlowWord p.start p.left b z

namespace ProjectedFlowWord
variable {H ρ ι}
def start {a b : H.State} {l r : ℝ} (_ : ProjectedFlowWord H ρ ι a l b r) : H.State := a
def VisitsState : {a b : H.State} → {l r : ℝ} →
    ProjectedFlowWord H ρ ι a l b r → H.State → Prop
  | _, _, _, _, .last p, s => p.VisitsState s
  | _, _, _, _, .cons p _ tail, s => p.VisitsState s ∨
      (Relation.ReflTransGen H.DiscreteStep p.finish s ∧
        Relation.ReflTransGen H.DiscreteStep s tail.start) ∨ tail.VisitsState s
def Realizes : {a b : H.State} → {l r : ℝ} →
    ProjectedFlowWord H ρ ι a l b r → (ρ.Time → V → ℝ) → Prop
  | _, _, _, _, .last p, values => p.Realizes values
  | _, _, _, _, .cons p _ tail, values => p.Realizes values ∧ tail.Realizes values

/-- Assemble adjacent visits into a positive flow word. A zero-time visit has
the same start and finish, so its outgoing jump becomes part of a discrete
block. The last visit supplies the final positive flow. -/
theorem ofVisits {n : ℕ} (nonempty : 0 < n)
    (start finish : Fin n → H.State) (time : Fin (n + 1) → ℝ)
    (jump : ∀ (i : Fin n) (hi : i.val + 1 < n),
      H.DiscreteStep (finish i) (start ⟨i.val + 1, hi⟩))
    (still : ∀ i : Fin n, time i.castSucc = time i.succ → start i = finish i)
    (flow : ∀ i : Fin n, time i.castSucc ≠ time i.succ →
      ∃ p : ProjectedFlowPiece H ρ ι,
        p.start = start i ∧ p.finish = finish i ∧
        p.left = time i.castSucc ∧ p.left + (p.duration : ℝ) = time i.succ)
    (last_positive : ∀ i : Fin n, i.val + 1 = n → time i.castSucc ≠ time i.succ) :
    ∃ a, Relation.ReflTransGen H.DiscreteStep (start ⟨0, nonempty⟩) a ∧
      Nonempty (ProjectedFlowWord H ρ ι a (time 0) (finish ⟨n - 1, by omega⟩)
        (time (Fin.last n))) := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  let P (k : ℕ) := ∀ (hk : k < n), ∃ a,
    Relation.ReflTransGen H.DiscreteStep (start ⟨k, hk⟩) a ∧
    Nonempty (ProjectedFlowWord H ρ ι a (time (⟨k, hk⟩ : Fin n).castSucc)
      (finish last) (time (Fin.last n)))
  have suffix (k : ℕ) (hk : k < n) : P k := by
    apply Nat.decreasingInduction (motive := fun j _ => P j) (n := n - 1) (m := k)
    · intro k _less ih hk
      let i : Fin n := ⟨k, hk⟩
      let j : Fin n := ⟨k + 1, by omega⟩
      obtain ⟨a, lead, ⟨word⟩⟩ := ih j.isLt
      have link := lead.head (jump i j.isLt)
      have adjacent : time i.succ = time j.castSucc := rfl
      by_cases zero : time i.castSucc = time i.succ
      · exact ⟨a, (still i zero).symm ▸ link, ⟨(zero.trans adjacent).symm ▸ word⟩⟩
      · obtain ⟨p, ps, pf, pl, pr⟩ := flow i zero
        have link' : Relation.ReflTransGen H.DiscreteStep p.finish a := pf.symm ▸ link
        have word' : ProjectedFlowWord H ρ ι a (p.left + (p.duration : ℝ))
            (finish last) (time (Fin.last n)) := (pr.trans adjacent).symm ▸ word
        exact ⟨start i, .refl, ⟨by simpa only [ps, pl] using ProjectedFlowWord.cons p link' word'⟩⟩
    · intro _hk
      have hn : last.val + 1 = n := by dsimp [last]; omega
      obtain ⟨p, ps, pf, pl, pr⟩ := flow last (last_positive last hn)
      have last_end : last.succ = Fin.last n := Fin.ext hn
      have end_time := pr.trans (congrArg time last_end)
      have word := ProjectedFlowWord.last p
      rw [ps, pf, end_time, pl] at word
      exact ⟨start last, .refl, ⟨word⟩⟩
    · omega
  exact suffix 0 nonempty nonempty

private structure Packed (a : H.State) (l : ℝ) (b : H.State) (r : ℝ) where
  k : ℕ
  ps : Fin (k+1) → ProjectedFlowPiece H ρ ι
  firstS : (ps 0).start = a
  firstL : (ps 0).left = l
  lastS : (ps (Fin.last k)).finish = b
  lastR : (ps (Fin.last k)).left + (ps (Fin.last k)).duration = r
  time : ∀ i : Fin k, (ps i.castSucc).left + (ps i.castSucc).duration = (ps i.succ).left
  jumps : ∀ i : Fin k,
    Relation.ReflTransGen H.DiscreteStep (ps i.castSucc).finish (ps i.succ).start

private theorem pack {a l b r} (word : ProjectedFlowWord H ρ ι a l b r) :
    ∃ s : Packed (H := H) (ρ := ρ) (ι := ι) a l b r,
      ∀ values, (∀ i, (s.ps i).Realizes values) → word.Realizes values := by
  induction word with
  | last p =>
    exact ⟨⟨0, fun _ => p, rfl, rfl, rfl, rfl, Fin.elim0, Fin.elim0⟩,
      fun values obs => obs 0⟩
  | cons p jump rest ih =>
    obtain ⟨s, cover⟩ := ih
    let out : Packed (H := H) (ρ := ρ) (ι := ι) _ _ _ _ :=
      ⟨s.k + 1, Fin.cases p s.ps, rfl, rfl, (by exact s.lastS), (by exact s.lastR),
        (by intro i; refine Fin.cases ?_ (fun j => ?_) i
            · exact s.firstL.symm
            · exact s.time j),
        (by intro i; refine Fin.cases ?_ (fun j => ?_) i
            · exact s.firstS.symm ▸ jump
            · exact s.jumps j)⟩
    refine ⟨out, ?_⟩
    intro values obs
    exact ⟨obs 0, cover values (fun i => obs i.succ)⟩

namespace Packed
variable {a b : H.State} {l r : ℝ} (s : Packed (ι := ι) (H := H) (ρ := ρ) a l b r)
private def bounds (i : Fin (s.k + 2)) : ℝ :=
  Fin.lastCases r (fun i => (s.ps i).left) i

private theorem leftTime (i : Fin (s.k + 1)) : s.bounds i.castSucc = (s.ps i).left := by
  simp [bounds]
private theorem rightTime (i : Fin (s.k + 1)) :
    s.bounds i.succ = (s.ps i).left + (s.ps i).duration := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [bounds] using s.lastR.symm
  · change s.bounds j.succ.castSucc = _
    rw [s.leftTime]
    exact (s.time j).symm
private theorem boundsMono : StrictMono s.bounds := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [s.leftTime,s.rightTime]
  exact lt_add_of_pos_right _ (s.ps i).positive
private theorem boundsFirst : s.bounds 0 = l := (s.leftTime 0).trans s.firstL
private theorem boundsLast : s.bounds (Fin.last (s.k + 1)) = r := by simp [bounds]

private theorem seg_unique {t : ℝ} {i j : Fin (s.k + 1)}
    (hi : t ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ))
    (hj : t ∈ Set.Ico (s.bounds j.castSucc) (s.bounds j.succ)) : i = j := by
  rcases lt_trichotomy i j with h|he|h
  · have h' : i.succ ≤ j.castSucc := h
    exact (not_lt_of_ge (s.boundsMono.monotone h') (hj.1.trans_lt hi.2)).elim
  · exact he
  · have h' : j.succ ≤ i.castSucc := h
    exact (not_lt_of_ge (s.boundsMono.monotone h') (hi.1.trans_lt hj.2)).elim

private theorem seg_exists (t : ρ.Time) (h0 : l = 0) (ht : t.val < r) :
    ∃ i : Fin (s.k + 1), t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ) :=
  IntervalPartition.exists_boundary_piece s.bounds
    ⟨(s.boundsFirst.trans h0).le.trans t.property.1,
    ht.trans_eq s.boundsLast.symm⟩

private def localTime (t : ρ.Time) (i : Fin (s.k + 1))
    (ht : t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ)) :
    Set.Icc (0 : ℝ) (s.ps i).duration :=
  ⟨t.val - s.bounds i.castSucc,sub_nonneg.mpr ht.1, by
    rw [s.leftTime]; have := ht.2; rw [s.rightTime] at this; linarith⟩

private noncomputable def aug (extend : (X → ℝ) → V → ℝ)
    (h0 : l = 0) : FiniteSignal V :=
  ⟨ρ.horizon,ρ.horizon_pos,fun t => if ht : t.val < r then
    let i := (s.seg_exists t h0 ht).choose
    (s.ps i).curve (s.localTime t i (s.seg_exists t h0 ht).choose_spec)
    else extend (ρ.value t)⟩

private theorem obs (extend : (X → ℝ) → V → ℝ) (h0 : l = 0)
    (i : Fin (s.k + 1)) (t : (s.aug extend h0).Time)
    (ht : t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ)) :
    (s.aug extend h0).value t = (s.ps i).curve (s.localTime t i ht) := by
  have he : t.val < r :=
    ht.2.trans_le ((s.boundsMono.monotone (Fin.le_last _)).trans_eq s.boundsLast)
  simp only [aug,dif_pos he]
  have eq := s.seg_unique (s.seg_exists t h0 he).choose_spec ht
  subst i
  rfl


private theorem projects (extend : (X → ℝ) → V → ℝ)
    (law : ∀ v x, extend v (ι x) = v x) (h0 : l = 0) :
    ∀ (t : (s.aug extend h0).Time) (u : ρ.Time), t.val = u.val →
      ∀ x, (s.aug extend h0).value t (ι x) = ρ.value u x := by
  intro t u he x
  have eq : (t : ρ.Time) = u := Subtype.ext he
  subst u
  by_cases ht : t.val < r
  · obtain ⟨i, hi⟩ := s.seg_exists t h0 ht
    rw [s.obs extend h0 i t hi]
    apply (s.ps i).observe
    · change (s.ps i).left + (t.val - s.bounds i.castSucc) = t.val
      rw [s.leftTime]; ring
    · change t.val - s.bounds i.castSucc < (s.ps i).duration
      have := hi.2; rw [s.rightTime] at this; rw [s.leftTime]; linarith
  · simpa only [aug, dif_neg ht] using law (ρ.value t) x

private theorem realizes (extend : (X → ℝ) → V → ℝ) (h0 : l = 0)
    (i : Fin (s.k + 1)) :
    (s.ps i).Realizes (s.aug extend h0).value := by
  intro t u time before
  have ht : t.val ∈ Set.Ico (s.bounds i.castSucc) (s.bounds i.succ) := by
    rw [s.leftTime, s.rightTime]
    constructor <;> linarith [u.property.1]
  rw [s.obs extend h0 i t ht]
  apply congrArg (s.ps i).curve
  apply Subtype.ext
  change t.val - s.bounds i.castSucc = u.val
  rw [s.leftTime]
  linarith

end Packed

private theorem prependChain {σ : FiniteSignal V} (f : ObservedFlow H σ)
    {a b : H.State} {l r : ℝ}
    (tail : ObservedFlowChain H σ (Relation.ReflTransGen H.DiscreteStep) a l b r)
    (time : f.endTime = l) (jump : Relation.ReflTransGen H.DiscreteStep f.finish a) :
    ∃ out : ObservedFlowChain H σ (Relation.ReflTransGen H.DiscreteStep)
      f.start f.beginTime b r,
      ∀ s, f.VisitsState s ∨
        (Relation.ReflTransGen H.DiscreteStep f.finish s ∧
          Relation.ReflTransGen H.DiscreteStep s a) ∨
        tail.VisitsState s → out.VisitsState s := by
  induction tail with
  | single g =>
    refine ⟨.snoc (.single f) g time jump, ?_⟩
    intro s visit
    exact visit
  | snoc p g ht hs ih =>
    obtain ⟨q, preserve⟩ := ih time jump
    refine ⟨.snoc q g ht hs, ?_⟩
    intro s visit
    rcases visit with flow | middle | old | middle | flow
    · exact Or.inl (preserve s (Or.inl flow))
    · exact Or.inl (preserve s (Or.inr (Or.inl middle)))
    · exact Or.inl (preserve s (Or.inr (Or.inr old)))
    · exact Or.inr (Or.inl middle)
    · exact Or.inr (Or.inr flow)

private theorem toChain {a b : H.State} {l r : ℝ}
    (word : ProjectedFlowWord H ρ ι a l b r) (values : ρ.Time → V → ℝ)
    (observed : word.Realizes values) :
    let aug : FiniteSignal V := ⟨ρ.horizon, ρ.horizon_pos, values⟩
    ∃ out : ObservedFlowChain H aug (Relation.ReflTransGen H.DiscreteStep) a l b r,
      ∀ s, word.VisitsState s → out.VisitsState s := by
  let aug : FiniteSignal V := ⟨ρ.horizon, ρ.horizon_pos, values⟩
  let lift (p : ProjectedFlowPiece H ρ ι) (obs : p.Realizes values) :
      ObservedFlow H aug := {
    start := p.start, finish := p.finish, beginTime := p.left,
    endTime := p.left + p.duration, duration := p.duration, positive := p.positive,
    duration_eq := by ring, curve := p.curve, step := p.step,
    observe := by
      intro t ht
      apply obs
      · simp
      · linarith [ht.2] }
  induction word with
  | last p => exact ⟨.single (lift p observed), fun _ visit => visit⟩
  | cons p jump tail ih =>
    obtain ⟨q, preserve⟩ := ih observed.2
    obtain ⟨out, all⟩ := prependChain (lift p observed.1) q rfl jump
    refine ⟨out, ?_⟩
    intro s visit
    rcases visit with flow | middle | rest
    · exact all s (Or.inl flow)
    · exact all s (Or.inr (Or.inl middle))
    · exact all s (Or.inr (Or.inr (preserve s rest)))

/-- Assemble actual finite projected flows and genuine connectors. The
extension fills only the unobserved suffix; it supplies no transitions. -/
theorem toExecution {a b : H.State} {l r : ℝ}
    (word : ProjectedFlowWord H ρ ι a l b r)
    (extend : (X → ℝ) → V → ℝ) (law : ∀ v x, extend v (ι x) = v x)
    (initial : H.State) (hi : initial.val ∈ H.initial)
    (zero : l = 0) (first : Relation.ReflTransGen H.DiscreteStep initial a)
    (horizon : r ≤ ρ.horizon) :
    ∃ (aug : FiniteSignal V) (e : H.PrelimExecution aug),
      aug.horizon = ρ.horizon ∧
      (∀ (t : aug.Time) (u : ρ.Time), t.val = u.val →
        ∀ x, aug.value t (ι x) = ρ.value u x) ∧
      e.initialState = initial ∧ e.start ⟨0, e.nonempty⟩ = a ∧
      e.finalState = b ∧ e.boundary ⟨e.count, by omega⟩ = r ∧
      (∀ s, word.VisitsState s → e.VisitsState s) ∧
      (∀ s, Relation.ReflTransGen H.DiscreteStep initial s →
        Relation.ReflTransGen H.DiscreteStep s a → e.VisitsState s) := by
  obtain ⟨s, cover⟩ := pack word
  let aug := s.aug extend zero
  obtain ⟨chain, preserve⟩ := toChain word aug.value
    (cover aug.value (s.realizes extend zero))
  obtain ⟨normalized, retain⟩ := chain.normalize
  obtain ⟨e, ei, ef, el, et, visits⟩ := normalized.toExecution initial hi zero first horizon
  refine ⟨aug, e, rfl, s.projects extend law zero,
    ei, ef, el, et, ?_, ?_⟩
  · intro state visit
    exact visits state (retain state (preserve state visit))
  · intro state before after
    exact Or.inr (Or.inl ⟨ei.symm ▸ before, ef.symm ▸ after⟩)

run_elab do
  for ax in ← Lean.collectAxioms ``toExecution do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"
end ProjectedFlowWord
end STLTableau.HybridAutomaton
