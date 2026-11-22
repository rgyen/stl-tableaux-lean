import STLTableaux.Syntax.Section3Judgements

/-! Transition forms (Definition 4.1) and their satisfaction under Section 3. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

structure Guard (Clock : Type*) where
  clock : Clock
  relation : ClockRelation
  bound : NNReal

namespace Guard

def holds (g : Guard Clock) (α : ClockValuation Clock) : Prop :=
  g.relation.Holds (α g.clock) g.bound

def toJudgement (g : Guard Clock) : Judgement Clock Var :=
  .clock g.clock g.relation g.bound

end Guard

inductive Local (Clock Var : Type*) where
  | terminal
  | marker (m : Marker)
  | predicate (p : Predicate Clock Var)

namespace Local

def toJudgement : Local Clock Var → Judgement Clock Var
  | .terminal => .terminal
  | .marker m => .marker m
  | .predicate p => .predicate p

def freeClocks (l : Local Clock Var) : Set Clock := l.toJudgement.freeClocks

def holds (l : Local Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop :=
  Judgement.holds σ P α k l.toJudgement

theorem holds_congr_of_agree (l : Local Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (h : ∀ c ∈ l.freeClocks, α c = β c) :
    l.holds σ P α k ↔ l.holds σ P β k :=
  Judgement.holds_congr_of_agree h σ P k

end Local

/-- A state form `C,Λ.L`: guards are outside the reset scope. -/
structure StateForm (Clock Var : Type*) where
  guards : Set (Guard Clock)
  guards_finite : guards.Finite
  resets : ClockResetSet Clock
  locals : Set (Local Clock Var)
  locals_finite : locals.Finite

namespace StateForm

def guardClocks (S : StateForm Clock Var) : Set Clock :=
  {c | ∃ g ∈ S.guards, g.clock = c}

def localClocks (S : StateForm Clock Var) : Set Clock :=
  {c | ∃ l ∈ S.locals, c ∈ l.freeClocks}

def freeClocks (S : StateForm Clock Var) : Set Clock :=
  S.guardClocks ∪ (S.localClocks \ S.resets.clocks)

def holds (S : StateForm Clock Var) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop :=
  (∀ g ∈ S.guards, g.holds α) ∧
    ∀ l ∈ S.locals, l.holds σ P (S.resets.apply α) k

end StateForm

/-- The six components `C,Λ.(L,X(C',Λ'.L'))`; absent next is permitted. -/
structure TransitionForm (Clock Var : Type*) where
  current : StateForm Clock Var
  nextPart : Option (StateForm Clock Var)

namespace TransitionForm

/-- Free clocks inside the outer reset, before that reset binds them. -/
def bodyFreeClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  Φ.current.localClocks ∪ match Φ.nextPart with
    | none => ∅
    | some N => N.freeClocks

def freeClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  Φ.current.guardClocks ∪ (Φ.bodyFreeClocks \ Φ.current.resets.clocks)

def holds (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Prop :=
  Φ.current.holds σ P α k ∧ match Φ.nextPart with
    | none => True
    | some N => if hk : k.1 < P.size then
        N.holds σ P
          (ClockResetSet.elapse (Φ.current.resets.apply α)
            (STLTableau.Judgement.duration P ⟨k.1, hk⟩)) ⟨k.1 + 1, by omega⟩
      else False

end TransitionForm

/-- Inclusion of reset graphs, retaining their assigned values. -/
def ResetIncluded (Λ Μ : ClockResetSet Clock) : Prop :=
  ∀ c a, Λ.value c = some a → Μ.value c = some a

structure ComponentsIncluded (S T : StateForm Clock Var) : Prop where
  guards : S.guards ⊆ T.guards
  resets : ResetIncluded S.resets T.resets
  locals : S.locals ⊆ T.locals

/-- Definition 4.3 (syntactic subsumption). The next-component conditions
apply when the source has a next component. -/
structure SyntacticallySubsumed (Φ Ψ : TransitionForm Clock Var) : Prop where
  current : ComponentsIncluded Φ.current Ψ.current
  outerFresh : Disjoint Ψ.current.resets.clocks
    (Φ.bodyFreeClocks \ Φ.current.resets.clocks)
  next : ∀ N, Φ.nextPart = some N → ∃ M, Ψ.nextPart = some M ∧
    ComponentsIncluded N M ∧ Disjoint M.resets.clocks (N.localClocks \ N.resets.clocks)

/-- Irrelevant reset extension, allowing the incoming valuations to differ
only outside the source's unbound clocks. -/
theorem reset_apply_agree {Λ Μ : ClockResetSet Clock} (hinc : ResetIncluded Λ Μ)
    (α β : ClockValuation Clock) (D : Set Clock)
    (hfresh : Disjoint Μ.clocks (D \ Λ.clocks))
    (hval : ∀ c ∈ D \ Λ.clocks, α c = β c) :
    ∀ c ∈ D, Λ.apply α c = Μ.apply β c := by
  intro c hc
  cases hΛ : Λ.value c with
  | some a => simp [ClockResetSet.apply, hΛ, hinc c a hΛ]
  | none =>
      have hcΛ : c ∉ Λ.clocks := by
        rintro ⟨a, ha⟩
        rw [hΛ] at ha
        cases ha
      have hcΜ : c ∉ Μ.clocks := fun hm => Set.disjoint_left.1 hfresh hm ⟨hc, hcΛ⟩
      have hΜ : Μ.value c = none := by
        cases h : Μ.value c with
        | none => rfl
        | some a => exact (hcΜ ⟨a, h⟩).elim
      simpa only [ClockResetSet.apply, hΛ, hΜ] using hval c ⟨hc, hcΛ⟩

namespace StateForm

theorem holds_of_included {S T : StateForm Clock Var} (h : ComponentsIncluded S T)
    (hfresh : Disjoint T.resets.clocks (S.localClocks \ S.resets.clocks))
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α β : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ S.freeClocks, α c = β c) (hs : T.holds σ P β k) :
    S.holds σ P α k := by
  constructor
  · intro g hg
    have hc := hagree g.clock (Or.inl ⟨g, hg, rfl⟩)
    simpa only [Guard.holds, hc] using hs.1 g (h.guards hg)
  · have he := reset_apply_agree h.resets α β S.localClocks hfresh
      (fun c hc => hagree c (Or.inr hc))
    intro l hl
    exact (l.holds_congr_of_agree σ P _ _ k (fun c hc => he c ⟨l, hl, hc⟩)).2
      (hs.2 l (h.locals hl))

theorem holds_congr_of_agree (S : StateForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ S.freeClocks, α c = β c) :
    S.holds σ P α k ↔ S.holds σ P β k := by
  have hi : ComponentsIncluded S S := ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩
  have hf : Disjoint S.resets.clocks (S.localClocks \ S.resets.clocks) :=
    Set.disjoint_left.2 (fun _ hc hd => hd.2 hc)
  exact ⟨holds_of_included hi hf σ P β α k (fun c hc => (hagree c hc).symm),
    holds_of_included hi hf σ P α β k hagree⟩

end StateForm

/-- Lemma 4.5 (soundness of syntactic subsumption). Satisfaction of the
target implies satisfaction of the source at every partition position. -/
theorem SyntacticallySubsumed.sound {Φ Ψ : TransitionForm Clock Var}
    (h : SyntacticallySubsumed Φ Ψ) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hs : Ψ.holds σ P α k) :
    Φ.holds σ P α k := by
  have hcurrentFresh : Disjoint Ψ.current.resets.clocks
      (Φ.current.localClocks \ Φ.current.resets.clocks) := by
    apply Set.disjoint_left.2
    intro c hc hcΦ
    apply Set.disjoint_left.1 h.outerFresh hc
    exact ⟨Or.inl hcΦ.1, hcΦ.2⟩
  refine ⟨StateForm.holds_of_included h.current hcurrentFresh σ P α α k
    (fun _ _ => rfl) hs.1, ?_⟩
  cases hn : Φ.nextPart with
  | none => trivial
  | some N =>
      obtain ⟨M, hm, hNM, hfresh⟩ := h.next N hn
      simp only [TransitionForm.holds, hm] at hs
      dsimp only
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk] at hs ⊢
        apply StateForm.holds_of_included hNM hfresh σ P _ _ _ ?_ hs.2
        have he := reset_apply_agree h.current.resets α α Φ.bodyFreeClocks h.outerFresh
          (fun _ _ => rfl)
        intro c hc
        have hb : c ∈ Φ.bodyFreeClocks := by
          change c ∈ Φ.current.localClocks ∪ _
          exact Or.inr (by simpa only [hn] using hc)
        simp only [ClockResetSet.elapse, he c hb]
      · simp only [dif_neg hk] at hs ⊢
        exact hs.2

namespace TransitionForm

theorem holds_congr_of_agree (Φ : TransitionForm Clock Var) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α β : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P)
    (hagree : ∀ c ∈ Φ.freeClocks, α c = β c) :
    Φ.holds σ P α k ↔ Φ.holds σ P β k := by
  have hcur : ∀ c ∈ Φ.current.freeClocks, α c = β c := by
    intro c hc
    rcases hc with hc | hc
    · exact hagree c (Or.inl hc)
    · exact hagree c (Or.inr ⟨Or.inl hc.1, hc.2⟩)
  have hf : Disjoint Φ.current.resets.clocks
      (Φ.bodyFreeClocks \ Φ.current.resets.clocks) :=
    Set.disjoint_left.2 (fun _ hc hd => hd.2 hc)
  have he := reset_apply_agree (fun _ _ h => h) α β Φ.bodyFreeClocks hf
    (fun c hc => hagree c (Or.inr hc))
  apply and_congr (Φ.current.holds_congr_of_agree σ P α β k hcur)
  cases hn : Φ.nextPart with
  | none => rfl
  | some N =>
      by_cases hk : k.1 < P.size
      · simp only [dif_pos hk]
        apply N.holds_congr_of_agree
        intro c hc
        have hb : c ∈ Φ.bodyFreeClocks := by
          change c ∈ Φ.current.localClocks ∪ _
          exact Or.inr (by simpa only [hn] using hc)
        simp only [ClockResetSet.elapse, he c hb]
      · simp only [dif_neg hk]

end TransitionForm

end STLTableau.Section3
