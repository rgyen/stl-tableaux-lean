import STLTableaux.Tableau.Stability.GeneratorStability
import STLTableaux.Closure.Residual.FreshNormalization

/-! Capture-avoiding clock renaming for the faithful mixed transition model.
Only syntactic reset binders generate alpha equivalence. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}

namespace Predicate

def rename (e : Equiv.Perm Clock) : Predicate Clock Var → Predicate Clock Var
  | .plain φ => .plain φ
  | .upper c b k I φ => .upper (e c) b k I φ
  | .bounded c d b q k I φ => .bounded (e c) (e d) b q k I φ

@[simp] theorem holds_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var)
    (σ : FiniteSignal Var) (J : MarkedInterval) (α : ClockValuation Clock) :
    (p.rename e).holds σ J α ↔ p.holds σ J (α ∘ e) := by
  cases p with
  | plain => rfl
  | upper c b k I φ => cases I <;> cases k <;> rfl
  | bounded c d b q k I φ => cases I <;> cases k <;> rfl

@[simp] theorem invariant_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (hk : k.1 < P.size) :
    (p.rename e).Invariant σ P α k hk ↔ p.Invariant σ P (α ∘ e) k hk := by
  cases p with
  | plain => rfl
  | upper c b kind I φ => cases I <;> cases kind <;> rfl
  | bounded c d b q kind I φ => cases I <;> cases kind <;> rfl

@[simp] theorem formula_rename (e : Equiv.Perm Clock) (p : Predicate Clock Var) :
    (p.rename e).formula = p.formula := by
  cases p with
  | plain => rfl
  | upper c b kind I φ => cases kind <;> rfl
  | bounded c d b q kind I φ => cases kind <;> rfl

end Predicate
namespace Local

def rename (e : Equiv.Perm Clock) : Local Clock Var → Local Clock Var
  | .terminal => .terminal
  | .marker m => .marker m
  | .predicate p => .predicate (p.rename e)

@[simp] theorem holds_rename (e : Equiv.Perm Clock) (l : Local Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (l.rename e).holds σ P α k ↔ l.holds σ P (α ∘ e) k := by
  cases l with
  | terminal => rfl
  | marker => rfl
  | predicate p =>
      by_cases hk : k.1 < P.size
      · simpa only [rename, holds, toJudgement, Judgement.holds, dif_pos hk] using
          Predicate.holds_rename e p σ (P.interval ⟨k.1,hk⟩) α
      · simp [rename, holds, toJudgement, Judgement.holds, hk]

@[simp] theorem freeClocks_rename (e : Equiv.Perm Clock) (l : Local Clock Var) :
    (l.rename e).freeClocks = e '' l.freeClocks := by
  cases l with
  | terminal => simp [rename, freeClocks, toJudgement, Judgement.freeClocks]
  | marker => simp [rename, freeClocks, toJudgement, Judgement.freeClocks]
  | predicate p => cases p <;>
      simp [rename, Predicate.rename, freeClocks, toJudgement, Judgement.freeClocks,
        Set.image_insert_eq, Set.image_singleton]

theorem freeClocks_finite (l : Local Clock Var) : l.freeClocks.Finite := by
  cases l with
  | terminal => exact Set.finite_empty
  | marker => exact Set.finite_empty
  | predicate p => cases p <;> simp [freeClocks, toJudgement, Judgement.freeClocks]

end Local
namespace Guard

def rename (e : Equiv.Perm Clock) (g : Guard Clock) : Guard Clock := { g with clock := e g.clock }
@[simp] theorem holds_rename (e : Equiv.Perm Clock) (g : Guard Clock) (α : ClockValuation Clock) :
    (g.rename e).holds α ↔ g.holds (α ∘ e) := Iff.rfl

end Guard
namespace StateForm

def rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) : StateForm Clock Var :=
  ⟨Guard.rename e '' S.guards, S.guards_finite.image _, S.resets.rename e,
    Local.rename e '' S.locals, S.locals_finite.image _⟩

def alphaReset (e : Equiv.Perm Clock) (S : StateForm Clock Var) : StateForm Clock Var :=
  { S.rename e with guards := S.guards, guards_finite := S.guards_finite }

theorem localClocks_finite (S : StateForm Clock Var) : S.localClocks.Finite := by
  have he : S.localClocks = ⋃ l ∈ S.locals, l.freeClocks := by ext c; simp [localClocks]
  rw [he]
  exact S.locals_finite.biUnion (fun l _ => l.freeClocks_finite)

theorem freeClocks_finite (S : StateForm Clock Var) : S.freeClocks.Finite := by
  apply Set.Finite.union
  · exact (S.guards_finite.image Guard.clock).subset (by rintro c ⟨g,hg,rfl⟩; exact ⟨g,hg,rfl⟩)
  · exact S.localClocks_finite.sdiff

@[simp] theorem localClocks_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.rename e).localClocks = e '' S.localClocks := by
  ext c
  simp only [localClocks, rename, Set.mem_setOf_eq, Set.mem_image, Local.freeClocks_rename]
  aesop

@[simp] theorem localClocks_alphaReset (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.alphaReset e).localClocks = e '' S.localClocks := S.localClocks_rename e

@[simp] theorem freeClocks_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock) :
    (S.rename e).freeClocks = e '' S.freeClocks := by
  have hg : (S.rename e).guardClocks = e '' S.guardClocks := by
    ext c; simp [guardClocks, rename, Guard.rename, Set.mem_image]; aesop
  rw [freeClocks,hg,localClocks_rename]
  change _ ∪ (_ \ (S.resets.rename e).clocks) = _
  rw [ClockResetSet.clocks_rename, ← Set.image_sdiff e.injective, ← Set.image_union]
  rfl

theorem holds_rename (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.rename e).holds σ P α k ↔ S.holds σ P (α ∘ e) k := by
  simp only [rename, holds, Set.forall_mem_image, Guard.holds_rename, Local.holds_rename,
    ClockResetSet.apply_rename]

theorem alphaReset_holds (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (S.alphaReset e).holds σ P α k ↔ S.holds σ P α k := by
  simp only [alphaReset, rename, holds, Set.forall_mem_image, Local.holds_rename,
    ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  apply Local.holds_congr_of_agree
  exact fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c ⟨l,hl,hc⟩

theorem alphaReset_freeClocks (S : StateForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c) :
    (S.alphaReset e).freeClocks = S.freeClocks := by
  have hi : e '' (S.localClocks \ S.resets.clocks) = S.localClocks \ S.resets.clocks := by
    ext c
    constructor
    · rintro ⟨x,hx,rfl⟩; simpa only [hfix x hx] using hx
    · intro hc; exact ⟨c,hc,hfix c hc⟩
  change S.guardClocks ∪ ((S.rename e).localClocks \ (S.resets.rename e).clocks) = _
  rw [localClocks_rename, ClockResetSet.clocks_rename, ← Set.image_sdiff e.injective, hi]
  rfl

end StateForm
namespace TransitionForm

def alphaOuter (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var) :
    TransitionForm Clock Var :=
  ⟨Φ.current.alphaReset e, Φ.nextPart.map (StateForm.rename e)⟩

def alphaNext (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var) :
    TransitionForm Clock Var := { Φ with nextPart := Φ.nextPart.map (StateForm.alphaReset e) }

def boundClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  Φ.current.resets.clocks ∪ match Φ.nextPart with | none => ∅ | some N => N.resets.clocks

def allClocks (Φ : TransitionForm Clock Var) : Set Clock := Φ.freeClocks ∪ Φ.boundClocks

theorem bodyFreeClocks_finite (Φ : TransitionForm Clock Var) : Φ.bodyFreeClocks.Finite := by
  apply Set.Finite.union Φ.current.localClocks_finite
  cases hn : Φ.nextPart with
  | none => exact Set.finite_empty
  | some N => exact N.freeClocks_finite

theorem freeClocks_finite (Φ : TransitionForm Clock Var) : Φ.freeClocks.Finite := by
  apply Set.Finite.union
  · exact (Φ.current.guards_finite.image Guard.clock).subset
      (by rintro c ⟨g,hg,rfl⟩; exact ⟨g,hg,rfl⟩)
  · exact Φ.bodyFreeClocks_finite.sdiff

theorem boundClocks_finite (Φ : TransitionForm Clock Var) : Φ.boundClocks.Finite := by
  apply Set.Finite.union Φ.current.resets.finite_domain
  cases hn : Φ.nextPart with
  | none => exact Set.finite_empty
  | some N => exact N.resets.finite_domain

theorem allClocks_finite (Φ : TransitionForm Clock Var) : Φ.allClocks.Finite :=
  Φ.freeClocks_finite.union Φ.boundClocks_finite

theorem alphaNext_holds (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaNext e).holds σ P α k ↔ Φ.holds σ P α k := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, holds, hn]
  | some N => simp [alphaNext, holds, hn, N.alphaReset_holds e (hfix N hn)]

theorem alphaNext_freeClocks (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    (Φ.alphaNext e).freeClocks = Φ.freeClocks := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, freeClocks, bodyFreeClocks, hn]
  | some N => simp [alphaNext, freeClocks, bodyFreeClocks, hn,
      N.alphaReset_freeClocks e (hfix N hn)]

theorem alphaOuter_holds (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) :
    (Φ.alphaOuter e).holds σ P α k ↔ Φ.holds σ P α k := by
  have hagree := Φ.current.resets.apply_pullback_agree e Φ.bodyFreeClocks hfix α
  simp only [alphaOuter, holds, StateForm.alphaReset, StateForm.rename, StateForm.holds,
    Set.forall_mem_image, Local.holds_rename, ClockResetSet.apply_rename]
  apply and_congr
  · apply and_congr Iff.rfl
    apply forall_congr'
    intro l
    apply forall_congr'
    intro hl
    exact Local.holds_congr_of_agree l σ P _ _ k
      (fun c hc => hagree c (Or.inl ⟨l,hl,hc⟩))
  · cases hn : Φ.nextPart with
    | none => rfl
    | some N =>
        simp only [Option.map_some]
        split
        · change (N.rename e).holds σ P _ _ ↔ N.holds σ P _ _
          rw [StateForm.holds_rename]
          have he : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
              (STLTableau.Judgement.duration P ⟨k.1,‹_›⟩) ∘ e =
              ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
                (STLTableau.Judgement.duration P ⟨k.1,‹_›⟩) := by
            funext c
            exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,‹_›⟩)
              (congrFun (Φ.current.resets.apply_rename e α) c)
          rw [he]
          apply StateForm.holds_congr_of_agree
          intro c hc
          exact congrArg (fun x => x + STLTableau.Judgement.duration P ⟨k.1,‹_›⟩)
            (hagree c (Or.inr (by simpa only [hn] using hc)))
        · rfl

theorem alphaOuter_bodyFreeClocks (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock) :
    (Φ.alphaOuter e).bodyFreeClocks = e '' Φ.bodyFreeClocks := by
  cases hn : Φ.nextPart with
  | none => simp [alphaOuter,bodyFreeClocks,hn]
  | some N => simp [alphaOuter,bodyFreeClocks,hn,Set.image_union]

theorem alphaOuter_freeClocks (Φ : TransitionForm Clock Var) (e : Equiv.Perm Clock)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c) :
    (Φ.alphaOuter e).freeClocks = Φ.freeClocks := by
  have hi : e '' (Φ.bodyFreeClocks \ Φ.current.resets.clocks) =
      Φ.bodyFreeClocks \ Φ.current.resets.clocks := by
    ext c
    constructor
    · rintro ⟨x,hx,rfl⟩; simpa only [hfix x hx] using hx
    · intro hc; exact ⟨c,hc,hfix c hc⟩
  change Φ.current.guardClocks ∪
      ((Φ.alphaOuter e).bodyFreeClocks \ (Φ.current.resets.rename e).clocks) = _
  rw [alphaOuter_bodyFreeClocks,ClockResetSet.clocks_rename,← Set.image_sdiff e.injective,hi]
  rfl

inductive AlphaEquivalent : TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | refl (Φ) : AlphaEquivalent Φ Φ
  | outer (Φ) (e : Equiv.Perm Clock)
      (hf : ∀ c ∈ Φ.bodyFreeClocks \ Φ.current.resets.clocks, e c = c) :
      AlphaEquivalent (Φ.alphaOuter e) Φ
  | next (Φ) (e : Equiv.Perm Clock)
      (hf : ∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
      AlphaEquivalent (Φ.alphaNext e) Φ
  | symm {Φ Ψ} : AlphaEquivalent Φ Ψ → AlphaEquivalent Ψ Φ
  | trans {Φ Ψ Χ} : AlphaEquivalent Φ Ψ → AlphaEquivalent Ψ Χ → AlphaEquivalent Φ Χ

theorem AlphaEquivalent.holds {Φ Ψ : TransitionForm Clock Var} (h : AlphaEquivalent Φ Ψ)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) : Φ.holds σ P α k ↔ Ψ.holds σ P α k := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_holds e hf σ P α k
  | next Φ e hf => exact Φ.alphaNext_holds e hf σ P α k
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem AlphaEquivalent.freeClocks {Φ Ψ : TransitionForm Clock Var} (h : AlphaEquivalent Φ Ψ) :
    Φ.freeClocks = Ψ.freeClocks := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_freeClocks e hf
  | next Φ e hf => exact Φ.alphaNext_freeClocks e hf
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem exists_fresh_alpha [Infinite Clock] (Φ : TransitionForm Clock Var)
    (U : Set Clock) (hU : U.Finite) :
    ∃ Φa, AlphaEquivalent Φa Φ ∧ Disjoint Φa.boundClocks U := by
  obtain ⟨e,he,hd⟩ := STLTableau.exists_fresh_clock_permutation Φ.current.resets.clocks
    (Φ.bodyFreeClocks \ Φ.current.resets.clocks) U Φ.current.resets.finite_domain
    Φ.bodyFreeClocks_finite.sdiff hU (Set.disjoint_left.2 (fun c hc hf => hf.2 hc))
  let F := Φ.alphaOuter e
  have hF : AlphaEquivalent F Φ := .outer Φ e he
  have hcurrent : Disjoint F.current.resets.clocks U := by
    simpa [F,alphaOuter,StateForm.alphaReset,StateForm.rename] using hd
  cases hn : F.nextPart with
  | none => exact ⟨F,hF,by simpa [boundClocks,hn] using hcurrent⟩
  | some N =>
      obtain ⟨d,hfix,hfresh⟩ := STLTableau.exists_fresh_clock_permutation N.resets.clocks
        (N.localClocks \ N.resets.clocks) U N.resets.finite_domain
        N.localClocks_finite.sdiff hU (Set.disjoint_left.2 (fun c hc hf => hf.2 hc))
      have hf : ∀ M, F.nextPart = some M →
          ∀ c ∈ M.localClocks \ M.resets.clocks, d c = c := by
        intro M hm
        have heq : M = N := Option.some.inj (hm.symm.trans hn)
        subst M
        exact hfix
      exact ⟨F.alphaNext d,(AlphaEquivalent.next F d hf).trans hF,
        by simpa [alphaNext,boundClocks,hn,StateForm.alphaReset,StateForm.rename]
          using hcurrent.union_left hfresh⟩

end TransitionForm
end STLTableau.Section3
