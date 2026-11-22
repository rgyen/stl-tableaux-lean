/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Closure.Residual.AlphaConversion

/-! # Compatible transition forms up to alpha-conversion -/
namespace STLTableau
open scoped STL

namespace ClockConstraint
variable {Clock : Type*}
def rename (e : Equiv.Perm Clock) (g : ClockConstraint Clock) : ClockConstraint Clock :=
  { g with clock := e g.clock }
@[simp] theorem satisfies_rename (e : Equiv.Perm Clock) (g : ClockConstraint Clock)
    (α : ClockValuation Clock) : (g.rename e).Satisfies α ↔ g.Satisfies (α ∘ e) := Iff.rfl
end ClockConstraint

namespace Judgement
theorem isLocal_rename {Clock Var : Type*} (e : Equiv.Perm Clock)
    (Ψ : Judgement Clock Var) : (Ψ.rename e).IsLocal ↔ Ψ.IsLocal := by
  cases Ψ <;> rfl
theorem clocks_eq_freeClocks_of_local {Clock Var : Type*}
    {Ψ : Judgement Clock Var} (h : Ψ.IsLocal) : Ψ.clocks = Ψ.freeClocks := by
  cases Ψ <;> simp_all [IsLocal, clocks, freeClocks]
end Judgement

namespace ClockResetSet
theorem apply_pullback_agree {Clock : Type*} (e : Equiv.Perm Clock)
    (Λ : ClockResetSet Clock) (F : Set Clock)
    (hfix : ∀ c ∈ F \ Λ.clocks, e c = c) (α : ClockValuation Clock) :
    ∀ c ∈ F, Λ.apply (α ∘ e) c = Λ.apply α c := by
  intro c hc
  cases hv : Λ.value c with
  | some a => simp [apply, hv]
  | none =>
      have hnot : c ∉ Λ.clocks := by
        rintro ⟨a, ha⟩
        rw [hv] at ha
        cases ha
      simp [apply, hv, hfix c ⟨hc, hnot⟩]

theorem consistent_of_disjoint {Clock : Type*} {Λ Γ : ClockResetSet Clock}
    (h : Disjoint Λ.clocks Γ.clocks) : Λ.Consistent Γ := by
  intro c a b ha hb
  exact (Set.disjoint_left.1 h ⟨a, ha⟩ ⟨b, hb⟩).elim
end ClockResetSet

namespace StateForm
variable {Clock Var : Type*}

def localClocks (S : StateForm Clock Var) : Set Clock := ⋃ Ψ ∈ S.locals, Ψ.freeClocks

theorem localClocks_finite (S : StateForm Clock Var) : S.localClocks.Finite :=
  S.locals_finite.biUnion (fun Ψ _ => Ψ.freeClocks_finite)

theorem freeClocks_finite (S : StateForm Clock Var) : S.freeClocks.Finite :=
  (S.constraints_finite.image ClockConstraint.clock).union
    (S.locals_finite.biUnion (fun Ψ _ => Ψ.freeClocks_finite.sdiff))

def rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) : StateForm Clock Var where
  constraints := ClockConstraint.rename e '' S.constraints
  constraints_finite := S.constraints_finite.image _
  resets := S.resets.rename e
  locals := Judgement.rename e '' S.locals
  locals_finite := S.locals_finite.image _
  locals_are_local := by
    rintro _ ⟨Ψ, hΨ, rfl⟩
    exact (Ψ.isLocal_rename e).2 (S.locals_are_local Ψ hΨ)

theorem satisfies_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.rename e).Satisfies σ P α k ↔ S.Satisfies σ P (α ∘ e) k := by
  simp [rename, Satisfies, Judgement.satisfies_rename, ClockResetSet.apply_rename]

theorem freeClocks_rename (e : Equiv.Perm Clock) (S : StateForm Clock Var) :
    (S.rename e).freeClocks = e '' S.freeClocks := by
  ext c
  simp [rename, freeClocks, Judgement.freeClocks_rename,
    ClockConstraint.rename, Set.mem_image, Set.mem_iUnion]
  aesop

/-- Rename only this state's reset binders and their body; guards are outside. -/
def alphaReset (e : Equiv.Perm Clock) (S : StateForm Clock Var) : StateForm Clock Var :=
  { S.rename e with constraints := S.constraints, constraints_finite := S.constraints_finite }

theorem alphaReset_satisfies (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P) :
    (S.alphaReset e).Satisfies σ P α k ↔ S.Satisfies σ P α k := by
  simp only [alphaReset, rename, Satisfies, Set.forall_mem_image,
    Judgement.satisfies_rename, ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro Ψ
  apply forall_congr'
  intro hΨ
  exact Judgement.satisfies_congr_of_agree
    (fun c hc => S.resets.apply_pullback_agree e S.localClocks hfix α c
      (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩)) σ P k

theorem alphaReset_freeClocks (e : Equiv.Perm Clock) (S : StateForm Clock Var)
    (hfix : ∀ c ∈ S.localClocks \ S.resets.clocks, e c = c) :
    (S.alphaReset e).freeClocks = S.freeClocks := by
  have himage : e '' (S.localClocks \ S.resets.clocks) =
      S.localClocks \ S.resets.clocks := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hfix x hx] using hx
    · intro hc
      exact ⟨c, hc, hfix c hc⟩
  have hloc : (⋃ Ψ ∈ S.locals, Ψ.freeClocks \ S.resets.clocks) =
      S.localClocks \ S.resets.clocks := by ext c; simp [localClocks]; aesop
  simp only [alphaReset, rename, freeClocks,
    ClockResetSet.clocks_rename]
  congr 1
  rw [hloc, ← himage]
  ext c
  simp [localClocks, Set.mem_image, Set.mem_iUnion]
  aesop

end StateForm

namespace TransitionForm
variable {Clock Var : Type*}

def freeClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  (ClockConstraint.clock '' Φ.current.constraints) ∪ Φ.bodyFreeClocks

def boundClocks (Φ : TransitionForm Clock Var) : Set Clock :=
  Φ.current.resets.clocks ∪ match Φ.nextPart with
    | none => ∅
    | some N => N.resets.clocks

def allClocks (Φ : TransitionForm Clock Var) : Set Clock := Φ.freeClocks ∪ Φ.boundClocks

theorem bodyFreeClocks_finite (Φ : TransitionForm Clock Var) : Φ.bodyFreeClocks.Finite := by
  apply Set.Finite.sdiff
  apply Set.Finite.union Φ.current.localClocks_finite
  cases h : Φ.nextPart with
  | none => exact Set.finite_empty
  | some N => exact N.freeClocks_finite

theorem freeClocks_finite (Φ : TransitionForm Clock Var) : Φ.freeClocks.Finite :=
  (Φ.current.constraints_finite.image _).union Φ.bodyFreeClocks_finite

theorem boundClocks_finite (Φ : TransitionForm Clock Var) : Φ.boundClocks.Finite := by
  apply Set.Finite.union Φ.current.resets.finite_domain
  cases h : Φ.nextPart with
  | none => exact Set.finite_empty
  | some N => exact N.resets.finite_domain

theorem allClocks_finite (Φ : TransitionForm Clock Var) : Φ.allClocks.Finite :=
  Φ.freeClocks_finite.union Φ.boundClocks_finite

def Equivalent (Φ Ψ : TransitionForm Clock Var) : Prop :=
  ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : Judgement.Position P),
    Φ.Satisfies σ P α k ↔ Ψ.Satisfies σ P α k

/-- Rename the outer reset scope, including the next state inside that scope.
Current guards remain outside the reset. -/
def alphaOuter (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var) :
    TransitionForm Clock Var :=
  ⟨Φ.current.alphaReset e, Φ.nextPart.map (StateForm.rename e)⟩

theorem alphaOuter_equivalent (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks, e c = c) : (Φ.alphaOuter e).Equivalent Φ := by
  intro σ P α k
  have hagree := Φ.current.resets.apply_pullback_agree e
    ((⋃ Ψ ∈ Φ.current.locals, Ψ.freeClocks) ∪
      match Φ.nextPart with | none => ∅ | some N => N.freeClocks) hfix α
  simp only [alphaOuter, Satisfies, StateForm.alphaReset, StateForm.rename,
    Set.forall_mem_image, Judgement.satisfies_rename, ClockResetSet.apply_rename]
  apply and_congr Iff.rfl
  apply and_congr
  · apply forall_congr'
    intro Ψ
    apply forall_congr'
    intro hΨ
    exact Judgement.satisfies_congr_of_agree
      (fun c hc => hagree c (Or.inl (Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hΨ, hc⟩⟩))) σ P k
  · cases hN : Φ.nextPart with
    | none => rfl
    | some N =>
        simp only [Option.map_some]
        split
        · rw [StateForm.satisfies_rename]
          have hcomp : ClockResetSet.elapse ((Φ.current.resets.rename e).apply α)
              (Judgement.duration P ⟨k.1, ‹_›⟩) ∘ e =
              ClockResetSet.elapse (Φ.current.resets.apply (α ∘ e))
                (Judgement.duration P ⟨k.1, ‹_›⟩) := by
            funext c
            have he := congrFun (Φ.current.resets.apply_rename e α) c
            exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
          rw [hcomp]
          apply StateForm.satisfies_congr_of_agree N ?_ σ P _
          intro c hc
          have he := hagree c (Or.inr (by simpa [hN] using hc))
          exact congrArg (fun x => x + Judgement.duration P ⟨k.1, ‹_›⟩) he
        · rfl

theorem alphaOuter_bodyFreeClocks (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var) :
    (Φ.alphaOuter e).bodyFreeClocks = e '' Φ.bodyFreeClocks := by
  cases hn : Φ.nextPart <;>
    simp only [alphaOuter, bodyFreeClocks, hn, Option.map_some, Option.map_none,
      StateForm.freeClocks_rename] <;>
    ext c <;>
    simp [StateForm.alphaReset, StateForm.rename, Set.mem_image, Set.mem_iUnion]

theorem alphaOuter_freeClocks (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ c ∈ Φ.bodyFreeClocks, e c = c) :
    (Φ.alphaOuter e).freeClocks = Φ.freeClocks := by
  have he : e '' Φ.bodyFreeClocks = Φ.bodyFreeClocks := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hfix x hx] using hx
    · intro hc
      exact ⟨c, hc, hfix c hc⟩
  change (ClockConstraint.clock '' Φ.current.constraints) ∪
    (Φ.alphaOuter e).bodyFreeClocks = _
  rw [alphaOuter_bodyFreeClocks, he]
  rfl

/-- Rename only the optional next state's own reset scope. -/
def alphaNext (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var) :
    TransitionForm Clock Var :=
  { Φ with nextPart := Φ.nextPart.map (StateForm.alphaReset e) }

theorem alphaNext_equivalent (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    (Φ.alphaNext e).Equivalent Φ := by
  intro σ P α k
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, Satisfies, hn]
  | some N =>
      simp [alphaNext, Satisfies, hn, N.alphaReset_satisfies e (hfix N hn)]

theorem alphaNext_freeClocks (e : Equiv.Perm Clock) (Φ : TransitionForm Clock Var)
    (hfix : ∀ N, Φ.nextPart = some N →
      ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
    (Φ.alphaNext e).freeClocks = Φ.freeClocks := by
  cases hn : Φ.nextPart with
  | none => simp [alphaNext, freeClocks, bodyFreeClocks, hn]
  | some N =>
      simp [alphaNext, freeClocks, bodyFreeClocks, hn, N.alphaReset_freeClocks e (hfix N hn)]

/-- Syntactic alpha-equivalence generated by capture-free renaming of the two
reset scopes. Semantic equivalence alone is not a constructor of this relation. -/
inductive AlphaEquivalent : TransitionForm Clock Var → TransitionForm Clock Var → Prop
  | refl (Φ) : AlphaEquivalent Φ Φ
  | outer (Φ) (e : Equiv.Perm Clock) (hfix : ∀ c ∈ Φ.bodyFreeClocks, e c = c) :
      AlphaEquivalent (Φ.alphaOuter e) Φ
  | next (Φ) (e : Equiv.Perm Clock)
      (hfix : ∀ N, Φ.nextPart = some N →
        ∀ c ∈ N.localClocks \ N.resets.clocks, e c = c) :
      AlphaEquivalent (Φ.alphaNext e) Φ
  | symm {Φ Ψ} : AlphaEquivalent Φ Ψ → AlphaEquivalent Ψ Φ
  | trans {Φ Ψ Χ} : AlphaEquivalent Φ Ψ → AlphaEquivalent Ψ Χ → AlphaEquivalent Φ Χ

theorem AlphaEquivalent.equivalent {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) : Φ.Equivalent Ψ := by
  induction h with
  | refl => exact fun _ _ _ _ => Iff.rfl
  | outer Φ e hf => exact Φ.alphaOuter_equivalent e hf
  | next Φ e hf => exact Φ.alphaNext_equivalent e hf
  | symm h ih => exact fun σ P α k => (ih σ P α k).symm
  | trans h₁ h₂ ih₁ ih₂ => exact fun σ P α k => (ih₁ σ P α k).trans (ih₂ σ P α k)

theorem AlphaEquivalent.freeClocks {Φ Ψ : TransitionForm Clock Var}
    (h : Φ.AlphaEquivalent Ψ) : Φ.freeClocks = Ψ.freeClocks := by
  induction h with
  | refl => rfl
  | outer Φ e hf => exact Φ.alphaOuter_freeClocks e hf
  | next Φ e hf => exact Φ.alphaNext_freeClocks e hf
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Fresh representatives carry a syntactic alpha-conversion derivation. -/
theorem exists_fresh_alpha [Infinite Clock] (Φ : TransitionForm Clock Var)
    (U : Set Clock) (hU : U.Finite) :
    ∃ Φa : TransitionForm Clock Var,
      Φa.AlphaEquivalent Φ ∧ Disjoint Φa.boundClocks U := by
  obtain ⟨e, he, hdis⟩ := exists_fresh_clock_permutation Φ.current.resets.clocks
    Φ.bodyFreeClocks U Φ.current.resets.finite_domain Φ.bodyFreeClocks_finite hU
    (by exact Set.disjoint_left.2 (fun c hc hf => hf.2 hc))
  let F := Φ.alphaOuter e
  have hF : F.AlphaEquivalent Φ := .outer Φ e he
  have hcur : Disjoint F.current.resets.clocks U := by
    simpa [F, alphaOuter, StateForm.alphaReset, StateForm.rename] using hdis
  cases hn : F.nextPart with
  | none =>
      exact ⟨F, hF, by simpa [boundClocks, hn] using hcur⟩
  | some N =>
      obtain ⟨d, hd, hdU⟩ := exists_fresh_clock_permutation N.resets.clocks
        (N.localClocks \ N.resets.clocks) U N.resets.finite_domain
        N.localClocks_finite.sdiff hU
        (by exact Set.disjoint_left.2 (fun c hc hf => hf.2 hc))
      have hfix : ∀ M, F.nextPart = some M →
          ∀ c ∈ M.localClocks \ M.resets.clocks, d c = c := by
        intro M hm
        have heq : M = N := Option.some.inj (hm.symm.trans hn)
        subst M
        exact hd
      refine ⟨F.alphaNext d, (AlphaEquivalent.next F d hfix).trans hF, ?_⟩
      · simpa [alphaNext, boundClocks, hn, StateForm.alphaReset, StateForm.rename]
          using hcur.union_left hdU

/-- Both binder levels can be made fresh for an arbitrary finite context.
Free clocks and the meaning at every valuation/position are preserved. -/
theorem exists_fresh [Infinite Clock] (Φ : TransitionForm Clock Var)
    (U : Set Clock) (hU : U.Finite) :
    ∃ Φa : TransitionForm Clock Var,
      Φa.Equivalent Φ ∧ Φa.freeClocks = Φ.freeClocks ∧ Disjoint Φa.boundClocks U := by
  obtain ⟨Φa, ha, hf⟩ := Φ.exists_fresh_alpha U hU
  exact ⟨Φa, ha.equivalent, ha.freeClocks, hf⟩

theorem nextResets_subset_bound {Φ : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hn : Φ.nextPart = some N) : N.resets.clocks ⊆ Φ.boundClocks := by
  intro c hc
  exact Or.inr (by simpa [hn] using hc)

theorem nextLocalClocks_subset_all {Φ : TransitionForm Clock Var} {N : StateForm Clock Var}
    (hn : Φ.nextPart = some N) : N.localClocks ⊆ Φ.allClocks := by
  intro c hc
  by_cases hcur : c ∈ Φ.current.resets.clocks
  · exact Or.inr (Or.inl hcur)
  by_cases hnext : c ∈ N.resets.clocks
  · exact Or.inr (nextResets_subset_bound hn hnext)
  apply Or.inl
  apply Or.inr
  refine ⟨Or.inr ?_, hcur⟩
  rw [hn]
  apply Or.inr
  obtain ⟨Ψ, hΨ⟩ := Set.mem_iUnion.1 hc
  obtain ⟨hm, hf⟩ := Set.mem_iUnion.1 hΨ
  exact Set.mem_iUnion.2 ⟨Ψ, Set.mem_iUnion.2 ⟨hm, hf, hnext⟩⟩

theorem subsumed_union_left_of_boundFresh (Φ Ψ : TransitionForm Clock Var)
    (hfresh : Disjoint Ψ.boundClocks Φ.allClocks) : Φ ⊑ Φ.union Ψ := by
  apply Φ.subsumed_union_left Ψ
  · apply Set.disjoint_left.2
    intro c hc hf
    have hother : c ∈ Ψ.current.resets.clocks := by
      have hu : c ∈ Φ.current.resets.clocks ∪ Ψ.current.resets.clocks := by
        simpa only [union, StateForm.union, ClockResetSet.clocks_union] using hc.1
      exact hu.resolve_left hc.2
    exact Set.disjoint_left.1 hfresh (Or.inl hother) (Or.inl (Or.inr hf))
  · intro N M hn hm
    cases hj : Ψ.nextPart with
    | none =>
        have heq : N = M := by simpa [union, unionNext, hn, hj] using hm
        subst M
        simp
    | some K =>
        have heq : N.union K = M := by simpa [union, unionNext, hn, hj] using hm
        subst M
        apply Set.disjoint_left.2
        intro c hc hf
        have hother : c ∈ K.resets.clocks := by
          have hu : c ∈ N.resets.clocks ∪ K.resets.clocks := by
            simpa only [StateForm.union, ClockResetSet.clocks_union] using hc.1
          exact hu.resolve_left hc.2
        have hl : c ∈ N.localClocks := by
          obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hf
          obtain ⟨hmem, hfree⟩ := Set.mem_iUnion.1 hl
          exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨hmem, hfree.1⟩⟩
        exact Set.disjoint_left.1 hfresh (nextResets_subset_bound hj hother)
          (nextLocalClocks_subset_all hn hl)

/-- Disjoint bound names supply all four compatibility fields, rather than
assuming subsumption as part of the normalization input. -/
theorem unionCompatible_of_boundFresh (Φ Ψ : TransitionForm Clock Var)
    (hleft : Disjoint Φ.boundClocks Ψ.allClocks)
    (hright : Disjoint Ψ.boundClocks Φ.allClocks) : Φ.UnionCompatible Ψ := by
  have hcur : Φ.current.resets.Consistent Ψ.current.resets :=
    ClockResetSet.consistent_of_disjoint
      (hleft.mono (fun _ h => Or.inl h) (fun _ h => Or.inr (Or.inl h)))
  have hnext : ∀ N K, Φ.nextPart = some N → Ψ.nextPart = some K →
      N.resets.Consistent K.resets := by
    intro N K hn hk
    exact ClockResetSet.consistent_of_disjoint
      (hleft.mono (nextResets_subset_bound hn)
        (fun _ h => Or.inr (nextResets_subset_bound hk h)))
  refine ⟨Φ.subsumed_union_left_of_boundFresh Ψ hright, ?_, hcur, hnext⟩
  apply Φ.subsumed_union_right Ψ hcur hnext
  · apply Set.disjoint_left.2
    intro c hc hf
    have hother : c ∈ Φ.current.resets.clocks := by
      have hu : c ∈ Φ.current.resets.clocks ∪ Ψ.current.resets.clocks := by
        simpa only [union, StateForm.union, ClockResetSet.clocks_union] using hc.1
      exact hu.resolve_right hc.2
    exact Set.disjoint_left.1 hleft (Or.inl hother) (Or.inl (Or.inr hf))
  · intro K M hk hm
    cases hn : Φ.nextPart with
    | none =>
        have heq : K = M := by simpa [union, unionNext, hn, hk] using hm
        subst M
        simp
    | some N =>
        have heq : N.union K = M := by simpa [union, unionNext, hn, hk] using hm
        subst M
        apply Set.disjoint_left.2
        intro c hc hf
        have hother : c ∈ N.resets.clocks := by
          have hu : c ∈ N.resets.clocks ∪ K.resets.clocks := by
            simpa only [StateForm.union, ClockResetSet.clocks_union] using hc.1
          exact hu.resolve_right hc.2
        have hl : c ∈ K.localClocks := by
          obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hf
          obtain ⟨hmem, hfree⟩ := Set.mem_iUnion.1 hl
          exact Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨hmem, hfree.1⟩⟩
        exact Set.disjoint_left.1 hleft (nextResets_subset_bound hn hother)
          (nextLocalClocks_subset_all hk hl)

/-- Every pair of transition forms has compatible alpha-converted
representatives, given an infinite clock supply. -/
theorem exists_alpha_compatible_representatives [Infinite Clock] (Φ Ψ : TransitionForm Clock Var) :
    ∃ Φa Ψa : TransitionForm Clock Var,
      Φa.AlphaEquivalent Φ ∧ Ψa.AlphaEquivalent Ψ ∧ Φa.UnionCompatible Ψa := by
  obtain ⟨Φa, hΦ, hΦfresh⟩ := Φ.exists_fresh_alpha Ψ.freeClocks Ψ.freeClocks_finite
  obtain ⟨Ψa, hΨ, hΨfresh⟩ := Ψ.exists_fresh_alpha Φa.allClocks Φa.allClocks_finite
  refine ⟨Φa, Ψa, hΦ, hΨ, Φa.unionCompatible_of_boundFresh Ψa ?_ hΨfresh⟩
  apply Set.disjoint_left.2
  intro c hc hd
  rcases hd with hf | hb
  · exact Set.disjoint_left.1 hΦfresh hc (hΨ.freeClocks ▸ hf)
  · exact Set.disjoint_left.1 hΨfresh hb (Or.inr hc)

theorem exists_compatible_representatives [Infinite Clock] (Φ Ψ : TransitionForm Clock Var) :
    ∃ Φa Ψa : TransitionForm Clock Var,
      Φa.Equivalent Φ ∧ Ψa.Equivalent Ψ ∧ Φa.UnionCompatible Ψa := by
  obtain ⟨Φa, Ψa, hΦ, hΨ, hc⟩ := exists_alpha_compatible_representatives Φ Ψ
  exact ⟨Φa, Ψa, hΦ.equivalent, hΨ.equivalent, hc⟩

/-- Unconditional semantic normalization of conjunction, up to alpha-conversion.
Literal subsumption is stated for the selected representatives. -/
theorem normalization_exists_up_to_alpha [Infinite Clock] (Φ Ψ : TransitionForm Clock Var) :
    ∃ Φa Ψa Φhat : TransitionForm Clock Var,
      Φa.Equivalent Φ ∧ Ψa.Equivalent Ψ ∧ Φa.UnionCompatible Ψa ∧
      Φhat = Φa.union Ψa ∧ (Φa ⊑ Φhat) ∧ (Ψa ⊑ Φhat) ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : Judgement.Position P),
        Φhat.Satisfies σ P α k ↔ Φ.Satisfies σ P α k ∧ Ψ.Satisfies σ P α k := by
  obtain ⟨Φa, Ψa, hΦ, hΨ, hc⟩ := exists_compatible_representatives Φ Ψ
  refine ⟨Φa, Ψa, Φa.union Ψa, hΦ, hΨ, hc, rfl, hc.leftSubsumed, hc.rightSubsumed, ?_⟩
  intro σ P α k
  exact (Φa.satisfies_union_iff Ψa hc.leftSubsumed hc.rightSubsumed
    hc.currentConsistent hc.nextConsistent σ P α k).trans
    (and_congr (hΦ σ P α k) (hΨ σ P α k))

end TransitionForm

namespace ConcreteRule
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]

/-- Every actual rule branch can be inserted into an arbitrary enclosing form.
The reset/freshness compatibility is constructed, not supplied by the caller. -/
theorem branch_normalization_exists_up_to_alpha
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hrule : ConcreteRule p R) {Ψ : Judgement Clock Var} (hΨ : Ψ ∈ R.branches)
    (Φ : TransitionForm Clock Var) :
    ∃ Φa B Φhat : TransitionForm Clock Var,
      Φa.Equivalent Φ ∧ Φa.UnionCompatible B ∧
      Φhat = Φa.union B ∧ (Φa ⊑ Φhat) ∧ (B ⊑ Φhat) ∧
      ∀ (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
        (α : ClockValuation Clock) (k : Judgement.Position P),
        Φhat.Satisfies σ P α k ↔ Φ.Satisfies σ P α k ∧
          Judgement.Satisfies σ P (Φ.current.resets.apply α) k Ψ := by
  obtain ⟨Φa, B, Φhat, hΦ, hB, hc, heq, hsubΦ, hsubB, heval⟩ :=
    Φ.normalization_exists_up_to_alpha (hrule.branchTransitionForm hΨ Φ.current.resets)
  refine ⟨Φa, B, Φhat, hΦ, hc, heq, hsubΦ, hsubB, ?_⟩
  intro σ P α k
  exact (heval σ P α k).trans (and_congr Iff.rfl
    ((hrule.branchTransitionForm_represents hΨ Φ.current.resets).evaluation σ P α k).1)

end ConcreteRule
end STLTableau
