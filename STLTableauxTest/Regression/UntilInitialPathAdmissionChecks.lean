/- A goal-reaching execution of the auxiliary derivation tableau has
residence times `[0, 0, 1]`. No partition has one piece for each of
the first two zero-duration visits. The projected constant signal is
recognized, and the middle mode can be chosen as the initial state.

The middle state is a completed derivation rather than an original minimal
closure. A second example uses a nonconstant signal whose one-piece flow
partition fails recognition and whose refinement at zero is recognized. -/

import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Automata.Translation.RootAutomata
import STLTableaux.Automata.Recognition.TableauDiscreteCorrespondence
import STLTableaux.Automata.Recognition.ExecutionPathTiming
import STLTableaux.Syntax.InputSyntax
import STLTableaux.Automata.Execution.TerminalPruning
import STLTableaux.Automata.Recognition.ExecutionFlowPartition
import STLTableaux.Semantics.Partitions.PartitionDurationAlignment
import STLTableaux.Automata.Translation.NormalizedInputTranslation
import STLTableaux.Finiteness.Correctness.RootIntervalNecessity
import STLTableaux.Automata.Recognition.ExecutionInducedPartitionReview
import STLTableaux.Automata.Translation.InitialRootReturn

namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*} [DecidableEq Clock]

private abbrev P (φ : Formula Var) : MixedJ Clock Var := .predicate (.plain φ)

def auditUntilDefer (φ ψ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic) :
    Resolve (Clock := Clock) (P (Formula.untimedUntil φ ψ))
      (.conj (P (Formula.untimedUntil φ ψ))
        (.conj (P φ) (.next (P (Formula.untimedUntil φ ψ)))))
      (.conj (P φ) (.next (P (Formula.untimedUntil φ ψ)))) := by
  refine .expandSolo (.finite (.plainUntil φ ψ)
    (B := .conj (.predicate (.plain φ))
      (.next (.predicate (.plain (Formula.untimedUntil φ ψ))))) ?_) ?_ ?_
    (.conj (.leaf (.atomic _ hφ)) (.leaf (.next _)))
  · simp [ExpansionRule.plainUntil]
  · simp [Predicate.IsAtomic, Formula.untimedUntil]
  · simp [FreshWithoutContext, resetNames, Judgement.ofFinite]

def auditUntilNow (φ ψ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic) :
    Resolve (Clock := Clock) (P (Formula.untimedUntil φ ψ))
      (.conj (P (Formula.untimedUntil φ ψ)) (.conj (P φ) (P ψ)))
      (.conj (P φ) (P ψ)) := by
  refine .expandSolo (.finite (.plainUntil φ ψ)
    (B := .conj (.predicate (.plain φ)) (.predicate (.plain ψ))) ?_) ?_ ?_
    (.conj (.leaf (.atomic _ hφ)) (.leaf (.atomic _ hψ)))
  · simp [ExpansionRule.plainUntil]
  · simp [Predicate.IsAtomic, Formula.untimedUntil]
  · simp [FreshWithoutContext, resetNames, Judgement.ofFinite]

def auditNestedUntil (φ ψ χ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic) :
    Resolve (Clock := Clock) (P (Formula.untimedUntil φ (Formula.untimedUntil ψ χ)))
      (.conj (P (Formula.untimedUntil φ (Formula.untimedUntil ψ χ)))
        (.conj (P φ) (.conj (P (Formula.untimedUntil ψ χ))
          (.conj (P ψ) (.next (P (Formula.untimedUntil ψ χ)))))))
      (.conj (P φ) (.conj (P ψ) (.next (P (Formula.untimedUntil ψ χ))))) := by
  refine .expandSolo (.finite (.plainUntil φ (Formula.untimedUntil ψ χ))
    (B := .conj (.predicate (.plain φ)) (.predicate (.plain (Formula.untimedUntil ψ χ)))) ?_) ?_ ?_
    (.conj (.leaf (.atomic _ hφ)) (auditUntilDefer ψ χ hψ))
  · simp [ExpansionRule.plainUntil]
  · simp [Predicate.IsAtomic, Formula.untimedUntil]
  · simp [FreshWithoutContext, resetNames, Judgement.ofFinite]

namespace UntilAdmissionAudit

abbrev plain (φ : Formula Var) : Section3.TransitionForm Clock Var :=
  .ofState (.ofLocal (.predicate (.plain φ)))
abbrev deferred (φ ψ : Formula Var) : Section3.TransitionForm Clock Var :=
  (plain (φ.untimedUntil ψ)).union ((plain φ).union
    (.ofNextState (.ofLocal (.predicate (.plain (φ.untimedUntil ψ))))))
abbrev immediate (φ ψ : Formula Var) : Section3.TransitionForm Clock Var :=
  (plain (φ.untimedUntil ψ)).union ((plain φ).union (plain ψ))
abbrev nested (φ ψ χ : Formula Var) : Section3.TransitionForm Clock Var :=
  (plain (φ.untimedUntil (ψ.untimedUntil χ))).union
    ((plain φ).union (deferred ψ χ))

omit [DecidableEq Clock] in
private theorem safeConj {J K : MixedJ Clock Var} {F G : Section3.TransitionForm Clock Var}
    (hF : SafeNormalization J F) (hG : SafeNormalization K G)
    (bF : F.boundClocks = ∅) (bG : G.boundClocks = ∅) :
    SafeNormalization (.conj J K) (F.union G) := by
  apply SafeNormalization.conj hF hG
  apply Section3.TransitionForm.unionCompatible_of_boundFresh <;> simp [bF,bG]

omit [DecidableEq Clock] in
private theorem bound_plain (φ : Formula Var) : (plain (Clock := Clock) φ).boundClocks = ∅ := by
  ext c
  change (c ∈ ClockResetSet.empty.clocks ∪ ∅) ↔ False
  change ((∃ a : NNReal, (none : Option NNReal) = some a) ∨ False) ↔ False
  constructor
  · rintro (⟨a,h⟩ | h)
    · cases h
    · exact h
  · exact False.elim

omit [DecidableEq Clock] in
private theorem bound_next (φ : Formula Var) :
    (Section3.TransitionForm.ofNextState (Section3.StateForm.ofLocal (.predicate (.plain φ))) :
      Section3.TransitionForm Clock Var).boundClocks = ∅ := by
  ext c
  change (c ∈ ClockResetSet.empty.clocks ∪ ClockResetSet.empty.clocks) ↔ False
  change ((∃ a : NNReal, (none : Option NNReal) = some a) ∨
    (∃ a : NNReal, (none : Option NNReal) = some a)) ↔ False
  constructor
  · rintro (⟨a,h⟩ | ⟨a,h⟩) <;> cases h
  · exact False.elim

omit [DecidableEq Clock] in
private theorem bound_union (F G : Section3.TransitionForm Clock Var)
    (hF : F.boundClocks = ∅) (hG : G.boundClocks = ∅) :
    (F.union G).boundClocks = ∅ := by
  unfold Section3.TransitionForm.boundClocks at *
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    simp [Section3.TransitionForm.union, Section3.TransitionForm.unionNext,
      hf, hg, Section3.StateForm.union, ClockResetSet.clocks_union] at * <;>
    aesop

omit [DecidableEq Clock] in
private theorem safeDefer (φ ψ : Formula Var) :
    SafeNormalization (Clock := Clock) (.conj (P φ) (.next (P (φ.untimedUntil ψ))))
      ((plain φ).union (.ofNextState (.ofLocal (.predicate (.plain (φ.untimedUntil ψ)))))) :=
  safeConj (.predicate _) (.next (.predicate _) rfl) (bound_plain _) (bound_next _)

omit [DecidableEq Clock] in
private theorem bound_defer (φ ψ : Formula Var) :
    (deferred (Clock := Clock) φ ψ).boundClocks = ∅ :=
  bound_union _ _ (bound_plain _) (bound_union _ _ (bound_plain _) (bound_next _))

omit [DecidableEq Clock] in
theorem full_deferred (φ ψ : Formula Var) :
    SafeNormalization
      (.conj (P (φ.untimedUntil ψ)) (.conj (P φ) (.next (P (φ.untimedUntil ψ)))))
      (deferred (Clock := Clock) φ ψ) :=
  safeConj (.predicate _) (safeDefer φ ψ) (bound_plain _)
    (bound_union _ _ (bound_plain _) (bound_next _))

omit [DecidableEq Clock] in
theorem full_immediate (φ ψ : Formula Var) :
    SafeNormalization (.conj (P (φ.untimedUntil ψ)) (.conj (P φ) (P ψ)))
      (immediate (Clock := Clock) φ ψ) :=
  safeConj (.predicate _) (safeConj (.predicate _) (.predicate _) (bound_plain _) (bound_plain _))
    (bound_plain _) (bound_union _ _ (bound_plain _) (bound_plain _))

omit [DecidableEq Clock] in
theorem full_nested (φ ψ χ : Formula Var) :
    SafeNormalization
      (.conj (P (φ.untimedUntil (ψ.untimedUntil χ)))
        (.conj (P φ) (.conj (P (ψ.untimedUntil χ))
          (.conj (P ψ) (.next (P (ψ.untimedUntil χ)))))))
      (nested (Clock := Clock) φ ψ χ) :=
  safeConj (.predicate _)
    (safeConj (.predicate _) (full_deferred ψ χ) (bound_plain _) (bound_defer _ _))
    (bound_plain _) (bound_union _ _ (bound_plain _) (bound_defer _ _))

private theorem erasedFrom {J H A : MixedJ Clock Var} {F G : Section3.TransitionForm Clock Var}
    (D : Resolve J H A) (hF : SafeNormalization H F) (hG : SafeNormalization A G) :
    SafeNormalization A F.atomicProjection := by
  have he : some G = some F.atomicProjection := by
    rw [← hG.normalizes, D.normalize_erased_eq_projection, hF.normalizes]
    rfl
  exact Option.some.inj he ▸ hG

theorem derives_deferred (φ ψ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic) :
    Derives (.ofLocal (.predicate (.plain (φ.untimedUntil ψ)))) (deferred (Clock := Clock) φ ψ) :=
  .resolved (auditUntilDefer φ ψ hφ) (.predicate _) (full_deferred φ ψ)
    (erasedFrom (auditUntilDefer φ ψ hφ) (full_deferred φ ψ) (safeDefer φ ψ))

theorem derives_immediate (φ ψ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic) :
    Derives (.ofLocal (.predicate (.plain (φ.untimedUntil ψ)))) (immediate (Clock := Clock) φ ψ) :=
  .resolved (auditUntilNow φ ψ hφ hψ) (.predicate _) (full_immediate φ ψ)
    (erasedFrom (auditUntilNow φ ψ hφ hψ) (full_immediate φ ψ)
      (safeConj (.predicate _) (.predicate _) (bound_plain _) (bound_plain _)))

theorem derives_nested (φ ψ χ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic) :
    Derives (.ofLocal (.predicate (.plain (φ.untimedUntil (ψ.untimedUntil χ)))))
      (nested (Clock := Clock) φ ψ χ) :=
  .resolved (auditNestedUntil φ ψ χ hφ hψ) (.predicate _) (full_nested φ ψ χ)
    (erasedFrom (auditNestedUntil φ ψ χ hφ hψ) (full_nested φ ψ χ)
      (safeConj (.predicate _) (safeDefer ψ χ) (bound_plain _)
        (bound_union _ _ (bound_plain _) (bound_next _))))

omit [DecidableEq Clock] in
theorem next_deferred (φ ψ : Formula Var) :
    (deferred (Clock := Clock) φ ψ).nextPart =
      some (.ofLocal (.predicate (.plain (φ.untimedUntil ψ)))) := rfl
omit [DecidableEq Clock] in
theorem next_immediate (φ ψ : Formula Var) :
    (immediate (Clock := Clock) φ ψ).nextPart = none := rfl
omit [DecidableEq Clock] in
theorem next_nested (φ ψ χ : Formula Var) :
    (nested (Clock := Clock) φ ψ χ).nextPart =
      some (.ofLocal (.predicate (.plain (ψ.untimedUntil χ)))) := rfl

variable [Infinite Clock]

theorem within_three (X : Set Var) (φ ψ χ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic)
    (hχ : (Predicate.plain χ : Predicate Clock Var).IsAtomic) :
    deferred (Clock := Clock) φ (ψ.untimedUntil χ) ∈
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))).states ∧
    nested (Clock := Clock) φ ψ χ ∈
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))).states ∧
    immediate (Clock := Clock) ψ χ ∈
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))).states := by
  classical
  have hm (θ : Formula Var)
      (hθ : θ ∈ Finiteness.rootPlainFormulas (φ.untimedUntil (ψ.untimedUntil χ))) :
      Local.predicate (.plain θ) ∈ FiniteInventory.locals
        (Finiteness.rootPlainFormulas (φ.untimedUntil (ψ.untimedUntil χ)))
        (rootSlotTriples (Clock := Clock) (φ.untimedUntil (ψ.untimedUntil χ))) := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨θ, hθ, rfl⟩
  have hA := hm (φ.untimedUntil (ψ.untimedUntil χ)) (by
    exact Finiteness.root_mem_rootPlainFormulas _)
  have hB := hm (ψ.untimedUntil χ) (by
    simp [Finiteness.rootPlainFormulas, Formula.untimedUntil])
  have hp := hm φ (by simp [Finiteness.rootPlainFormulas, Formula.untimedUntil,
    Finiteness.root_mem_rootPlainFormulas])
  have hq := hm ψ (by simp [Finiteness.rootPlainFormulas, Formula.untimedUntil,
    Finiteness.root_mem_rootPlainFormulas])
  have hr := hm χ (by simp [Finiteness.rootPlainFormulas, Formula.untimedUntil,
    Finiteness.root_mem_rootPlainFormulas])
  refine ⟨⟨⟨_, derives_deferred φ (ψ.untimedUntil χ) hφ⟩, ?_⟩,
    ⟨⟨_, derives_nested φ ψ χ hφ hψ⟩, ?_⟩,
    ⟨⟨_, derives_immediate ψ χ hψ hχ⟩, ?_⟩⟩ <;>
    simp [FiniteInventory.TransitionWithin, FiniteInventory.Within,
      deferred, nested, immediate, plain, Section3.TransitionForm.union, Section3.TransitionForm.unionNext,
      Section3.TransitionForm.ofState, Section3.TransitionForm.ofNextState, Section3.StateForm.ofLocal,
      Section3.StateForm.empty, Section3.StateForm.union, ClockResetSet.union, ClockResetSet.empty,
      Set.subset_def, hA, hB, hp, hq, hr]
  all_goals first
    | (constructor <;> intro c a he <;> cases he)
    | (intro c a he; cases he)

def threePath (φ ψ χ : Formula Var) : Path Clock (Section3.TransitionForm Clock Var) :=
  .step (JudgementTableau.incoming (deferred φ (ψ.untimedUntil χ)))
    (deferred φ (ψ.untimedUntil χ))
    (.step (JudgementTableau.incoming (nested φ ψ χ)) (nested φ ψ χ)
      (.last (JudgementTableau.incoming (immediate ψ χ)) (immediate ψ χ)))

theorem threePath_accepting_run (X : Set Var) (φ ψ χ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic)
    (hχ : (Predicate.plain χ : Predicate Clock Var).IsAtomic) :
    (threePath (Clock := Clock) φ ψ χ).run
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) ∧
    (threePath (Clock := Clock) φ ψ χ).accepting
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) := by
  obtain ⟨h₀, h₁, h₂⟩ := within_three X φ ψ χ hφ hψ hχ
  have hv : (threePath (Clock := Clock) φ ψ χ).valid
      (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) := by
    refine ⟨h₀, ⟨h₁, h₂, ?_⟩, ?_⟩
    · exact ⟨⟨h₁.1, h₂.1, _, rfl, derives_immediate ψ χ hψ hχ, rfl⟩, h₁, h₂⟩
    · exact ⟨⟨h₀.1, h₁.1, _, rfl, derives_nested φ ψ χ hφ hψ, rfl⟩, h₀, h₁⟩
  exact ⟨⟨hv, ⟨⟨derives_deferred φ (ψ.untimedUntil χ) hφ, rfl⟩, h₀⟩⟩,
    ⟨hv, rfl, h₂⟩⟩

/-- The nested state is already an admissible initial state. The first
deferred state is unnecessary for this accepting path; the remaining edge
is retained literally. -/
def twoPath (φ ψ χ : Formula Var) : Path Clock (Section3.TransitionForm Clock Var) :=
  .step (JudgementTableau.incoming (nested φ ψ χ)) (nested φ ψ χ)
    (.last (JudgementTableau.incoming (immediate ψ χ)) (immediate ψ χ))

theorem twoPath_accepting_run (X : Set Var) (φ ψ χ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic)
    (hχ : (Predicate.plain χ : Predicate Clock Var).IsAtomic) :
    (twoPath (Clock := Clock) φ ψ χ).run
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) ∧
    (twoPath (Clock := Clock) φ ψ χ).accepting
        (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) := by
  obtain ⟨_, h₁, h₂⟩ := within_three X φ ψ χ hφ hψ hχ
  have hv : (twoPath (Clock := Clock) φ ψ χ).valid
      (finiteRootTableau X (φ.untimedUntil (ψ.untimedUntil χ))) := by
    exact ⟨h₁, h₂,
      ⟨⟨h₁.1, h₂.1, _, rfl, derives_immediate ψ χ hψ hχ, rfl⟩, h₁, h₂⟩⟩
  exact ⟨⟨hv, ⟨⟨derives_nested φ ψ χ hφ hψ, rfl⟩, h₁⟩⟩,
    ⟨hv, rfl, h₂⟩⟩

namespace ConcreteExecution
def atom : AtomicProposition Unit := ⟨0, Fin.elim0, fun _ => 0, .ge⟩
def a : Formula Unit := .atom atom
def root : Formula Unit := a.untimedUntil (a.untimedUntil a)
noncomputable def T := finiteRootTableau (Clock := Nat) (Set.univ : Set Unit) root
theorem ready : T.TranslationReady :=
  finiteRootTableau_translationReady _ (Set.toFinite _) root (by simp)
noncomputable def H := T.toAutomaton ready 1 (by norm_num)
abbrev F0 := deferred (Clock := Nat) a (a.untimedUntil a)
abbrev F1 := nested (Clock := Nat) a a a
abbrev F2 := immediate (Clock := Nat) a a
theorem members : F0 ∈ T.states ∧ F1 ∈ T.states ∧ F2 ∈ T.states :=
  within_three _ a a a (by trivial) (by trivial) (by trivial)
def val (t : ℝ) : T.HAVar → ℝ
  | .inl _ => 0
  | .inr _ => t

theorem label_atom (F : Section3.TransitionForm Nat Unit)
    (hF : F = F0 ∨ F = F1 ∨ F = F2) (b : AtomicProposition Unit)
    (hb : Local.predicate (.plain (.atom b)) ∈ T.label F) : b = atom := by
  rcases hF with rfl | rfl | rfl <;>
    simp [T, finiteRootTableau, sparseDerivesTableau, Subgraph.restrict,
      JudgementTableau.tableau, JudgementTableau.labels, F0,F1,F2,
      deferred,nested,immediate,plain,Section3.TransitionForm.union,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty,
      a,Formula.untimedUntil] at hb <;> aesop

theorem invariant (F : Section3.TransitionForm Nat Unit) (hf : F ∈ T.states)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (t : ℝ) (ht : t ≤ 1) :
    (⟨F,hf⟩,val t) ∈ H.invariant := by
  constructor
  · intro b hb
    have hb' := label_atom F he b hb
    subst b
    refine ⟨(by intro i; exact Fin.elim0 i), ?_⟩
    exact le_refl 0
  · intro _
    exact ht

noncomputable def s0 : H.State := ⟨(⟨F0,members.1⟩,val 0), invariant _ _ (Or.inl rfl) _ (by norm_num)⟩
noncomputable def s1 : H.State := ⟨(⟨F1,members.2.1⟩,val 0), invariant _ _ (Or.inr (Or.inl rfl)) _ (by norm_num)⟩
noncomputable def s2 (t : ℝ) (ht : t ≤ 1) : H.State :=
  ⟨(⟨F2,members.2.2⟩,val t), invariant _ _ (Or.inr (Or.inr rfl)) _ ht⟩

theorem incoming_empty (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) :
    (JudgementTableau.incoming F).guards = ∅ ∧
      (JudgementTableau.incoming F).resets = ClockResetSet.empty := by
  rcases he with rfl | rfl | rfl <;>
    simp [JudgementTableau.incoming,F0,F1,F2,deferred,nested,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState,Section3.StateForm.union,
      Section3.StateForm.ofLocal,Section3.StateForm.empty,ClockResetSet.union,
      ClockResetSet.empty]
  all_goals rfl

theorem reset_empty (t : ℝ) : T.reset ClockResetSet.empty (val t) = val t := by
  funext x
  cases x with
  | inl x => rfl
  | inr x => cases x <;> rfl

theorem init : s0.val ∈ H.initial := by
  refine ⟨JudgementTableau.incoming F0, ?_, val 0, ?_, ?_⟩
  · exact ⟨⟨derives_deferred a (a.untimedUntil a) (by trivial), rfl⟩, members.1⟩
  · intro g hg
    rw [(incoming_empty F0 (Or.inl rfl)).1] at hg
    exact False.elim hg
  · rw [(incoming_empty F0 (Or.inl rfl)).2]
    funext x
    cases x with
    | inl x => rfl
    | inr x => cases x <;> rfl

theorem step01 : H.DiscreteStep s0 s1 := by
  apply (T.discreteStep_iff ready 1 (by norm_num)).2
  refine ⟨JudgementTableau.incoming F1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨members.1.1,members.2.1.1,_,rfl,derives_nested a a a (by trivial) (by trivial),rfl⟩,
      members.1,members.2.1⟩
  · intro g hg
    rw [(incoming_empty F1 (Or.inr (Or.inl rfl))).1] at hg
    exact False.elim hg
  · exact ((incoming_empty F1 (Or.inr (Or.inl rfl))).2 ▸ reset_empty 0).symm
  · intro ht
    have : Local.terminal ∈ T.label F1 := ht
    simp [T,finiteRootTableau,sparseDerivesTableau,Subgraph.restrict,
      JudgementTableau.tableau,JudgementTableau.labels,F1,nested,deferred,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty] at this
  · intro _; norm_num [s1,val,Tableau.globalClock]

theorem step12 : H.DiscreteStep s1 (s2 0 (by norm_num)) := by
  apply (T.discreteStep_iff ready 1 (by norm_num)).2
  refine ⟨JudgementTableau.incoming F2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨members.2.1.1,members.2.2.1,_,rfl,derives_immediate a a (by trivial) (by trivial),rfl⟩,
      members.2.1,members.2.2⟩
  · intro g hg
    rw [(incoming_empty F2 (Or.inr (Or.inr rfl))).1] at hg
    exact False.elim hg
  · exact ((incoming_empty F2 (Or.inr (Or.inr rfl))).2 ▸ reset_empty 0).symm
  · intro ht
    have : Local.terminal ∈ T.label F2 := ht
    simp [T,finiteRootTableau,sparseDerivesTableau,Subgraph.restrict,
      JudgementTableau.tableau,JudgementTableau.labels,F2,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.StateForm.union,Section3.StateForm.ofLocal] at this
  · intro _; norm_num [s2,val,Tableau.globalClock]

theorem flow : H.ContinuousStep (s2 0 (by norm_num)) (s2 1 (by norm_num)) 1
    (fun t => val t.val) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro t
  refine ⟨⟨?_,?_⟩, invariant F2 members.2.2 (Or.inr (Or.inr rfl)) _ t.property.2⟩
  · intro c
    change t.val = 0 + t.val
    ring
  · change t.val = 0 + t.val
    ring

def signal : FiniteSignal T.HAVar := ⟨1, by norm_num, fun t => val t.val⟩

noncomputable def execution : H.Execution signal where
  count := 1
  nonempty := by omega
  initialState := s0
  initial_mem := init
  initial_signal_eq := rfl
  start := fun _ => s2 0 (by norm_num)
  finish := fun _ => s2 1 (by norm_num)
  boundary := fun i => if i.val = 0 then 0 else 1
  first_zero := by simp
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 1
  duration_eq := by
    intro i
    fin_cases i
    norm_num
  curve := fun _ t => val t.val
  continuousStep := fun _ => flow
  initialSteps := (Relation.ReflTransGen.single step01).trans
    (Relation.ReflTransGen.single step12)
  discreteSteps := by intro i hi; omega
  finalState := s2 1 (by norm_num)
  finalSteps := .refl
  final_signal_eq := by
    intro t ht
    have hlt := t.property.2
    change t.val < 1 at hlt
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false] at ht
    linarith
  signal_eq := by
    intro i t ht _
    fin_cases i
    change val t.val = val (t.val - (if (0 : ℕ) = 0 then 0 else 1))
    simp

theorem reaches : H.Reaches signal T.goalModes :=
  ⟨execution, rfl, members.2.2⟩

theorem normalized_input : root.NormalizedReady :=
  .until (.atom atom) (.until (.atom atom) (.atom atom))

theorem guards_empty (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (v : T.HAVar → ℝ) :
    T.guardsHold (JudgementTableau.incoming F) v := by
  intro g hg
  rw [(incoming_empty F he).1] at hg
  exact False.elim hg

theorem reset_incoming (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (t : ℝ) :
    T.reset (JudgementTableau.incoming F).resets (val t) = val t := by
  rw [(incoming_empty F he).2]
  exact reset_empty t

theorem timed_path : T.TimedPath (threePath (Clock := Nat) a a a)
    (val 0) (val 1) [0,0,1] := by
  refine .step _ _ (Tableau.ClockElapse.zero T _) (guards_empty F1 (Or.inr (Or.inl rfl)) _) ?_
  change T.TimedPath (twoPath (Clock := Nat) a a a)
    (T.reset (JudgementTableau.incoming F1).resets (val 0)) (val 1) [0,1]
  rw [reset_incoming F1 (Or.inr (Or.inl rfl)) 0]
  refine .step _ _ (Tableau.ClockElapse.zero T _) (guards_empty F2 (Or.inr (Or.inr rfl)) _) ?_
  change T.TimedPath (.last (JudgementTableau.incoming F2) F2)
    (T.reset (JudgementTableau.incoming F2).resets (val 0)) (val 1) [1]
  rw [reset_incoming F2 (Or.inr (Or.inr rfl)) 0]
  exact .last _ _ (T.continuousStep_clockElapse ready 1 (by norm_num) flow)

theorem witnessed_path : T.ExecutionPathWitness ready 1 (by norm_num)
    s0 (s2 1 (by norm_num)) (threePath (Clock := Nat) a a a) := by
  have he01 := (T.discreteStep_iff ready 1 (by norm_num)).1 step01
  have he12 := (T.discreteStep_iff ready 1 (by norm_num)).1 step12
  obtain ⟨l1,edge1,guard1,reset1,_⟩ := he01
  obtain ⟨l2,edge2,guard2,reset2,_⟩ := he12
  have hl1 : l1 = JudgementTableau.incoming F1 := by
    obtain ⟨_,_,N,_,_,hl⟩ := edge1.1
    exact hl
  have hl2 : l2 = JudgementTableau.incoming F2 := by
    obtain ⟨_,_,N,_,_,hl⟩ := edge2.1
    exact hl
  subst l1
  subst l2
  exact .jump _ edge1 guard1 reset1 step01
    (.jump _ edge2 guard2 reset2 step12
      (.flow 1 (fun t => val t.val) flow (.stop _ _)))

theorem F0_ne_F1 : F0 ≠ F1 := by
  intro h
  have hn := congrArg Section3.TransitionForm.nextPart h
  have hs := Option.some.inj hn
  have hl := congrArg Section3.StateForm.locals hs
  have hm : Local.predicate (.plain root) ∈
      (Section3.StateForm.ofLocal (.predicate (.plain root)) : Section3.StateForm Nat Unit).locals := rfl
  unfold root at hm
  rw [hl] at hm
  change Local.predicate (.plain root) = Local.predicate (.plain (a.untimedUntil a)) at hm
  simp [root,a,Formula.untimedUntil] at hm

theorem F1_ne_F2 : F1 ≠ F2 := by
  intro h
  have hn := congrArg Section3.TransitionForm.nextPart h
  cases hn

#print axioms timed_path
#print axioms witnessed_path
#print axioms F0_ne_F1
#print axioms F1_ne_F2

#print axioms execution
#print axioms reaches

end ConcreteExecution
namespace PrunedExecution
abbrev atom := ConcreteExecution.atom
def a : Formula Unit := .atom atom
def root : Formula Unit := a.untimedUntil (a.untimedUntil a)
noncomputable def T := ConcreteExecution.T.pruneTerminal
theorem ready : T.TranslationReady :=
  ConcreteExecution.T.pruneTerminal_translationReady ConcreteExecution.ready
noncomputable def H := T.toAutomaton ready 1 (by norm_num)
abbrev F0 := deferred (Clock := Nat) a (a.untimedUntil a)
abbrev F1 := nested (Clock := Nat) a a a
abbrev F2 := immediate (Clock := Nat) a a
theorem terminal_free (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) : Local.terminal ∉ ConcreteExecution.T.label F := by
  rcases he with rfl | rfl | rfl <;>
    simp [ConcreteExecution.T,finiteRootTableau,sparseDerivesTableau,Subgraph.restrict,
      JudgementTableau.tableau,JudgementTableau.labels,F0,F1,F2,nested,deferred,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty]
theorem compat (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) : ConcreteExecution.T.TerminalCompatible F :=
  fun ht => (terminal_free F he ht).elim
theorem members : F0 ∈ T.states ∧ F1 ∈ T.states ∧ F2 ∈ T.states :=
  ⟨⟨ConcreteExecution.members.1,compat _ (Or.inl rfl)⟩,
   ⟨ConcreteExecution.members.2.1,compat _ (Or.inr (Or.inl rfl))⟩,
   ⟨ConcreteExecution.members.2.2,compat _ (Or.inr (Or.inr rfl))⟩⟩
def val (t : ℝ) : T.HAVar → ℝ
  | .inl _ => 0
  | .inr _ => t

theorem label_atom (F : Section3.TransitionForm Nat Unit)
    (hF : F = F0 ∨ F = F1 ∨ F = F2) (b : AtomicProposition Unit)
    (hb : Local.predicate (.plain (.atom b)) ∈ T.label F) : b = atom := by
  rcases hF with rfl | rfl | rfl <;>
    simp [T,Tableau.pruneTerminal,ConcreteExecution.T, finiteRootTableau, sparseDerivesTableau, Subgraph.restrict,
      JudgementTableau.tableau, JudgementTableau.labels, F0,F1,F2,
      deferred,nested,immediate,plain,Section3.TransitionForm.union,
      Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty,
      a,Formula.untimedUntil] at hb <;> aesop

theorem invariant (F : Section3.TransitionForm Nat Unit) (hf : F ∈ T.states)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (t : ℝ) (ht : t ≤ 1) :
    (⟨F,hf⟩,val t) ∈ H.invariant := by
  constructor
  · intro b hb
    have hb' := label_atom F he b hb
    subst b
    refine ⟨(by intro i; exact Fin.elim0 i), ?_⟩
    exact le_refl 0
  · intro _
    exact ht

noncomputable def s0 : H.State := ⟨(⟨F0,members.1⟩,val 0), invariant _ _ (Or.inl rfl) _ (by norm_num)⟩
noncomputable def s1 : H.State := ⟨(⟨F1,members.2.1⟩,val 0), invariant _ _ (Or.inr (Or.inl rfl)) _ (by norm_num)⟩
noncomputable def s2 (t : ℝ) (ht : t ≤ 1) : H.State :=
  ⟨(⟨F2,members.2.2⟩,val t), invariant _ _ (Or.inr (Or.inr rfl)) _ ht⟩

theorem incoming_empty (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) :
    (JudgementTableau.incoming F).guards = ∅ ∧
      (JudgementTableau.incoming F).resets = ClockResetSet.empty := by
  rcases he with rfl | rfl | rfl <;>
    simp [JudgementTableau.incoming,F0,F1,F2,deferred,nested,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState,Section3.StateForm.union,
      Section3.StateForm.ofLocal,Section3.StateForm.empty,ClockResetSet.union,
      ClockResetSet.empty]
  all_goals rfl

theorem reset_empty (t : ℝ) : T.reset ClockResetSet.empty (val t) = val t := by
  funext x
  cases x with
  | inl x => rfl
  | inr x => cases x <;> rfl

theorem init : s0.val ∈ H.initial := by
  refine ⟨JudgementTableau.incoming F0, ?_, val 0, ?_, ?_⟩
  · exact ⟨⟨⟨derives_deferred a (a.untimedUntil a) (by trivial), rfl⟩, ConcreteExecution.members.1⟩, compat _ (Or.inl rfl)⟩
  · intro g hg
    rw [(incoming_empty F0 (Or.inl rfl)).1] at hg
    exact False.elim hg
  · rw [(incoming_empty F0 (Or.inl rfl)).2]
    funext x
    cases x with
    | inl x => rfl
    | inr x => cases x <;> rfl

theorem step01 : H.DiscreteStep s0 s1 := by
  apply (T.discreteStep_iff ready 1 (by norm_num)).2
  refine ⟨JudgementTableau.incoming F1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨⟨ConcreteExecution.members.1.1,ConcreteExecution.members.2.1.1,_,rfl,derives_nested a a a (by trivial) (by trivial),rfl⟩,ConcreteExecution.members.1,ConcreteExecution.members.2.1⟩, compat _ (Or.inl rfl), compat _ (Or.inr (Or.inl rfl)),terminal_free _ (Or.inl rfl)⟩
  · intro g hg
    rw [(incoming_empty F1 (Or.inr (Or.inl rfl))).1] at hg
    exact False.elim hg
  · exact ((incoming_empty F1 (Or.inr (Or.inl rfl))).2 ▸ reset_empty 0).symm
  · intro ht
    have : Local.terminal ∈ T.label F1 := ht
    simp [T,Tableau.pruneTerminal,ConcreteExecution.T,finiteRootTableau,sparseDerivesTableau,Subgraph.restrict,
      JudgementTableau.tableau,JudgementTableau.labels,F1,nested,deferred,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty] at this
  · intro _; norm_num [s1,val,Tableau.globalClock]

theorem step12 : H.DiscreteStep s1 (s2 0 (by norm_num)) := by
  apply (T.discreteStep_iff ready 1 (by norm_num)).2
  refine ⟨JudgementTableau.incoming F2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨⟨ConcreteExecution.members.2.1.1,ConcreteExecution.members.2.2.1,_,rfl,derives_immediate a a (by trivial) (by trivial),rfl⟩,ConcreteExecution.members.2.1,ConcreteExecution.members.2.2⟩, compat _ (Or.inr (Or.inl rfl)), compat _ (Or.inr (Or.inr rfl)),terminal_free _ (Or.inr (Or.inl rfl))⟩
  · intro g hg
    rw [(incoming_empty F2 (Or.inr (Or.inr rfl))).1] at hg
    exact False.elim hg
  · exact ((incoming_empty F2 (Or.inr (Or.inr rfl))).2 ▸ reset_empty 0).symm
  · intro ht
    have : Local.terminal ∈ T.label F2 := ht
    simp [T,Tableau.pruneTerminal,ConcreteExecution.T,finiteRootTableau,sparseDerivesTableau,Subgraph.restrict,
      JudgementTableau.tableau,JudgementTableau.labels,F2,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,
      Section3.StateForm.union,Section3.StateForm.ofLocal] at this
  · intro _; norm_num [s2,val,Tableau.globalClock]

theorem flow : H.ContinuousStep (s2 0 (by norm_num)) (s2 1 (by norm_num)) 1
    (fun t => val t.val) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro t
  refine ⟨⟨?_,?_⟩, invariant F2 members.2.2 (Or.inr (Or.inr rfl)) _ t.property.2⟩
  · intro c
    change t.val = 0 + t.val
    ring
  · change t.val = 0 + t.val
    ring

def signal : FiniteSignal T.HAVar := ⟨1, by norm_num, fun t => val t.val⟩

noncomputable def execution : H.Execution signal where
  count := 1
  nonempty := by omega
  initialState := s0
  initial_mem := init
  initial_signal_eq := rfl
  start := fun _ => s2 0 (by norm_num)
  finish := fun _ => s2 1 (by norm_num)
  boundary := fun i => if i.val = 0 then 0 else 1
  first_zero := by simp
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 1
  duration_eq := by
    intro i
    fin_cases i
    norm_num
  curve := fun _ t => val t.val
  continuousStep := fun _ => flow
  initialSteps := (Relation.ReflTransGen.single step01).trans
    (Relation.ReflTransGen.single step12)
  discreteSteps := by intro i hi; omega
  finalState := s2 1 (by norm_num)
  finalSteps := .refl
  final_signal_eq := by
    intro t ht
    have hlt := t.property.2
    change t.val < 1 at hlt
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false] at ht
    linarith
  signal_eq := by
    intro i t ht _
    fin_cases i
    change val t.val = val (t.val - (if (0 : ℕ) = 0 then 0 else 1))
    simp

theorem reaches : H.Reaches signal T.goalModes :=
  ⟨execution, ⟨rfl, ConcreteExecution.members.2.2⟩, compat _ (Or.inr (Or.inr rfl))⟩


#print axioms execution
#print axioms reaches
theorem guards_empty (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (v : T.HAVar → ℝ) :
    T.guardsHold (JudgementTableau.incoming F) v := by
  intro g hg
  rw [(incoming_empty F he).1] at hg
  exact False.elim hg

theorem reset_incoming (F : Section3.TransitionForm Nat Unit)
    (he : F = F0 ∨ F = F1 ∨ F = F2) (t : ℝ) :
    T.reset (JudgementTableau.incoming F).resets (val t) = val t := by
  rw [(incoming_empty F he).2]
  exact reset_empty t

theorem timed_path : T.TimedPath (threePath (Clock := Nat) a a a)
    (val 0) (val 1) [0,0,1] := by
  refine .step _ _ (Tableau.ClockElapse.zero T _) (guards_empty F1 (Or.inr (Or.inl rfl)) _) ?_
  change T.TimedPath (twoPath (Clock := Nat) a a a)
    (T.reset (JudgementTableau.incoming F1).resets (val 0)) (val 1) [0,1]
  rw [reset_incoming F1 (Or.inr (Or.inl rfl)) 0]
  refine .step _ _ (Tableau.ClockElapse.zero T _) (guards_empty F2 (Or.inr (Or.inr rfl)) _) ?_
  change T.TimedPath (.last (JudgementTableau.incoming F2) F2)
    (T.reset (JudgementTableau.incoming F2).resets (val 0)) (val 1) [1]
  rw [reset_incoming F2 (Or.inr (Or.inr rfl)) 0]
  exact .last _ _ (T.continuousStep_clockElapse ready 1 (by norm_num) flow)

theorem witnessed_path : T.ExecutionPathWitness ready 1 (by norm_num)
    s0 (s2 1 (by norm_num)) (threePath (Clock := Nat) a a a) := by
  have he01 := (T.discreteStep_iff ready 1 (by norm_num)).1 step01
  have he12 := (T.discreteStep_iff ready 1 (by norm_num)).1 step12
  obtain ⟨l1,edge1,guard1,reset1,_⟩ := he01
  obtain ⟨l2,edge2,guard2,reset2,_⟩ := he12
  have hl1 : l1 = JudgementTableau.incoming F1 := by
    obtain ⟨_,_,N,_,_,hl⟩ := edge1.1.1
    exact hl
  have hl2 : l2 = JudgementTableau.incoming F2 := by
    obtain ⟨_,_,N,_,_,hl⟩ := edge2.1.1
    exact hl
  subst l1
  subst l2
  exact .jump _ edge1 guard1 reset1 step01
    (.jump _ edge2 guard2 reset2 step12
      (.flow 1 (fun t => val t.val) flow (.stop _ _)))


#print axioms timed_path
#print axioms witnessed_path
def rho : FiniteSignal Unit := ⟨1, by norm_num, fun _ _ => 0⟩

theorem projects : T.ProjectsTo signal rho :=
  ⟨rfl, by intro t u ht x; rfl⟩

theorem atom_true (t : rho.Time) : rho.Satisfies a t := le_refl 0

theorem inner_true (t : rho.Time) : rho.Satisfies (a.untimedUntil a) t :=
  FiniteSignal.satisfies_untimedUntil_of_and rho a a t (atom_true t) (atom_true t)

theorem root_true (t : rho.Time) : rho.Satisfies root t :=
  FiniteSignal.satisfies_untimedUntil_of_and rho a (a.untimedUntil a) t
    (atom_true t) (inner_true t)

theorem sub_atom (χ : Formula Unit) (h : χ.IsSubformula a) : χ = a := by
  cases h
  rfl

theorem sub_inner (χ : Formula Unit) (h : χ.IsSubformula (a.untimedUntil a)) :
    χ = a.untimedUntil a ∨ χ = a := by
  cases h with
  | refl => exact Or.inl rfl
  | until_left h => exact Or.inr (sub_atom χ h)
  | until_right h => exact Or.inr (sub_atom χ h)

theorem sub_root (χ : Formula Unit) (h : χ.IsSubformula root) :
    χ = root ∨ χ = a.untimedUntil a ∨ χ = a := by
  cases h with
  | refl => exact Or.inl rfl
  | until_left h => exact Or.inr (Or.inr (sub_atom χ h))
  | until_right h => exact Or.inr (sub_inner χ h)

theorem subformula_true (χ : Formula Unit) (h : χ.IsSubformula root) (t : rho.Time) :
    rho.Satisfies χ t := by
  rcases sub_root χ h with rfl | rfl | rfl
  · exact root_true t
  · exact inner_true t
  · exact atom_true t

theorem stable (P : IntervalPartition rho.domain) : rho.StablePartition root P := by
  intro i χ hχ u v _ _
  exact ⟨fun _ => subformula_true χ hχ v, fun _ => subformula_true χ hχ u⟩

noncomputable def rhoPartition : IntervalPartition rho.domain :=
  execution.fullFlowPartition rfl

theorem finite_variability : rho.HasFiniteVariability root :=
  ⟨rhoPartition, stable rhoPartition⟩

/-- The execution skips its two initial jumps before its single positive flow.
The zero entries belong to the expanded mode path, not two extra flow pieces. -/
theorem one_positive_flow : execution.count = 1 ∧
    ∀ i, execution.duration i = 1 := by
  exact ⟨rfl, fun _ => rfl⟩

/-- The unpruned derivation tableau recognizes the projected signal on the
partition from the positive flow. -/
theorem recognizes_flow_partition :
    ConcreteExecution.T.recognizes JudgementTableau.labels_finite rho rhoPartition := by
  apply (finiteRootTableau_recognizes_iff (Clock := Nat) (Set.univ : Set Unit) root
    ConcreteExecution.normalized_input.mixedReady rho rhoPartition (stable rhoPartition)).2
  exact root_true ⟨0, le_rfl, rho.horizon_pos⟩

/-- The destination of the first zero-time jump is already an admissible
initial state. Its original incoming label and reset witness are retained. -/
theorem middle_initial : s1.val ∈ H.initial := by
  apply T.initial_of_zero_time_jump ready 1 (by norm_num) step01 rfl
  intro l he
  exact ⟨finiteRootTableau_root_return_initial Set.univ root he.1 rfl,
    compat _ (Or.inr (Or.inl rfl))⟩

noncomputable def rebasedExecution : H.Execution signal :=
  execution.rebaseInitialState s1 middle_initial (Relation.ReflTransGen.single step12) rfl

/-- Rechoosing the initial witness changes neither the signal domain, positive
flow data nor the partition induced by the original execution. -/
theorem rebased_review_partition :
    rebasedExecution.reviewInducedPartition = execution.reviewInducedPartition := rfl

theorem rebased_reaches : rebasedExecution.finalState.val.1 ∈ T.goalModes :=
  ⟨⟨rfl, ConcreteExecution.members.2.2⟩, compat _ (Or.inr (Or.inr rfl))⟩

theorem rebased_timed_path : T.TimedPath (twoPath (Clock := Nat) a a a)
    (val 0) (val 1) [0, 1] := by
  refine .step _ _ (Tableau.ClockElapse.zero T _)
    (guards_empty F2 (Or.inr (Or.inr rfl)) _) ?_
  change T.TimedPath (.last (JudgementTableau.incoming F2) F2)
    (T.reset (JudgementTableau.incoming F2).resets (val 0)) (val 1) [1]
  rw [reset_incoming F2 (Or.inr (Or.inr rfl)) 0]
  exact .last _ _ (T.continuousStep_clockElapse ready 1 (by norm_num) flow)

theorem rebased_witnessed_path : T.ExecutionPathWitness ready 1 (by norm_num)
    rebasedExecution.initialState rebasedExecution.finalState
    (twoPath (Clock := Nat) a a a) := by
  obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff ready 1 (by norm_num)).mp step12
  have hl : l = JudgementTableau.incoming F2 := by
    obtain ⟨_, _, N, _, _, hl⟩ := he.1.1
    exact hl
  subst l
  exact .jump _ he hg hr step12 (.flow 1 (fun t => val t.val) flow (.stop _ _))

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``middle_initial, ``rebasedExecution, ``rebased_review_partition,
      ``rebased_reaches, ``rebased_timed_path, ``rebased_witnessed_path] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

#print axioms projects
#print axioms finite_variability

end PrunedExecution

namespace LiteralClosureAudit
open ConcreteExecution

theorem branch_nonatomic {p : Predicate Nat Unit} {R : ClockResetSet Nat}
    {F : Section3.TransitionForm Nat Unit}
    (h : ConcreteContextual.catalogue.Branch p R F) : ¬ p.IsAtomic := by
  obtain ⟨B,A,hb,_,_⟩ := h
  rcases hb with hb | hb
  · obtain ⟨p0,rule,raw,G,rfl,hr,_,_,_⟩ := hb
    cases hr <;> simp [Predicate.ofFinite,Predicate.IsAtomic,Formula.untimedUntil,
      Formula.or,Formula.always,Formula.eventually,Formula.release]
  · rcases hb with hb | hb
    · obtain ⟨p0,bs,raw,G,rfl,hr,_,_,_⟩ := hb
      cases hr <;> simp [Predicate.ofUnbounded,Predicate.IsAtomic]
    · obtain ⟨c,m,k,t,φ,G,rfl,_,_⟩ := hb
      cases k <;> simp [UnboundedClocked.formula,Predicate.IsAtomic,Formula.always,Formula.eventually]

theorem atom_closed (F : Section3.TransitionForm Nat Unit) :
    ConcreteContextual.catalogue.RuleClosedFor F (.plain a) := by
  left
  rintro ⟨B,hB⟩
  exact branch_nonatomic hB (by trivial)

theorem until_now_branch (φ ψ : Formula Unit) (R : ClockResetSet Nat) :
    ConcreteContextual.catalogue.Branch (.plain (φ.untimedUntil ψ)) R
      (((plain φ).union (plain ψ)).underReset R) := by
  refine ⟨((plain φ).union (plain ψ)).underReset ClockResetSet.empty,
    ((plain φ).union (plain ψ)), ?_, ?_, rfl⟩
  · left
    refine ⟨.plain (φ.untimedUntil ψ), ExpansionRule.plainUntil φ ψ,
      .conj (.predicate (.plain φ)) (.predicate (.plain ψ)),
      (plain φ).union (plain ψ), rfl, .plainUntil φ ψ, ?_, ?_, rfl⟩
    · simp [ExpansionRule.plainUntil]
    · rfl
  · have he : (((plain (Clock := Nat) φ).union (plain ψ)).underReset ClockResetSet.empty) =
        ((plain φ).union (plain ψ)) := by
      apply congrArg₂ Section3.TransitionForm.mk
      · apply Section3.StateForm.ext_components <;> try rfl
      · rfl
    rw [he]
    exact .refl _

abbrev G : Section3.TransitionForm Nat Unit :=
  (plain root).union ((plain a).union (plain (a.untimedUntil a)))

theorem now_subsumed (φ ψ : Formula Unit)
    (hφ : Local.predicate (.plain φ) ∈ G.current.locals)
    (hψ : Local.predicate (.plain ψ) ∈ G.current.locals) :
    Section3.SyntacticallySubsumed (((plain φ).union (plain ψ)).underReset G.current.resets) G := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro g hg
    rcases hg with h | h <;> exact False.elim h
  · intro c x hx
    cases hx
  · intro l hl
    rcases hl with hl | hl
    · exact (show l = Local.predicate (.plain φ) from hl) ▸ hφ
    · exact (show l = Local.predicate (.plain ψ) from hl) ▸ hψ
  · apply Set.disjoint_left.2
    rintro c ⟨x,hx⟩ _
    cases hx
  · intro N hn
    cases hn

theorem G_closed : ConcreteContextual.catalogue.IsClosed G := by
  intro p hp
  change Local.predicate p = Local.predicate (.plain root) ∨
    Local.predicate p = Local.predicate (.plain a) ∨
    Local.predicate p = Local.predicate (.plain (a.untimedUntil a)) at hp
  simp only [Local.predicate.injEq] at hp
  rcases hp with rfl | rfl | rfl
  · right
    refine ⟨_, until_now_branch a (a.untimedUntil a) G.current.resets,
      now_subsumed a (a.untimedUntil a) ?_ ?_⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · exact atom_closed G
  · right
    refine ⟨_, until_now_branch a a G.current.resets, now_subsumed a a ?_ ?_⟩ <;>
      exact Or.inr (Or.inl rfl)

#print axioms G_closed

/-- The example's generators each admit an original closure. This is separate
from minimality of the completed output. -/
theorem generator_original_closure_exists (φ : Formula Unit)
    (hφ : Local.predicate (.plain φ) ∈ G.current.locals) :
    ∃ F : Section3.TransitionForm Nat Unit, ConcreteContextual.catalogue.IsClosure
      (.ofState (.ofLocal (.predicate (.plain φ)))) F := by
  apply ConcreteContextual.catalogue.exists_minimal_closed_extension
  refine ⟨G, ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, G_closed⟩
  · intro g hg
    exact False.elim hg
  · intro c a ha
    cases ha
  · intro l hl
    exact (show l = Local.predicate (.plain φ) from hl) ▸ hφ
  · apply Set.disjoint_left.2
    rintro c ⟨a, ha⟩ _
    cases ha
  · intro N hn
    cases hn

theorem root_original_closure_exists :
    ∃ F : Section3.TransitionForm Nat Unit, ConcreteContextual.catalogue.IsClosure
      (.ofState (.ofLocal (.predicate (.plain root)))) F :=
  generator_original_closure_exists root (Or.inl rfl)

theorem inner_original_closure_exists :
    ∃ F : Section3.TransitionForm Nat Unit, ConcreteContextual.catalogue.IsClosure
      (.ofState (.ofLocal (.predicate (.plain (a.untimedUntil a))))) F :=
  generator_original_closure_exists _ (Or.inr (Or.inr rfl))

theorem F1_current_eq_G : Section3.TransitionForm.ofState F1.current = G := by
  apply congrArg₂ Section3.TransitionForm.mk
  · apply Section3.StateForm.ext_components
    · ext x
      simp [F1,nested,deferred,plain,Section3.TransitionForm.union,
        Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
        Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty]
    · rfl
    · ext l
      simp only [F1,nested,deferred,plain,Section3.TransitionForm.union,
        Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
        Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty,
        Set.mem_union,Set.mem_singleton_iff,Set.mem_empty_iff_false]
      aesop
  · rfl

theorem F1_current_closed : ConcreteContextual.catalogue.IsClosed
    (Section3.TransitionForm.ofState F1.current) := by
  rw [F1_current_eq_G]
  exact G_closed

theorem F1_not_literal_closure (N : Section3.StateForm Nat Unit) :
    ¬ ConcreteContextual.catalogue.IsClosure (.ofState N) F1 := by
  intro hc
  have hn := hc.nextPart_eq_none_of_current_closed F1_current_closed
  rw [next_nested a a a] at hn
  cases hn

#print axioms F1_not_literal_closure
theorem derives_but_not_literal_closure :
    Derives (.ofLocal (.predicate (.plain root))) F1 ∧
      ¬ ConcreteContextual.catalogue.IsClosure
        (.ofState (.ofLocal (.predicate (.plain root)))) F1 :=
  ⟨derives_nested a a a (by trivial) (by trivial), F1_not_literal_closure _⟩

theorem F1_not_literal_state (X : Set Unit) (root : Formula Unit) :
    F1 ∉ (finiteLiteralRootTableau X root).states := by
  rintro ⟨⟨N, hN⟩, _⟩
  exact F1_not_literal_closure N hN.1

theorem F1_not_literal_input_state (X : Set Unit) (root : Formula.NormalizedInput Unit) :
    F1 ∉ (literalInputTableau X root).states := F1_not_literal_state X root.val

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``G_closed, ``F1_current_closed,
      ``F1_not_literal_closure, ``derives_but_not_literal_closure,
      ``F1_not_literal_state, ``F1_not_literal_input_state,
      ``root_original_closure_exists, ``inner_original_closure_exists] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

end LiteralClosureAudit

end UntilAdmissionAudit
end STLTableau.Section4.Finiteness


#print axioms STLTableau.Section4.Finiteness.UntilAdmissionAudit.threePath_accepting_run
#print axioms STLTableau.Section4.Finiteness.UntilAdmissionAudit.twoPath_accepting_run

namespace STLTableau.IntervalPartition

theorem no_first_two_zero_durations {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hn : 2 ≤ P.size)
    (h₀ : Judgement.duration P ⟨0, by omega⟩ = 0)
    (h₁ : Judgement.duration P ⟨1, by omega⟩ = 0) : False := by
  have z₀ := congrArg (fun x : NNReal => (x : ℝ)) h₀
  have z₁ := congrArg (fun x : NNReal => (x : ℝ)) h₁
  change (P.interval ⟨0, by omega⟩).right - (P.interval ⟨0, by omega⟩).left = 0 at z₀
  change (P.interval ⟨1, by omega⟩).right - (P.interval ⟨1, by omega⟩).left = 0 at z₁
  exact P.adjacent_not_both_zero_width ⟨0, by omega⟩ (by change 1 < P.size; omega)
    (sub_eq_zero.mp z₀) (sub_eq_zero.mp z₁)

end STLTableau.IntervalPartition

namespace STLTableau.IntervalPartition

theorem zero_zero_one_no_alignment {Var : Type*} (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (hlen : 3 ≤ P.size + 1)
    (hd : ∀ (i : Fin 3) (hi : i.val + 1 < 3),
      (([0, 0, 1] : List NNReal)[i.val] : ℝ) =
        Judgement.duration P ⟨i.val, by have := i.isLt; omega⟩) : False := by
  have h₀ := hd ⟨0, by decide⟩ (by decide)
  have h₁ := hd ⟨1, by decide⟩ (by decide)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, NNReal.coe_zero] at h₀ h₁
  apply no_first_two_zero_durations σ P (by omega)
  · exact_mod_cast h₀.symm
  · exact_mod_cast h₁.symm

end STLTableau.IntervalPartition

#print axioms STLTableau.IntervalPartition.zero_zero_one_no_alignment

namespace STLTableau.Section4.Finiteness.UntilAdmissionAudit.PrunedExecution

/-- No partition matches both initial zero-duration visits of the
three-frame path. -/
theorem no_raw_duration_partition :
    ¬ ∃ P : IntervalPartition rho.domain, ∃ hlen : 3 ≤ P.size + 1,
      ∀ (i : Fin 3) (hi : i.val + 1 < 3),
        (([0, 0, 1] : List NNReal)[i.val] : ℝ) =
          STLTableau.Judgement.duration P ⟨i.val, by have := i.isLt; omega⟩ := by
  rintro ⟨P, hlen, hd⟩
  exact IntervalPartition.zero_zero_one_no_alignment rho P hlen hd

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execution, ``reaches, ``timed_path, ``witnessed_path,
      ``projects, ``finite_variability, ``one_positive_flow,
      ``recognizes_flow_partition, ``no_raw_duration_partition] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

end STLTableau.Section4.Finiteness.UntilAdmissionAudit.PrunedExecution

namespace STLTableau.Section4.Finiteness.UntilAdmissionAudit.SkippedFlowCandidate
open Section3
def pAtom : AtomicProposition Unit := ⟨1, fun _ => (), fun v => -v 0, .ge⟩
def qAtom : AtomicProposition Unit := ⟨0, Fin.elim0, fun _ => 0, .ge⟩
def p : Formula Unit := .atom pAtom
def q : Formula Unit := .atom qAtom
def root : Formula Unit := p.untimedUntil (q.untimedUntil q)
noncomputable def U := finiteRootTableau (Clock := Nat) (Set.univ : Set Unit) root
abbrev F1 := nested (Clock := Nat) p q q
abbrev F2 := immediate (Clock := Nat) q q
theorem base_members : F1 ∈ U.states ∧ F2 ∈ U.states :=
  (within_three Set.univ p q q (by trivial) (by trivial) (by trivial)).2
theorem no_terminal (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2) :
    Local.terminal ∉ U.label F := by
  rcases he with rfl | rfl <;>
    simp [U, finiteRootTableau, sparseDerivesTableau, Subgraph.restrict,
      JudgementTableau.tableau, JudgementTableau.labels, F1, F2, nested, deferred,
      immediate, plain, Section3.TransitionForm.union, Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState, Section3.StateForm.union, Section3.StateForm.ofLocal, Section3.StateForm.empty]
theorem compat (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2) :
    U.TerminalCompatible F := fun ht => (no_terminal F he ht).elim
noncomputable def T := U.pruneTerminal
theorem ready : T.TranslationReady :=
  U.pruneTerminal_translationReady
    (finiteRootTableau_translationReady _ (Set.toFinite _) root (by simp))
noncomputable def H := T.toAutomaton ready 1 (by norm_num)
theorem members : F1 ∈ T.states ∧ F2 ∈ T.states :=
  ⟨⟨base_members.1, compat _ (Or.inl rfl)⟩,
    ⟨base_members.2, compat _ (Or.inr rfl)⟩⟩
def val (t : ℝ) : T.HAVar → ℝ
  | .inl _ => t
  | .inr _ => t
theorem label_atoms (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2)
    (b : AtomicProposition Unit)
    (hb : Local.predicate (.plain (.atom b)) ∈ T.label F) :
    (F = F1 ∧ b = pAtom) ∨ b = qAtom := by
  rcases he with rfl | rfl <;>
    simp [T, Tableau.pruneTerminal, U, finiteRootTableau, sparseDerivesTableau,
      Subgraph.restrict, JudgementTableau.tableau, JudgementTableau.labels,
      F1, F2, nested, deferred, immediate, plain, Section3.TransitionForm.union,
      Section3.TransitionForm.ofState, Section3.TransitionForm.ofNextState, Section3.StateForm.union,
      Section3.StateForm.ofLocal, Section3.StateForm.empty, p, q, Formula.untimedUntil] at hb <;> aesop
theorem invariant (F : Section3.TransitionForm Nat Unit) (hf : F ∈ T.states)
    (he : F = F1 ∨ F = F2) (t : ℝ) (ht : t ≤ 1)
    (hz : F = F1 → t = 0) : (⟨F,hf⟩, val t) ∈ H.invariant := by
  constructor
  · intro b hb
    rcases label_atoms F he b hb with ⟨hF, rfl⟩ | rfl
    · refine ⟨?_, ?_⟩
      · intro i; trivial
      · simp [pAtom, val, hz hF, RealRelation.Holds]
    · refine ⟨(by intro i; exact Fin.elim0 i), le_refl 0⟩
  · intro _; exact ht
theorem different : F2 ≠ F1 := by
  intro he
  have hn := congrArg Section3.TransitionForm.nextPart he
  change none = some _ at hn
  cases hn
noncomputable def s1 : H.State :=
  ⟨(⟨F1,members.1⟩,val 0), invariant _ _ (Or.inl rfl) _ (by norm_num) (by simp)⟩
noncomputable def s2 (t : ℝ) (ht : t ≤ 1) : H.State :=
  ⟨(⟨F2,members.2⟩,val t), invariant _ _ (Or.inr rfl) _ ht (fun h => (different h).elim)⟩
theorem incoming_empty (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2) :
    (JudgementTableau.incoming F).guards = ∅ ∧
      (JudgementTableau.incoming F).resets = ClockResetSet.empty := by
  rcases he with rfl | rfl <;>
    simp [JudgementTableau.incoming,F1,F2,nested,deferred,immediate,plain,
      Section3.TransitionForm.union,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.union,Section3.StateForm.ofLocal,Section3.StateForm.empty,ClockResetSet.union,ClockResetSet.empty]
  all_goals rfl
theorem reset_empty (t : ℝ) : T.reset ClockResetSet.empty (val t) = val t := by
  funext x
  cases x with
  | inl x => rfl
  | inr x => cases x <;> rfl
theorem init : s1.val ∈ H.initial := by
  refine ⟨JudgementTableau.incoming F1, ?_, val 0, ?_, ?_⟩
  · exact ⟨⟨⟨derives_nested p q q (by trivial) (by trivial), rfl⟩, base_members.1⟩,
      compat _ (Or.inl rfl)⟩
  · intro g hg
    rw [(incoming_empty F1 (Or.inl rfl)).1] at hg
    exact False.elim hg
  · rw [(incoming_empty F1 (Or.inl rfl)).2]
    funext x
    cases x with
    | inl x => rfl
    | inr x => cases x <;> rfl
theorem jump : H.DiscreteStep s1 (s2 0 (by norm_num)) := by
  apply (T.discreteStep_iff ready 1 (by norm_num)).2
  refine ⟨JudgementTableau.incoming F2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨⟨base_members.1.1,base_members.2.1,_,rfl,
        derives_immediate q q (by trivial) (by trivial),rfl⟩,base_members.1,base_members.2⟩,
      compat _ (Or.inl rfl), compat _ (Or.inr rfl), no_terminal _ (Or.inl rfl)⟩
  · intro g hg
    rw [(incoming_empty F2 (Or.inr rfl)).1] at hg
    exact False.elim hg
  · exact ((incoming_empty F2 (Or.inr rfl)).2 ▸ reset_empty 0).symm
  · intro ht; exact (no_terminal F2 (Or.inr rfl) ht).elim
  · intro _; norm_num [s2,val,Tableau.globalClock]
theorem flow : H.ContinuousStep (s2 0 (by norm_num)) (s2 1 (by norm_num)) 1
    (fun t => val t.val) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro t
  refine ⟨⟨?_,?_⟩, invariant F2 members.2 (Or.inr rfl) _ t.property.2
    (fun h => (different h).elim)⟩
  · intro c
    change t.val = 0 + t.val
    ring
  · change t.val = 0 + t.val
    ring
def signal : FiniteSignal T.HAVar := ⟨1, by norm_num, fun t => val t.val⟩
noncomputable def execution : H.Execution signal where
  count := 1
  nonempty := by omega
  initialState := s1
  initial_mem := init
  initial_signal_eq := rfl
  start := fun _ => s2 0 (by norm_num)
  finish := fun _ => s2 1 (by norm_num)
  boundary := fun i => if i.val = 0 then 0 else 1
  first_zero := by simp
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  last_le_horizon := by norm_num [signal]
  duration := fun _ => 1
  duration_eq := by intro i; fin_cases i; norm_num
  curve := fun _ t => val t.val
  continuousStep := fun _ => flow
  initialSteps := Relation.ReflTransGen.single jump
  discreteSteps := by intro i hi; omega
  finalState := s2 1 (by norm_num)
  finalSteps := .refl
  final_signal_eq := by
    intro t ht
    have hlt := t.property.2
    change t.val < 1 at hlt
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false] at ht
    linarith
  signal_eq := by
    intro i t ht _
    fin_cases i
    change val t.val = val (t.val - (if (0 : ℕ) = 0 then 0 else 1))
    simp
theorem timed_path : T.TimedPath (twoPath (Clock := Nat) p q q)
    (val 0) (val 1) [0, 1] := by
  refine .step _ _ (Tableau.ClockElapse.zero T _) ?_ ?_
  · intro g hg
    change g ∈ (JudgementTableau.incoming F2).guards at hg
    rw [(incoming_empty F2 (Or.inr rfl)).1] at hg
    exact False.elim hg
  · change T.TimedPath (.last (JudgementTableau.incoming F2) F2)
      (T.reset (JudgementTableau.incoming F2).resets (val 0)) (val 1) [1]
    rw [(incoming_empty F2 (Or.inr rfl)).2, reset_empty]
    exact .last _ _ (T.continuousStep_clockElapse ready 1 (by norm_num) flow)

/-- The witness follows the execution's initial jump and subsequent flow. -/
theorem witnessed_path : T.ExecutionPathWitness ready 1 (by norm_num)
    s1 (s2 1 (by norm_num)) (twoPath (Clock := Nat) p q q) := by
  obtain ⟨l, he, hg, hr, _⟩ := (T.discreteStep_iff ready 1 (by norm_num)).mp jump
  have hl : l = JudgementTableau.incoming F2 := by
    obtain ⟨_, _, N, _, _, hl⟩ := he.1.1
    exact hl
  subst l
  exact .jump _ he hg hr jump (.flow 1 (fun t => val t.val) flow (.stop _ _))

theorem reaches : H.Reaches signal T.goalModes :=
  ⟨execution, ⟨rfl,base_members.2⟩,compat _ (Or.inr rfl)⟩
def rho : FiniteSignal Unit := ⟨1, by norm_num, fun t _ => t.val⟩
theorem projects : T.ProjectsTo signal rho :=
  ⟨rfl, by intro t u ht x; exact ht⟩
theorem normalized_input : root.NormalizedReady :=
  .until (.atom pAtom) (.until (.atom qAtom) (.atom qAtom))

noncomputable def rhoPartition : IntervalPartition rho.domain :=
  execution.fullFlowPartition rfl
theorem one_piece : rhoPartition.size = 1 := rfl
theorem p_iff_zero (t : rho.Time) : rho.Satisfies p t ↔ t.val = 0 := by
  change -t.val ≥ 0 ↔ t.val = 0
  have hn := t.property.1
  constructor <;> intro ht <;> linarith
theorem q_true (t : rho.Time) : rho.Satisfies q t := le_refl 0
theorem inner_true (t : rho.Time) : rho.Satisfies (q.untimedUntil q) t :=
  FiniteSignal.satisfies_untimedUntil_of_and rho q q t (q_true t) (q_true t)
theorem root_iff_zero (t : rho.Time) : rho.Satisfies root t ↔ t.val = 0 := by
  constructor
  · intro ht
    exact (p_iff_zero t).mp (FiniteSignal.satisfies_left_of_until rho _ _ _ t ht)
  · intro ht
    exact FiniteSignal.satisfies_untimedUntil_of_and rho p (q.untimedUntil q) t
      ((p_iff_zero t).mpr ht) (inner_true t)
theorem not_recognizes_flow_partition :
    ¬ U.recognizes JudgementTableau.labels_finite rho rhoPartition := by
  intro h
  have hall := finiteRootTableau_root_everywhere_of_one_piece
    (Clock := Nat) Set.univ root rho rhoPartition one_piece h
  have hz := (root_iff_zero ⟨1/2, by norm_num [rho]⟩).mp
    (hall ⟨1/2, by norm_num [rho]⟩)
  norm_num at hz
theorem not_pruned_recognizes_flow_partition :
    ¬ T.recognizes JudgementTableau.labels_finite rho rhoPartition := by
  intro h
  exact not_recognizes_flow_partition
    ((U.pruneTerminal_recognizes_iff JudgementTableau.labels_finite rho rhoPartition).mp h)

noncomputable def stablePartition : IntervalPartition rho.domain :=
  execution.pointOpenFlowPartition
theorem zero_agreement (i : Fin stablePartition.size) (u v : rho.Time)
    (hu : u.val ∈ (stablePartition.interval i).carrier)
    (hv : v.val ∈ (stablePartition.interval i).carrier) :
    u.val = 0 ↔ v.val = 0 := by
  change Fin 2 at i
  fin_cases i
  · change u.val ∈ (IntervalPartition.pointOpenPiece execution.boundary ⟨0, by decide⟩).carrier at hu
    change v.val ∈ (IntervalPartition.pointOpenPiece execution.boundary ⟨0, by decide⟩).carrier at hv
    rw [IntervalPartition.pointOpenPiece_carrier] at hu hv
    simp [execution] at hu hv
    exact ⟨fun _ => congrArg Subtype.val hv, fun _ => congrArg Subtype.val hu⟩
  · change u.val ∈ (IntervalPartition.pointOpenPiece execution.boundary ⟨1, by decide⟩).carrier at hu
    change v.val ∈ (IntervalPartition.pointOpenPiece execution.boundary ⟨1, by decide⟩).carrier at hv
    rw [IntervalPartition.pointOpenPiece_carrier] at hu hv
    simp [execution] at hu hv
    exact iff_of_false (ne_of_gt hu.1) (ne_of_gt hv.1)
theorem sub_root (χ : Formula Unit) (h : χ.IsSubformula root) :
    χ = root ∨ χ = p ∨ χ = q.untimedUntil q ∨ χ = q := by
  cases h with
  | refl => exact Or.inl rfl
  | until_left h => cases h; exact Or.inr (Or.inl rfl)
  | until_right h =>
    cases h with
    | refl => exact Or.inr (Or.inr (Or.inl rfl))
    | until_left h => cases h; exact Or.inr (Or.inr (Or.inr rfl))
    | until_right h => cases h; exact Or.inr (Or.inr (Or.inr rfl))
theorem stable : rho.StablePartition root stablePartition := by
  intro i χ hχ u v hu hv
  rcases sub_root χ hχ with rfl | rfl | rfl | rfl
  · exact (root_iff_zero u).trans ((zero_agreement i u v hu hv).trans (root_iff_zero v).symm)
  · exact (p_iff_zero u).trans ((zero_agreement i u v hu hv).trans (p_iff_zero v).symm)
  · exact ⟨fun _ => inner_true v, fun _ => inner_true u⟩
  · exact ⟨fun _ => q_true v, fun _ => q_true u⟩
theorem finite_variability : rho.HasFiniteVariability root := ⟨stablePartition, stable⟩
/-- Splitting off the singleton at zero gives a stable partition on which the
signal is recognized. -/
theorem recognizes_stable_partition :
    U.recognizes JudgementTableau.labels_finite rho stablePartition := by
  apply (finiteRootTableau_recognizes_iff (Clock := Nat) Set.univ root
    normalized_input.mixedReady rho stablePartition stable).2
  exact (root_iff_zero ⟨0, le_rfl, rho.horizon_pos⟩).mpr rfl

theorem recognizes_review_partition :
    U.recognizes JudgementTableau.labels_finite rho execution.reviewInducedPartition := by
  rw [execution.reviewInducedPartition_of_horizon rfl]
  exact recognizes_stable_partition

theorem directPath_labels (F : Section3.TransitionForm Nat Unit)
    (he : F = F1 ∨ F = F2) (l : Local Nat Unit) (hl : l ∈ U.label F) :
    (F = F1 ∧ l = .predicate (.plain p)) ∨ l = .predicate (.plain q) := by
  rcases he with rfl | rfl <;>
    simp [U, finiteRootTableau, sparseDerivesTableau, Subgraph.restrict,
      JudgementTableau.tableau, JudgementTableau.labels, F1, F2, nested,
      deferred, immediate, plain, Section3.TransitionForm.union,
      Section3.TransitionForm.ofState, Section3.TransitionForm.ofNextState,
      Section3.StateForm.union, Section3.StateForm.ofLocal, Section3.StateForm.empty,
      root, p, q, Formula.untimedUntil, Section3.TransitionForm.KeepAtomic,
      Predicate.IsAtomic] at hl ⊢ <;> aesop

/-- The two-state path records the initial and post-jump modes of
`execution`. The flow remains in the second mode. -/
theorem directPath_skeleton : twoPath (Clock := Nat) p q q =
    .step (JudgementTableau.incoming F1) execution.initialState.val.1.val
      (.last (JudgementTableau.incoming F2)
        (execution.start ⟨0, execution.nonempty⟩).val.1.val) := rfl

theorem directPath_trace (α : ClockValuation Nat) :
    ((twoPath (Clock := Nat) p q q).trace JudgementTableau.labels
      JudgementTableau.labels_finite).holds rho stablePartition α ⟨0, by omega⟩ := by
  have guards (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2)
      (β : ClockValuation Nat) : ∀ g ∈ (JudgementTableau.incoming F).guards, g.holds β := by
    intro g hg
    rw [(incoming_empty F he).1] at hg
    exact False.elim hg
  have first (β : ClockValuation Nat) : ∀ l ∈ U.label F1,
      l.holds rho stablePartition β ⟨0, by omega⟩ := by
    intro l hl
    rcases directPath_labels F1 (Or.inl rfl) l hl with ⟨_, rfl⟩ | rfl
    all_goals
      change (if h : 0 < stablePartition.size then _ else False)
      rw [dif_pos (show 0 < stablePartition.size by decide)]
      intro t ht
    · apply (p_iff_zero t).mpr
      change t.val ∈
        (IntervalPartition.pointOpenPiece execution.boundary ⟨0, by decide⟩).carrier at ht
      rw [IntervalPartition.pointOpenPiece_carrier] at ht
      change t.val ∈ ({0} : Set ℝ) at ht
      exact ht
    · exact q_true t
  have last (β : ClockValuation Nat) : ∀ l ∈ U.label F2,
      l.holds rho stablePartition β ⟨1, by change 1 < 2 + 1; omega⟩ := by
    intro l hl
    rcases directPath_labels F2 (Or.inr rfl) l hl with ⟨he, _⟩ | rfl
    · exact (different he).elim
    · change (if h : 1 < stablePartition.size then _ else False)
      rw [dif_pos (show 1 < stablePartition.size by decide)]
      intro t _
      exact q_true t
  refine ⟨⟨guards F1 (Or.inl rfl) _, first _⟩, ?_⟩
  change (if h : 0 < stablePartition.size then _ else False)
  rw [dif_pos (show 0 < stablePartition.size by decide)]
  exact ⟨guards F2 (Or.inr rfl) _, last _⟩

/-- The execution's two-frame path recognizes the refined partition. -/
theorem recognizes_review_partition_direct :
    U.recognizes JudgementTableau.labels_finite rho execution.reviewInducedPartition := by
  rw [execution.reviewInducedPartition_of_horizon rfl]
  have hr := twoPath_accepting_run (Clock := Nat) Set.univ p q q
    (by trivial) (by trivial) (by trivial)
  exact ⟨twoPath p q q, hr.1, hr.2, directPath_trace⟩

theorem pruned_recognizes_review_partition_direct :
    T.recognizes JudgementTableau.labels_finite rho execution.reviewInducedPartition :=
  (U.pruneTerminal_recognizes_iff JudgementTableau.labels_finite rho
    execution.reviewInducedPartition).mpr recognizes_review_partition_direct

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``execution, ``reaches, ``projects, ``not_recognizes_flow_partition,
      ``not_pruned_recognizes_flow_partition, ``finite_variability,
      ``recognizes_stable_partition, ``recognizes_review_partition,
      ``timed_path, ``witnessed_path, ``directPath_skeleton, ``directPath_trace,
      ``recognizes_review_partition_direct, ``pruned_recognizes_review_partition_direct] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"
end STLTableau.Section4.Finiteness.UntilAdmissionAudit.SkippedFlowCandidate

namespace STLTableau.Section4.Finiteness.UntilAdmissionAudit.PrunedExecution
open Section3

theorem rebasedPath_labels (F : Section3.TransitionForm Nat Unit)
    (he : F = F1 ∨ F = F2) (l : Local Nat Unit) (hl : l ∈ T.label F) :
    l = .predicate (.plain a) := by
  rcases he with rfl | rfl <;>
    simp [T, Tableau.pruneTerminal, ConcreteExecution.T, finiteRootTableau,
      sparseDerivesTableau, Subgraph.restrict, JudgementTableau.tableau,
      JudgementTableau.labels, F1, F2, nested, deferred, immediate, plain,
      Section3.TransitionForm.union, Section3.TransitionForm.ofState,
      Section3.TransitionForm.ofNextState, Section3.StateForm.union,
      Section3.StateForm.ofLocal, Section3.StateForm.empty,
      a, Formula.untimedUntil, Section3.TransitionForm.KeepAtomic,
      Predicate.IsAtomic] at hl ⊢ <;> aesop

/-- The retained F1→F2 path occupies the boundary singleton and open flow
piece. This does not assign all three original modes to distinct pieces. -/
theorem rebasedPath_trace (α : ClockValuation Nat) :
    ((twoPath (Clock := Nat) a a a).trace JudgementTableau.labels
      JudgementTableau.labels_finite).holds rho execution.pointOpenFlowPartition
        α ⟨0, by omega⟩ := by
  have guards (F : Section3.TransitionForm Nat Unit)
      (he : F = F0 ∨ F = F1 ∨ F = F2) (β : ClockValuation Nat) :
      ∀ g ∈ (JudgementTableau.incoming F).guards, g.holds β := by
    intro g hg
    rw [(incoming_empty F he).1] at hg
    exact False.elim hg
  have labels (F : Section3.TransitionForm Nat Unit) (he : F = F1 ∨ F = F2)
      (β : ClockValuation Nat) (k : Fin 2) : ∀ l ∈ T.label F,
      l.holds rho execution.pointOpenFlowPartition β
        ⟨k.val, by change k.val < 2 + 1; have := k.isLt; omega⟩ := by
    intro l hl
    have heq := rebasedPath_labels F he l hl
    subst l
    change (if h : k.val < execution.pointOpenFlowPartition.size then _ else False)
    rw [dif_pos (show k.val < execution.pointOpenFlowPartition.size from k.isLt)]
    intro t _
    exact atom_true t
  refine ⟨⟨guards F1 (Or.inr (Or.inl rfl)) _, labels F1 (Or.inl rfl) _ ⟨0, by decide⟩⟩, ?_⟩
  change (if h : 0 < execution.pointOpenFlowPartition.size then _ else False)
  rw [dif_pos (show 0 < execution.pointOpenFlowPartition.size by decide)]
  exact ⟨guards F2 (Or.inr (Or.inr rfl)) _, labels F2 (Or.inr rfl) _ ⟨1, by decide⟩⟩

/-- The path beginning in the second mode recognizes the partition induced
by the execution. -/
theorem recognizes_review_partition_rebased :
    ConcreteExecution.T.recognizes JudgementTableau.labels_finite
      rho execution.reviewInducedPartition := by
  rw [execution.reviewInducedPartition_of_horizon rfl]
  have hr := twoPath_accepting_run (Clock := Nat) Set.univ a a a
    (by trivial) (by trivial) (by trivial)
  exact ⟨twoPath a a a, hr.1, hr.2, rebasedPath_trace⟩

/-- The pruned tableau recognizes the same induced partition. -/
theorem pruned_recognizes_review_partition_rebased :
    T.recognizes JudgementTableau.labels_finite rho execution.reviewInducedPartition :=
  (ConcreteExecution.T.pruneTerminal_recognizes_iff JudgementTableau.labels_finite
    rho execution.reviewInducedPartition).mpr recognizes_review_partition_rebased

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``rebasedPath_trace, ``recognizes_review_partition_rebased,
      ``pruned_recognizes_review_partition_rebased] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} uses unapproved axiom {ax}"

end STLTableau.Section4.Finiteness.UntilAdmissionAudit.PrunedExecution
