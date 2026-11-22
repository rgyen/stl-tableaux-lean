import STLTableaux.Finiteness.Derivation.Branches.RawBranchNextOrigin
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNextUnique
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Actual raw occurrence witnesses for predicates in a safely normalized next
state. Reset scope is handled by normalization, not an assumed provenance tag. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

private def nextPayloads : MixedJ Clock Var → Set (MixedJ Clock Var)
  | .next K => {K}
  | .conj J K => nextPayloads J ∪ nextPayloads K
  | .reset _ J => nextPayloads J
  | _ => ∅

private def nextPredicates : MixedJ Clock Var → Set (Predicate Clock Var)
  | .next J => J.currentPredicates
  | .conj J K => nextPredicates J ∪ nextPredicates K
  | .reset _ J => nextPredicates J
  | _ => ∅

private def normalizedNextPredicates (F : Section3.TransitionForm Clock Var) : Set (Predicate Clock Var) :=
  match F.nextPart with
  | none => ∅
  | some N => {p | Local.predicate p ∈ N.locals}

private theorem current_predicates_safe {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) (p : Predicate Clock Var) :
    Local.predicate p ∈ F.current.locals ↔ p ∈ J.currentPredicates := by
  induction h with
  | terminal => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | clock => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofGuard,Section3.Judgement.currentPredicates]
  | marker => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | predicate q => simp [Section3.TransitionForm.ofState,Section3.StateForm.ofLocal,Section3.Judgement.currentPredicates]
  | conj h g hc ih ig => exact or_congr ih ig
  | reset R h hd ih => exact ih
  | next h hn ih => simp [Section3.TransitionForm.ofNextState,Section3.StateForm.empty,Section3.Judgement.currentPredicates]

private theorem next_predicates_union (F G : Section3.TransitionForm Clock Var) :
    normalizedNextPredicates (F.union G) = normalizedNextPredicates F ∪ normalizedNextPredicates G := by
  cases hf : F.nextPart <;> cases hg : G.nextPart <;>
    ext p <;> simp [normalizedNextPredicates,Section3.TransitionForm.union,Section3.TransitionForm.unionNext,
      Section3.StateForm.union,hf,hg]

private theorem next_predicates_safe {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    normalizedNextPredicates F = nextPredicates J := by
  induction h with
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | predicate => rfl
  | conj h g hc ih ig => exact (next_predicates_union _ _).trans (congrArg₂ Set.union ih ig)
  | reset R h hd ih => exact ih
  | @next J F h hn ih =>
      ext p
      exact current_predicates_safe h p

set_option maxHeartbeats 12000000 in
set_option linter.unusedSimpArgs false in
private theorem actual_literal_next [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B)
    (N : MixedJ Clock Var) (hn : N ∈ nextPayloads B) : Conjunct B (.next N) := by
  cases h with
  | finite hr hb =>
    (cases hr <;>
      simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
        ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
        ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
        ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
      Section3.Judgement.ofFinite,Section3.Predicate.ofFinite,
      Section3.Judgement.currentPredicates,nextPayloads]
    all_goals first | exact .here _ | exact .right (.here _)
  | infinite hr hb =>
    (cases hr <;>
      simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
        UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hb <;>
      (try split_ifs at hb) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hb) <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp_all [ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
      ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
      ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
      ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
      UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
      UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
      UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
      UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
      UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
      UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,
      Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,
      Section3.Judgement.currentPredicates,nextPayloads]
    all_goals first | exact .here _ | exact .right (.here _)
  | opening c m kind a φ =>
    simp_all [UnboundedClocked.opening,Section3.Judgement.ofUnbounded,Section3.Predicate.ofUnbounded,Section3.Judgement.currentPredicates,nextPayloads]

private theorem next_predicate_payload (J : MixedJ Clock Var) (p : Predicate Clock Var) :
    p ∈ nextPredicates J ↔ ∃ K ∈ nextPayloads J, p ∈ K.currentPredicates := by
  induction J with
  | terminal | clock | marker | predicate => simp [nextPredicates,nextPayloads]
  | next K => simp [nextPredicates,nextPayloads]
  | reset R J ih => exact ih
  | conj J K ih ik =>
    simp only [nextPredicates,nextPayloads,Set.mem_union,ih,ik]
    aesop

/-- A normalized next-state predicate has an actual literal raw payload witness
in this ordinary branch. This asserts occurrence, not just representability. -/
theorem RawBranch.normalized_next_predicate_origin [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hRaw : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (q : Predicate Clock Var) (hq : Local.predicate q ∈ N.locals) :
    ∃ K, Conjunct B (.next K) ∧ q ∈ K.currentPredicates := by
  have hp : q ∈ nextPredicates B := by
    rw [← next_predicates_safe hSafe]
    exact (show q ∈ normalizedNextPredicates F by
      simpa only [normalizedNextPredicates,hNext,Set.mem_setOf_eq] using hq)
  obtain ⟨K,hK,hqK⟩ := (next_predicate_payload B q).1 hp
  exact ⟨K,actual_literal_next hRaw K hK,hqK⟩

/-- Exact actual-source classification in the normalized next state. The upper
alternative contains the literal raw freezing payload and marker witness. -/
theorem RawBranch.normalized_next_bounded_origin [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hRaw : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (c d : Clock) (m q : Marker) (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var)
    (hq : Local.predicate (.bounded c d m q kind I φ) ∈ N.locals) :
    (∃ b, p = .upper c b kind I φ ∧ c ≠ d ∧
      ∃ K ℓ, Conjunct B (.next K) ∧ q = Marker.complement ℓ ∧
        FrozenOccurrence K c d m ℓ kind I φ) ∨
      (∃ b, p = .bounded c d b q kind I φ ∧ c ≠ d) := by
  obtain ⟨K,hK,hqK⟩ := hRaw.normalized_next_predicate_origin hSafe hNext _ hq
  rcases hRaw.next_bounded_origin hK c d m q kind I φ hqK with
    ⟨b,hp,hcd,ℓ,hqℓ,hf⟩ | hb
  · exact Or.inl ⟨b,hp,hcd,K,ℓ,hK,hqℓ,hf⟩
  · exact Or.inr hb

/-- Normalization cannot multiply an actual branch's unique bounded next
continuation. This counts neither plain next demands nor retained annotations. -/
theorem RawBranch.normalized_next_bounded_unique [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (hRaw : RawBranch p B)
    {F : Section3.TransitionForm Clock Var} (hSafe : SafeNormalization B F)
    {N : Section3.StateForm Clock Var} (hNext : F.nextPart = some N)
    (c₁ d₁ : Clock) (m₁ q₁ : Marker) (kind₁ : TemporalKind) (I₁ : TimeInterval) (φ₁ : Formula Var)
    (c₂ d₂ : Clock) (m₂ q₂ : Marker) (kind₂ : TemporalKind) (I₂ : TimeInterval) (φ₂ : Formula Var)
    (hq₁ : Local.predicate (.bounded c₁ d₁ m₁ q₁ kind₁ I₁ φ₁) ∈ N.locals)
    (hq₂ : Local.predicate (.bounded c₂ d₂ m₂ q₂ kind₂ I₂ φ₂) ∈ N.locals) :
    Predicate.bounded c₁ d₁ m₁ q₁ kind₁ I₁ φ₁ =
      Predicate.bounded c₂ d₂ m₂ q₂ kind₂ I₂ φ₂ := by
  obtain ⟨K₁,hK₁,hqK₁⟩ := hRaw.normalized_next_predicate_origin hSafe hNext _ hq₁
  obtain ⟨K₂,hK₂,hqK₂⟩ := hRaw.normalized_next_predicate_origin hSafe hNext _ hq₂
  exact hRaw.next_bounded_unique hK₁ hK₂ c₁ d₁ m₁ q₁ kind₁ I₁ φ₁
    c₂ d₂ m₂ q₂ kind₂ I₂ φ₂ hqK₁ hqK₂

end STLTableau.Section4.Finiteness
