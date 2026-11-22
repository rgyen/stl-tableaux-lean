import STLTableaux.Finiteness.Derivation.CanonicalProjections

/-! Current guard projection of actual raw syntax, canonical bodies and
concrete branches. Reset scopes do not hide guards; next scopes do. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

def currentGuards : MixedJ Clock Var → Set (Section3.Guard Clock)
  | .clock c r a => {⟨c,r,a⟩}
  | .conj J K => currentGuards J ∪ currentGuards K
  | .reset _ J => currentGuards J
  | _ => ∅

theorem ACIdem.currentGuards_eq {J K : MixedJ Clock Var} (h : StructuralEq J K) :
    currentGuards J = currentGuards K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => exact Set.union_assoc _ _ _
  | comm => exact Set.union_comm _ _
  | idem => exact Set.union_self _
  | conj h g ih ig => exact congrArg₂ Set.union ih ig
  | reset R h ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

theorem SafeNormalization.currentGuards_eq {J : MixedJ Clock Var}
    {F : Section3.TransitionForm Clock Var} (h : SafeNormalization J F) :
    F.current.guards = currentGuards J := by
  induction h with
  | terminal => rfl
  | clock => rfl
  | marker => rfl
  | predicate => rfl
  | conj h g hc ih ig => exact congrArg₂ Set.union ih ig
  | reset R h hd ih => exact ih
  | next h hn ih => rfl

private def optionGuards : Option (MixedJ Clock Var) → Set (Section3.Guard Clock)
  | none => ∅
  | some J => currentGuards J

private theorem optional_guards (J K : Option (MixedJ Clock Var)) :
    optionGuards (optionalConj J K) = optionGuards J ∪ optionGuards K := by
  cases J <;> cases K <;> simp [optionalConj,optionGuards,currentGuards]

private theorem fold_guards (Js : List (MixedJ Clock Var)) (g : Section3.Guard Clock) :
    g ∈ optionGuards (foldCurrent Js) ↔ ∃ J ∈ Js, g ∈ currentGuards J := by
  induction Js with
  | nil => simp [foldCurrent,optionGuards]
  | cons J Js ih =>
      rw [foldCurrent,optional_guards]
      change (g ∈ currentGuards J ∨ g ∈ optionGuards (foldCurrent Js)) ↔ _
      simp only [ih,List.mem_cons,exists_eq_or_imp]

theorem canonical_currentGuards
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) :
    currentGuards C = {g | g ∈ G} := by
  have hp : optionGuards ((foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next)).map
      (Section3.Judgement.reset R)) = ∅ := by
    cases hf : foldCurrent (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) with
    | none => rfl
    | some K =>
      change currentGuards K = ∅
      ext g
      have he := fold_guards (L.map Local.toJudgement ++ Ns.map Section3.Judgement.next) g
      rw [hf] at he
      simp only [optionGuards] at he
      rw [he]
      simp only [List.mem_append,List.mem_map]
      constructor
      · rintro ⟨J,(⟨l,hl,rfl⟩ | ⟨N,hN,rfl⟩),hg⟩
        · cases l <;> exact hg
        · exact hg
      · exact False.elim
  have he := congrArg optionGuards h
  simp only [canonicalSyntax] at he
  rw [optional_guards,hp,Set.union_empty] at he
  change optionGuards (foldCurrent (G.map (fun g => g.toJudgement))) = currentGuards C at he
  rw [← he]
  ext g
  rw [fold_guards]
  simp only [List.mem_map]
  constructor
  · rintro ⟨J,⟨a,ha,rfl⟩,hg⟩
    have hg' : g = a := by simpa only [Guard.toJudgement,currentGuards,Set.mem_singleton_iff] using hg
    exact hg' ▸ ha
  · intro hg
    exact ⟨g.toJudgement,⟨g,hg,rfl⟩,by cases g; exact Set.mem_singleton _⟩

theorem canonical_guards_nil_of_empty
    {R : ClockResetSet Clock} {G : List (Section3.Guard Clock)}
    {L : List (Local Clock Var)} {Ns : List (MixedJ Clock Var)} {C : MixedJ Clock Var}
    (h : canonicalSyntax R G L Ns = some C) (hg : currentGuards C = ∅) : G = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro g hm
  have he := canonical_currentGuards h
  rw [hg] at he
  exact (Set.ext_iff.mp he g).2 hm

set_option maxHeartbeats 2400000 in
set_option linter.unusedSimpArgs false in
private theorem finite_current_guards [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var} (hm : B ∈ R.branches) :
    currentGuards (Judgement.ofFinite B) = ∅ := by
  classical
  (cases hr <;>
    simp only [ExpansionRule.plainAnd,ExpansionRule.plainOr,ExpansionRule.plainUntil,
      ExpansionRule.plainRelease,ExpansionRule.openEventually,ExpansionRule.openAlways,
      ExpansionRule.upperAlways,ExpansionRule.boundedAlways,ExpansionRule.upperEventually,
      ExpansionRule.boundedEventually,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
    (try split_ifs at hm) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp_all [currentGuards,Section3.Judgement.ofFinite,
    Section3.Judgement.currentPredicates,Predicate.ofFinite,
    ExpansionRule.upperAlways_defer,ExpansionRule.upperAlways_check,
    ExpansionRule.boundedAlways_defer,ExpansionRule.boundedAlways_check,ExpansionRule.boundedAlways_finish,
    ExpansionRule.upperEventually_defer,ExpansionRule.upperEventually_check,
    ExpansionRule.boundedEventually_defer,ExpansionRule.boundedEventually_check,ExpansionRule.boundedEventually_finish,
    STLTableau.Judgement.markedLT_eq_clock,STLTableau.Judgement.markedGT_eq_clock,
    ClockResetSet.clocks_union,Set.subset_def]

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
private theorem infinite_current_guards [DecidableEq Clock]
    {p : UnboundedClocked.Predicate Clock Var} {Bs : List (UnboundedClocked.Node Clock Var)}
    (hr : UnboundedClocked.ConcreteRule p Bs) {B : UnboundedClocked.Node Clock Var} (hm : B ∈ Bs) :
    currentGuards (Judgement.ofUnbounded B) = ∅ := by
  classical
  (cases hr <;>
    simp only [UnboundedClocked.upperAlwaysBranches,UnboundedClocked.boundedAlwaysBranches,
      UnboundedClocked.upperEventuallyBranches,UnboundedClocked.boundedEventuallyBranches,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hm <;>
    (try split_ifs at hm) <;>
    (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hm) <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp_all [currentGuards,Section3.Judgement.ofUnbounded,
    Section3.Judgement.currentPredicates,Predicate.ofUnbounded,
    UnboundedClocked.upperAlwaysDefer,UnboundedClocked.upperAlwaysCheck,
    UnboundedClocked.boundedAlwaysDefer,UnboundedClocked.boundedAlwaysCheck,
    UnboundedClocked.upperEventuallyDefer,UnboundedClocked.upperEventuallyCheck,
    UnboundedClocked.boundedEventuallyDefer,UnboundedClocked.boundedEventuallyCheck,
    UnboundedClocked.boundedEventuallyFinish,UnboundedClocked.alwaysWait,UnboundedClocked.alwaysLast,
    UnboundedClocked.Node.lt,UnboundedClocked.Node.gt,ClockResetSet.clocks_union,Set.subset_def]


theorem RawBranch.currentGuards_empty [DecidableEq Clock]
    {p : Predicate Clock Var} {B : MixedJ Clock Var} (h : RawBranch p B) :
    currentGuards B = ∅ := by
  cases h with
  | finite hr hm => exact finite_current_guards hr hm
  | infinite hr hm => exact infinite_current_guards hr hm
  | opening c m kind a φ =>
      simp [currentGuards,Judgement.ofUnbounded,UnboundedClocked.opening]

end STLTableau.Section4.Finiteness
