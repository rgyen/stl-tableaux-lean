import STLTableaux.Automata.Translation.EndPositionCorrectness
import STLTableaux.Automata.Recognition.ForwardWellBehaved
import STLTableaux.Finiteness.Inventory.RootFormulaInventory
import Mathlib.Topology.Order.OrderClosed
import STLTableaux.Automata.Translation.NormalizedInputTranslation
import STLTableaux.Semantics.Partitions.SingletonBoundaryPartition
import STLTableaux.Finiteness.Inventory.RootSlotPalette
import STLTableaux.Automata.Translation.InitialTerminalSupport
import STLTableaux.Finiteness.ClockAllocation.SelectedNextAnnotations
import STLTableaux.Finiteness.Derivation.Branches.RawBranchNormalization
import STLTableaux.Automata.Translation.LocalClosureGraph
import STLTableaux.Automata.Translation.FinalClosureSupport
import STLTableaux.Finiteness.Correctness.JudgementTableauSoundness
import STLTableaux.Finiteness.Derivation.DerivationRelation
import STLTableaux.Automata.Recognition.EarlyGoalPrefix
import STLTableaux.Automata.Execution.AppendObservedFlow

/-! A recognized signal for which `typedAutomaton` cannot reach a goal. -/

/- TailDependenceAudit -/
namespace STLTableau.TailDependenceAudit
def I : BoundedTimeInterval := ⟨0,1,by norm_num,by norm_num⟩
def J : BoundedTimeInterval := ⟨1,2,by norm_num,by norm_num⟩
def a (b : Bool) : AtomicProposition Bool := ⟨1,fun _ => b,fun s => s 0,.ge⟩
def p : Formula Bool := .atom (a false)
def q : Formula Bool := .atom (a true)
def body : Formula Bool := p.or (.eventually J q)
def ψ : Formula Bool := .always I body
noncomputable def σ : FiniteSignal Bool :=
  ⟨2,by norm_num,fun t b => if b then 0 else -|t.val - 1|⟩
noncomputable def σ' (T : ℝ) : FiniteSignal Bool :=
  ⟨2,by norm_num,fun t b => if b then -(max 0 (t.val-T)) else -|t.val-1|⟩
theorem same_through (T : ℝ) (t : σ.Time) (ht : t.val ≤ T) :
    (σ' T).value t = σ.value t := by
  funext b
  cases b
  · rfl
  · change -max 0 (t.val - T) = 0
    rw [max_eq_left (by linarith)]; simp

theorem actual_sat : σ.Satisfies ψ ⟨0,by norm_num [σ]⟩ := by
  apply (FiniteSignal.satisfies_always_iff σ I body _).2
  intro t ht
  change 0 ≤ t.val - 0 ∧ t.val - 0 ≤ 1 at ht
  apply (FiniteSignal.satisfies_or σ p (.eventually J q) t).2
  by_cases he : t.val = 1
  · left
    change -|t.val - 1| ≥ 0
    simp [he]
  · right
    apply (FiniteSignal.satisfies_eventually_iff σ J q t).2
    have hlt : t.val < 1 := lt_of_le_of_ne (by linarith [ht.2]) he
    let u : σ.Time := ⟨t.val+1,by
      change 0 ≤ _ ∧ _ < 2
      constructor <;> linarith [ht.1]⟩
    refine ⟨u,?_,?_⟩
    · change 1 ≤ t.val+1-t.val ∧ t.val+1-t.val ≤ 2
      constructor <;> linarith
    · change (0:ℝ) ≥ 0
      rfl

theorem changed_false (T : ℝ) (hT : 0 ≤ T) (hτ : T < 2) :
    ¬ (σ' T).Satisfies ψ ⟨0,by norm_num [σ']⟩ := by
  intro hr
  let t : (σ' T).Time := ⟨T/2,by change 0 ≤ _ ∧ _ < 2; constructor <;> linarith⟩
  have ho := (FiniteSignal.satisfies_always_iff (σ' T) I body _).1 hr t
    (by change 0 ≤ T/2-0 ∧ T/2-0 ≤ 1; constructor <;> linarith)
  rcases (FiniteSignal.satisfies_or (σ' T) p (.eventually J q) t).1 ho with hp | hf
  · change -|T/2-1| ≥ 0 at hp
    rw [abs_of_neg (by linarith)] at hp
    linarith
  · obtain ⟨u, hw, hq⟩ := (FiniteSignal.satisfies_eventually_iff (σ' T) J q t).1 hf
    change 1 ≤ u.val-T/2 ∧ u.val-T/2 ≤ 2 at hw
    change -max 0 (u.val-T) ≥ 0 at hq
    linarith [le_max_right (0 : ℝ) (u.val-T), hw.1]

theorem atom_cases {atom : AtomicProposition Bool}
    (h : Formula.IsSubformula (.atom atom) ψ) : atom = a false ∨ atom = a true := by
  classical
  have := Section4.Finiteness.subformula_mem_rootPlainFormulas h
  simpa [Section4.Finiteness.rootPlainFormulas,ψ,body,Formula.always,Formula.eventually,
    Formula.or,p,q] using this

theorem wellBehaved_actual : SignalAtomRightContinuous σ ψ := by
  intro atom h t
  rcases atom_cases h with rfl | rfl
  · change ContinuousWithinAt (fun u : σ.Time => -|u.val-1|) _ t
    exact ((continuous_subtype_val.sub continuous_const).abs.neg).continuousAt.continuousWithinAt
  · change ContinuousWithinAt (fun _ : σ.Time => (0 : ℝ)) _ t
    exact continuous_const.continuousAt.continuousWithinAt

theorem wellBehaved_changed (T : ℝ) : SignalAtomRightContinuous (σ' T) ψ := by
  intro atom h t
  rcases atom_cases h with rfl | rfl
  · change ContinuousWithinAt (fun u : (σ' T).Time => -|u.val-1|) _ t
    exact ((continuous_subtype_val.sub continuous_const).abs.neg).continuousAt.continuousWithinAt
  · change ContinuousWithinAt (fun u : (σ' T).Time => -(max 0 (u.val-T))) _ t
    exact ((continuous_const.max (continuous_subtype_val.sub continuous_const)).neg).continuousAt.continuousWithinAt

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``same_through,``actual_sat,``changed_false,``wellBehaved_actual,``wellBehaved_changed] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.TailDependenceAudit

/- TailStable -/
namespace STLTableau.TailDependenceAudit
open Section4.Finiteness

theorem p_iff_one (t : σ.Time) : σ.Satisfies p t ↔ t.val = 1 := by
  change -|t.val-1| ≥ 0 ↔ _
  constructor
  · intro h
    have hz : |t.val-1| = 0 := by linarith [abs_nonneg (t.val-1)]
    linarith [abs_eq_zero.mp hz]
  · rintro h
    simp [h]

theorem future_iff (t : σ.Time) : σ.Satisfies (.eventually J q) t ↔ t.val < 1 := by
  rw [FiniteSignal.satisfies_eventually_iff]
  constructor
  · rintro ⟨u,hu,_⟩
    change 1 ≤ u.val-t.val ∧ u.val-t.val ≤ 2 at hu
    have hτ : u.val < 2 := u.property.2
    linarith [hu.1]
  · intro ht
    let u : σ.Time := ⟨t.val+1,by change 0 ≤ _ ∧ _ < 2; constructor <;> linarith [t.property.1]⟩
    refine ⟨u,?_,?_⟩
    · change 1 ≤ t.val+1-t.val ∧ t.val+1-t.val ≤ 2
      constructor <;> linarith
    · change (0 : ℝ) ≥ 0
      rfl

theorem body_iff (t : σ.Time) : σ.Satisfies body t ↔ t.val ≤ 1 := by
  rw [body,FiniteSignal.satisfies_or,p_iff_one,future_iff]
  constructor
  · rintro (h|h) <;> linarith
  · intro h
    rcases lt_or_eq_of_le h with h|h
    · exact Or.inr h
    · exact Or.inl h

theorem root_iff_zero (t : σ.Time) : σ.Satisfies ψ t ↔ t.val = 0 := by
  constructor
  · intro h
    by_contra he
    have hpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm he)
    have htτ : t.val < 2 := t.property.2
    let v : σ.Time := ⟨max t.val (1+t.val/2),t.property.1.trans (le_max_left _ _),
      max_lt htτ (by change 1+t.val/2 < 2; linarith)⟩
    have hbody := (FiniteSignal.satisfies_always_iff σ I body t).1 h v (by
      change 0 ≤ max t.val (1+t.val/2)-t.val ∧ max t.val (1+t.val/2)-t.val ≤ 1
      have hmax : max t.val (1+t.val/2) ≤ t.val+1 := max_le (by linarith) (by linarith)
      constructor <;> linarith [le_max_left t.val (1+t.val/2)])
    have hn := (body_iff v).1 hbody
    change max t.val (1+t.val/2) ≤ 1 at hn
    linarith [le_max_right t.val (1+t.val/2)]
  · intro ht
    obtain rfl : t = (⟨0,by norm_num [σ]⟩ : σ.Time) := Subtype.ext ht
    exact actual_sat

def bs : Fin 5 → ℝ := ![0,0,1,1,2]
def ms : Fin 5 → Marker := ![●,○,●,○,●]
def stablePart : IntervalPartition σ.domain :=
  IntervalPartition.ofSingletonBoundaries bs
    (by intro i j hij; change i.val ≤ j.val at hij
        fin_cases i <;> fin_cases j <;> norm_num [bs] at *)
    ms (by intro i hi; fin_cases i <;> norm_num [ms,bs] at *) rfl rfl

theorem cell (i : Fin stablePart.size) (u v : σ.Time)
    (hu : u.val ∈ (stablePart.interval i).carrier) (hv : v.val ∈ (stablePart.interval i).carrier) :
    (u.val=0 ↔ v.val=0) ∧ (u.val<1 ↔ v.val<1) ∧ (u.val=1 ↔ v.val=1) := by
  change Fin 4 at i
  change u.val ∈ (IntervalPartition.markedBoundaryPiece bs ms i).carrier at hu
  change v.val ∈ (IntervalPartition.markedBoundaryPiece bs ms i).carrier at hv
  fin_cases i <;> simp [IntervalPartition.markedBoundaryPiece,MarkedInterval.carrier_eq,bs,ms]
    at hu hv <;> grind

private abbrev Agree (u v : σ.Time) (φ : Formula Bool) :=
  σ.Satisfies φ u ↔ σ.Satisfies φ v
private abbrev AllAgree (u v : σ.Time) (φ : Formula Bool) :=
  ∀ χ, Formula.IsSubformula χ φ → Agree u v χ
private theorem all_truth (u v : σ.Time) : AllAgree u v .truth := by
  intro χ h; cases h; rfl
private theorem all_atom (u v : σ.Time) (x : AtomicProposition Bool)
    (hx : Agree u v (.atom x)) : AllAgree u v (.atom x) := by
  intro χ h; cases h; exact hx
private theorem all_neg {u v : σ.Time} {φ : Formula Bool}
    (hφ : AllAgree u v φ) : AllAgree u v (.neg φ) := by
  intro χ h
  cases h with
  | refl => exact not_congr (hφ _ (.refl _))
  | neg h => exact hφ _ h
private theorem all_and {u v : σ.Time} {φ θ : Formula Bool}
    (hφ : AllAgree u v φ) (hθ : AllAgree u v θ) : AllAgree u v (.and φ θ) := by
  intro χ h
  cases h with
  | refl => exact and_congr (hφ _ (.refl _)) (hθ _ (.refl _))
  | and_left h => exact hφ _ h
  | and_right h => exact hθ _ h
private theorem all_until {u v : σ.Time} {φ θ : Formula Bool} {K : TimeInterval}
    (hφ : AllAgree u v φ) (hθ : AllAgree u v θ) (he : Agree u v (.until K φ θ)) :
    AllAgree u v (.until K φ θ) := by
  intro χ h
  cases h with
  | refl => exact he
  | until_left h => exact hφ _ h
  | until_right h => exact hθ _ h

theorem stable : σ.StablePartition ψ stablePart := by
  intro i χ hχ u v hu hv
  obtain ⟨hz,hl,ho⟩ := cell i u v hu hv
  have ap : AllAgree u v p := all_atom u v _ ((p_iff_one u).trans (ho.trans (p_iff_one v).symm))
  have aq : AllAgree u v q := all_atom u v _ Iff.rfl
  have af : AllAgree u v (.eventually J q) :=
    all_until (all_truth u v) aq ((future_iff u).trans (hl.trans (future_iff v).symm))
  have ab : AllAgree u v body := all_neg (all_and (all_neg ap) (all_neg af))
  have hr := (root_iff_zero u).trans (hz.trans (root_iff_zero v).symm)
  have hsub : Agree u v (.eventually I (.neg body)) := by
    change (¬ σ.Satisfies (.eventually I (.neg body)) u ↔
      ¬ σ.Satisfies (.eventually I (.neg body)) v) at hr
    change σ.Satisfies (.eventually I (.neg body)) u ↔ σ.Satisfies (.eventually I (.neg body)) v
    tauto
  exact all_neg (all_until (all_truth u v) (all_neg ab) hsub) χ hχ

def tailInput : Formula.NormalizedInput Bool :=
  ⟨ψ,.always _ (.or (.atom _) (.eventually _ (.atom _)))⟩
theorem original_recognizes :
    (inputTableau (Clock := Nat) (Set.univ : Set Bool) tailInput).recognizes
      JudgementTableau.labels_finite σ stablePart :=
  (inputTableau_recognizes_iff _ tailInput σ stablePart stable).2 actual_sat

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``stable,``original_recognizes] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"

end STLTableau.TailDependenceAudit

/- TerminalObligationAudit -/
namespace STLTableau.Section4.Finiteness.TerminalObligationAudit
open Section3

def I : BoundedTimeInterval := ⟨0,1,by norm_num,by norm_num⟩
def J : BoundedTimeInterval := ⟨1,2,by norm_num,by norm_num⟩
variable {Var Clock : Type*}
def body (a b : AtomicProposition Var) := Formula.or (.atom a) (.eventually J (.atom b))
def root (a b : AtomicProposition Var) := Formula.always I (body a b)

local macro "inventory" : tactic => `(tactic| classical
  simp [Finiteness.rootTemporalSignatures,
    Finiteness.RootTemporalInventory.rootAlwaysSignatures,
    Finiteness.RootTemporalInventory.rootEventualSignatures,
    Finiteness.RootTemporalInventory.literalAlwaysAtRoot,
    Finiteness.RootTemporalInventory.literalEventualAtRoot,
    Finiteness.rootPlainFormulas,root,body,Formula.always,Formula.eventually,Formula.or,
    Formula.release,Formula.untimedUntil])

theorem only_always (a b : AtomicProposition Var) (K : TimeInterval) (φ : Formula Var)
    (h : (TemporalKind.always,K,φ) ∈ Finiteness.rootTemporalSignatures (root a b)) :
    K = I ∧ φ = body a b := by
  simpa [Finiteness.rootTemporalSignatures,
    Finiteness.RootTemporalInventory.rootAlwaysSignatures,
    Finiteness.RootTemporalInventory.rootEventualSignatures,
    Finiteness.RootTemporalInventory.literalAlwaysAtRoot,
    Finiteness.RootTemporalInventory.literalEventualAtRoot,
    root,body,Formula.always,Formula.eventually,Formula.or] using h

theorem no_unbounded_release (a b : AtomicProposition Var) (φ ψ : Formula Var) :
    Formula.release (.unbounded 0) φ ψ ∉ Finiteness.rootPlainFormulas (root a b) := by
  inventory

theorem no_unbounded_always (a b : AtomicProposition Var) (x : NNReal) (φ : Formula Var) :
    (TemporalKind.always,TimeInterval.unbounded x,φ) ∉ Finiteness.rootTemporalSignatures (root a b) :=
  fun h => TimeInterval.noConfusion (only_always a b _ _ h).1

theorem no_unbounded_signature (a b : AtomicProposition Var) (k : TemporalKind) (x : NNReal)
    (φ : Formula Var) :
    (k,TimeInterval.unbounded x,φ) ∉ Finiteness.rootTemporalSignatures (root a b) := by
  cases k <;> inventory

def StarHere : MixedJ Clock Var → Prop
  | .terminal => True
  | .conj J K => StarHere J ∨ StarHere K
  | .reset _ J => StarHere J
  | _ => False
def StarNext : MixedJ Clock Var → Prop
  | .next K => StarHere K
  | .conj J K => StarNext J ∨ StarNext K
  | .reset _ J => StarNext J
  | _ => False
def WaitHere : MixedJ Clock Var → Prop
  | .clock _ .le a => (a : ℝ) = 0
  | .conj J K => WaitHere J ∨ WaitHere K
  | .reset _ J => WaitHere J
  | _ => False
def WaitNext : MixedJ Clock Var → Prop
  | .next K => WaitHere K
  | .conj J K => WaitNext J ∨ WaitNext K
  | .reset _ J => WaitNext J
  | _ => False

def AllowedFinite (θ : Formula Var) : IntervalPredicate Clock Var → Prop
  | .plain φ => ∀ x y, φ ≠ Formula.release (.unbounded 0) x y
  | .upper _ _ .always I φ | .bounded _ _ _ _ .always I φ => φ = θ ∧ I.lower = 0
  | _ => True

private theorem zero_nnreal (h : (0 : ℝ) ≤ 0) : (⟨0,h⟩ : NNReal) = 0 := rfl

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem finite_star_reason [DecidableEq Clock] {p : IntervalPredicate Clock Var}
    {R : ExpansionRule Clock Var} {B : STLTableau.Judgement Clock Var}
    (hr : STLTableau.ConcreteRule p R) (hB : B ∈ R.branches) (θ : Formula Var)
    (hok : AllowedFinite θ p) (hstar : StarNext (Judgement.ofFinite B)) :
    WaitNext (Judgement.ofFinite B) ∨ .plain θ ∈ (Judgement.ofFinite B).currentPredicates := by
  classical
  open STLTableau.ExpansionRule in
    cases hr <;>
      simp only [plainAnd,plainOr,plainUntil,plainRelease,openEventually,openAlways,
        upperAlways,boundedAlways,upperEventually,boundedEventually,List.mem_cons,
        List.not_mem_nil,or_false,List.mem_append] at hB <;>
      (try split_ifs at hB) <;>
      (try simp only [List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hB) <;>
      rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [upperAlways_defer,upperAlways_check,boundedAlways_defer,boundedAlways_check,
        boundedAlways_finish,upperEventually_defer,upperEventually_check,boundedEventually_defer,
        boundedEventually_check,boundedEventually_finish,STLTableau.Judgement.markedLT_eq_clock,
        STLTableau.Judgement.markedGT_eq_clock,Judgement.ofFinite,Predicate.ofFinite,
        StarHere,StarNext,WaitHere,WaitNext,AllowedFinite,Section3.Judgement.currentPredicates,
        zero_nnreal]
  all_goals first | rfl | assumption | exact hok.1 | exact hok.2 | exact (hok _ _ rfl).elim

theorem star_struct {J K : MixedJ Clock Var} (h : ACIdem J K) :
    StarNext J ↔ StarNext K := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | assoc => exact or_assoc
  | comm => exact or_comm
  | idem => exact or_self_iff
  | conj _ _ ih ik => exact or_congr ih ik
  | reset _ _ ih => exact ih
  | resetDistrib | resetUnused | resetNested => rfl
theorem wait_struct {J K : MixedJ Clock Var} (h : ACIdem J K) :
    WaitNext J ↔ WaitNext K := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | assoc => exact or_assoc
  | comm => exact or_comm
  | idem => exact or_self_iff
  | conj _ _ ih ik => exact or_congr ih ik
  | reset _ _ ih => exact ih
  | resetDistrib | resetUnused | resetNested => rfl

@[simp] theorem wait_boundary (c : Clock) (m : Marker) (Γ : MixedJ Clock Var) :
    WaitNext (withBoundaryGuard c m Γ) ↔ WaitNext Γ := by cases m <;> simp [withBoundaryGuard,WaitNext]
@[simp] theorem star_boundary (c : Clock) (m : Marker) (Γ : MixedJ Clock Var) :
    StarNext (withBoundaryGuard c m Γ) ↔ StarNext Γ := by cases m <;> simp [withBoundaryGuard,StarNext]
@[simp] theorem body_boundary (c : Clock) (m : Marker) (Γ : MixedJ Clock Var) :
    (withBoundaryGuard c m Γ).currentPredicates = Γ.currentPredicates := by
  cases m <;> simp [withBoundaryGuard,Section3.Judgement.currentPredicates]

theorem wait_persists [DecidableEq Clock] {J H A : MixedJ Clock Var} (d : Resolve J H A) :
    WaitNext J → WaitNext H := by
  induction d with
  | leaf => exact id
  | conj _ _ ih ik => exact Or.imp ih ik
  | reset _ _ ih | unusedReset _ _ _ _ _ ih => exact ih
  | structural hs _ ih => exact fun h => ih ((wait_struct hs).mp h)
  | expandSolo => exact False.elim
  | expandCtx _ _ _ _ ih => exact fun h => Or.inr (ih (Or.inr (h.elim False.elim id)))
  | boundaryOptional _ _ _ ih | boundaryRequired _ _ _ ih =>
    simp only [WaitNext,false_or,wait_boundary] at ih ⊢
    exact ih

theorem body_not_timed (a b : AtomicProposition Var) (k : TemporalKind) (I : TimeInterval)
    (ψ : Formula Var) : body a b ≠ timedFormula k I ψ := by
  cases k <;> simp [body,Formula.or,Formula.eventually,Formula.always,timedFormula]

theorem body_persists [DecidableEq Clock] {J H A : MixedJ Clock Var} (d : Resolve J H A)
    (a b : AtomicProposition Var) :
    .plain (body a b) ∈ J.currentPredicates → .plain (body a b) ∈ H.currentPredicates := by
  induction d with
  | leaf => exact id
  | conj _ _ ih ik => exact Or.imp ih ik
  | reset _ _ ih | unusedReset _ _ _ _ _ ih => exact ih
  | structural hs _ ih => exact fun h => ih (hs.currentPredicates_eq ▸ h)
  | expandSolo => exact fun h => Or.inl h
  | expandCtx _ _ _ _ ih =>
    rintro (hp | hg)
    · exact Or.inl hp
    · exact Or.inr (ih (Or.inr hg))
  | boundaryRequired _ _ _ ih | boundaryOptional _ _ _ ih =>
    simp only [Section3.Judgement.currentPredicates,Set.mem_union,Set.mem_singleton_iff,
      Set.mem_empty_iff_false,false_or,body_boundary,reduceCtorEq,Predicate.plain.injEq,
      body_not_timed] at ih ⊢
    exact ih

theorem resolve_star [DecidableEq Clock] {J H A : MixedJ Clock Var} (d : Resolve J H A)
    (a b : AtomicProposition Var)
    (allowed : ∀ p ∈ H.currentPredicates, ∀ B, RawBranch p B → StarNext B →
      WaitNext B ∨ .plain (body a b) ∈ B.currentPredicates) :
    StarNext H → StarNext J ∨ WaitNext H ∨ .plain (body a b) ∈ H.currentPredicates := by
  induction d with
  | leaf => exact fun h => Or.inl h
  | conj _ _ ih ik =>
    intro h
    rcases h with h | h
    · rcases ih (fun p hp => allowed p (Or.inl hp)) h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases ik (fun p hp => allowed p (Or.inr hp)) h with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inr h))
  | reset _ _ ih | unusedReset _ _ _ _ _ ih => exact ih allowed
  | structural hs _ ih =>
    exact fun h => ((ih allowed) h).imp (star_struct hs).mpr id
  | expandSolo hb _ _ child ih =>
    intro h
    rcases ih (fun p hp => allowed p (Or.inr hp)) (h.elim False.elim id) with fromB | hw | hφ
    · rcases allowed _ (Or.inl (Set.mem_singleton _)) _ hb fromB with hw | hφ
      · exact Or.inr (Or.inl (Or.inr (wait_persists child hw)))
      · exact Or.inr (Or.inr (Or.inr (body_persists child a b hφ)))
    · exact Or.inr (Or.inl (Or.inr hw))
    · exact Or.inr (Or.inr (Or.inr hφ))
  | expandCtx hb _ _ child ih =>
    intro h
    rcases ih (fun p hp => allowed p (Or.inr hp)) (h.elim False.elim id) with hs | hw | hφ
    · rcases hs with fromB | fromΓ
      · rcases allowed _ (Or.inl (Set.mem_singleton _)) _ hb fromB with hw | hφ
        · exact Or.inr (Or.inl (Or.inr (wait_persists child (Or.inl hw))))
        · exact Or.inr (Or.inr (Or.inr (body_persists child a b (Or.inl hφ))))
      · exact Or.inl (Or.inr fromΓ)
    · exact Or.inr (Or.inl (Or.inr hw))
    · exact Or.inr (Or.inr (Or.inr hφ))
  | boundaryRequired _ _ _ ih | boundaryOptional _ _ _ ih =>
    simp only [StarNext,false_or,star_boundary] at ih ⊢
    exact ih allowed

def Allowed (θ : Formula Var) : Predicate Clock Var → Prop
  | .plain φ => ∀ x y, φ ≠ Formula.release (.unbounded 0) x y
  | .upper _ _ _ (.unbounded _) _ | .bounded _ _ _ _ _ (.unbounded _) _ => False
  | .upper _ _ .always (.bounded I) ψ | .bounded _ _ _ _ .always (.bounded I) ψ =>
      ψ = θ ∧ I.lower = 0
  | _ => True

theorem raw_star_reason [DecidableEq Clock] (θ : Formula Var) {p : Predicate Clock Var}
    {B : MixedJ Clock Var} (hb : RawBranch p B) (h : Allowed θ p) :
    StarNext B → WaitNext B ∨ .plain θ ∈ B.currentPredicates := by
  cases hb with
  | @finite p R hr B hB =>
    apply finite_star_reason hr hB θ
    cases p with
    | plain => exact h
    | upper _ _ k | bounded _ _ _ _ k => cases k <;> exact h
  | @infinite p Bs hr B hB =>
    cases p with
    | upper | bounded => exact h.elim
  | opening =>
    intro hbad
    simp [UnboundedClocked.opening,Judgement.ofUnbounded,StarNext] at hbad

theorem inventory_allowed [Infinite Clock] (a b : AtomicProposition Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ FiniteInventory.locals (Finiteness.rootPlainFormulas (root a b))
      (rootSlotTriples (Clock:=Clock) (root a b))) : Allowed (body a b) p := by
  classical
  unfold FiniteInventory.locals at hp
  rcases Finset.mem_union.mp hp with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨o,_,ho⟩ := Finset.mem_image.mp h
      cases o <;> cases ho
    · obtain ⟨φ,hφ,eq⟩ := Finset.mem_image.mp h
      obtain rfl := Local.predicate.inj eq
      intro x y he
      subst φ
      exact no_unbounded_release a b x y hφ
  · obtain ⟨⟨slot,tag⟩,_,he⟩ := Finset.mem_image.mp h
    have hsig := slot.1.property
    obtain ⟨⟨⟨k,I,φ⟩,hs⟩,j⟩ := slot
    change (k,I,φ) ∈ Finiteness.rootTemporalSignatures (root a b) at hsig
    cases tag with
    | inl m =>
      simp only [FiniteInventory.slotLocal,rootSlotTriples,Local.predicate.injEq] at he
      subst p
      cases I with
      | unbounded x => exact (no_unbounded_signature a b k x φ hsig).elim
      | bounded I =>
        cases k with
        | eventually => trivial
        | always =>
          obtain ⟨heq,rfl⟩ := only_always a b _ φ hsig
          exact ⟨rfl,TimeInterval.bounded.inj heq ▸ rfl⟩
    | inr e =>
      obtain ⟨r,m,q⟩ := e
      simp only [FiniteInventory.slotLocal,rootSlotTriples,Local.predicate.injEq] at he
      subst p
      cases I with
      | unbounded x => exact (no_unbounded_signature a b k x φ hsig).elim
      | bounded I =>
        cases k with
        | eventually => trivial
        | always =>
          obtain ⟨heq,rfl⟩ := only_always a b _ φ hsig
          exact ⟨rfl,TimeInterval.bounded.inj heq ▸ rfl⟩

def NextHas (f : Section3.StateForm Clock Var → Prop) (N : Option (Section3.StateForm Clock Var)) : Prop :=
  ∃ M, N=some M ∧ f M
def HasWait (N : Section3.StateForm Clock Var) : Prop := ∃ c : Clock, (⟨c,.le,0⟩ : Guard Clock) ∈ N.guards
def HasStar (N : Section3.StateForm Clock Var) : Prop := Local.terminal ∈ N.locals

theorem unionNext_has {f : Section3.StateForm Clock Var → Prop} (N M : Option (Section3.StateForm Clock Var))
    (hh : ∀ A B, f (A.union B) ↔ f A ∨ f B) :
    NextHas f (Section3.TransitionForm.unionNext N M) ↔ NextHas f N ∨ NextHas f M := by
  cases N <;> cases M <;> simp [NextHas,Section3.TransitionForm.unionNext,hh]

theorem safe_star_here {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : StarHere J ↔ HasStar F.current := by
  induction h with
  | terminal | clock | marker | predicate | next =>
    simp [StarHere,HasStar,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.ofLocal,Section3.StateForm.ofGuard,Section3.StateForm.empty]
  | conj _ _ _ ih ik => exact or_congr ih ik
  | reset _ _ _ ih => exact ih

theorem safe_wait_here {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : WaitHere J ↔ HasWait F.current := by
  induction h with
  | clock c r a => cases r <;> simp [WaitHere,HasWait,Section3.TransitionForm.ofState,
      Section3.StateForm.ofGuard]
                   exact eq_comm
  | terminal | marker | predicate | next =>
    simp [WaitHere,HasWait,Section3.TransitionForm.ofState,Section3.TransitionForm.ofNextState,
      Section3.StateForm.ofLocal,Section3.StateForm.empty]
  | conj _ _ _ ih ik => simp [WaitHere,ih,ik,HasWait,Section3.TransitionForm.union,Section3.StateForm.union,
      exists_or]
  | reset _ _ _ ih => exact ih

theorem safe_star_next {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : StarNext J ↔ NextHas HasStar F.nextPart := by
  induction h with
  | terminal | clock | marker | predicate => simp [StarNext,NextHas,Section3.TransitionForm.ofState]
  | next h _ _ => simpa [StarNext,NextHas,Section3.TransitionForm.ofNextState] using safe_star_here h
  | conj h g _ ih ik =>
    change _ ↔ NextHas HasStar (Section3.TransitionForm.unionNext _ _)
    rw [unionNext_has _ _ (fun _ _ => Iff.rfl)]
    exact or_congr ih ik
  | reset _ _ _ ih => exact ih

theorem safe_wait_next {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) : WaitNext J ↔ NextHas HasWait F.nextPart := by
  induction h with
  | terminal | clock | marker | predicate => simp [WaitNext,NextHas,Section3.TransitionForm.ofState]
  | next h _ _ => simpa [WaitNext,NextHas,Section3.TransitionForm.ofNextState] using safe_wait_here h
  | conj h g _ ih ik =>
    change _ ↔ NextHas HasWait (Section3.TransitionForm.unionNext _ _)
    rw [unionNext_has _ _ (fun _ _ => by simp [HasWait,Section3.StateForm.union,exists_or])]
    exact or_congr ih ik
  | reset _ _ _ ih => exact ih

theorem resolved_star_origin [DecidableEq Clock] {N N' : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} {J H A : MixedJ Clock Var} (d : Resolve J H A)
    (hi : SafeNormalization J (.ofState N)) (hf : SafeNormalization H F)
    (a b : AtomicProposition Var)
    (allowed : ∀ p, Local.predicate p ∈ F.current.locals → Allowed (body a b) p)
    (hn : F.nextPart = some N') (ht : Local.terminal ∈ N'.locals) :
    HasWait N' ∨ Local.predicate (.plain (body a b)) ∈ F.current.locals := by
  have hs := (safe_star_next hf).mpr ⟨N',hn,ht⟩
  obtain h | hw | hp := resolve_star d a b (fun p hp =>
    fun _ hB => raw_star_reason _ hB (allowed p ((hf.current_predicate_mem p).2 hp))) hs
  · obtain ⟨M,he,_⟩ := (safe_star_next hi).mp h
    cases he
  · obtain ⟨M,he,hM⟩ := (safe_wait_next hf).mp hw
    obtain rfl := Option.some.inj (he.symm.trans hn)
    exact Or.inl hM
  · exact Or.inr ((hf.current_predicate_mem _).2 hp)

theorem rename_star (S : Section3.StateForm Clock Var) (e : Equiv.Perm Clock) :
    HasStar (S.rename e) ↔ HasStar S := by
  change Local.terminal ∈ Local.rename e '' S.locals ↔ _
  constructor
  · rintro ⟨l,hl,he⟩
    cases l <;> cases he
    exact hl
  · exact fun h => ⟨_,h,rfl⟩
theorem rename_wait (S : Section3.StateForm Clock Var) (e : Equiv.Perm Clock) :
    HasWait (S.rename e) ↔ HasWait S := by
  constructor
  · rintro ⟨c,g,hg,he⟩
    rcases g with ⟨c',r,v⟩
    cases he
    exact ⟨_,hg⟩
  · rintro ⟨c,hc⟩
    exact ⟨e c,_,hc,rfl⟩

theorem rename_plain (S : Section3.StateForm Clock Var) (e : Equiv.Perm Clock) (θ : Formula Var) :
    Local.predicate (.plain θ) ∈ (S.alphaReset e).locals ↔
      Local.predicate (.plain θ) ∈ S.locals := by
  constructor
  · rintro ⟨l,hl,he⟩
    cases l with
    | terminal | marker => cases he
    | predicate p => cases p <;> cases he; exact hl
  · exact fun h => ⟨_,h,rfl⟩

theorem alpha_star {F G : Section3.TransitionForm Clock Var}
    (h : Section3.TransitionForm.AlphaEquivalent F G) :
    NextHas HasStar F.nextPart ↔ NextHas HasStar G.nextPart := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | outer F e hf =>
    cases hn : F.nextPart <;> simp [Section3.TransitionForm.alphaOuter,hn,NextHas,rename_star]
  | next F e hf =>
    cases hn : F.nextPart <;> simp [Section3.TransitionForm.alphaNext,hn,NextHas]
    exact rename_star _ _
theorem alpha_wait {F G : Section3.TransitionForm Clock Var}
    (h : Section3.TransitionForm.AlphaEquivalent F G) :
    NextHas HasWait F.nextPart ↔ NextHas HasWait G.nextPart := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | outer F e hf =>
    cases hn : F.nextPart <;> simp [Section3.TransitionForm.alphaOuter,hn,NextHas,rename_wait]
  | next F e hf =>
    cases hn : F.nextPart <;> simp [Section3.TransitionForm.alphaNext,hn,NextHas]
    rfl
theorem alpha_body {F G : Section3.TransitionForm Clock Var}
    (h : Section3.TransitionForm.AlphaEquivalent F G) (θ : Formula Var) :
    Local.predicate (.plain θ) ∈ F.current.locals ↔ Local.predicate (.plain θ) ∈ G.current.locals := by
  induction h with
  | refl | next => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | outer F e hf => exact rename_plain _ _ _

def ReasonForm (θ : Formula Var) (F : Section3.TransitionForm Clock Var) : Prop :=
  NextHas HasStar F.nextPart → NextHas HasWait F.nextPart ∨ Local.predicate (.plain θ) ∈ F.current.locals

theorem normal_branch_reason [DecidableEq Clock] (θ : Formula Var) {p : Predicate Clock Var}
    {B : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var} (hb : RawBranch p B)
    (hok : Allowed θ p) (hn : Section3.TransitionForm.normalize? B = some F) : ReasonForm θ F := by
  obtain ⟨G,hG,_⟩ := hb.safe_normalization
  have he : G=F := Option.some.inj (hG.normalizes.symm.trans hn)
  subst G
  intro hs
  obtain hw | hp := raw_star_reason θ hb hok ((safe_star_next hG).mpr hs)
  · exact Or.inl ((safe_wait_next hG).mp hw)
  · exact Or.inr ((hG.current_predicate_mem _).2 hp)

theorem mixed_branch_reason [DecidableEq Clock] (θ : Formula Var) {p : Predicate Clock Var}
    {Λ : ClockResetSet Clock} {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteMixed.catalogue.Branch p Λ B) (hok : Allowed θ p) : ReasonForm θ B := by
  rcases hb with hf | hi | ho
  · obtain ⟨p,R,b,F,rfl,hr,hm,hn,rfl⟩ := hf
    exact normal_branch_reason (F := F) θ (.finite hr hm) hok hn
  · obtain ⟨p,Bs,b,F,rfl,hr,hm,hn,rfl⟩ := hi
    exact normal_branch_reason (F := F) θ (.infinite hr hm) hok hn
  · obtain ⟨c,m,k,a,φ,F,rfl,hn,rfl⟩ := ho
    exact normal_branch_reason (F := F) θ (.opening c m k a φ) hok hn

theorem contextual_branch_reason [DecidableEq Clock] (θ : Formula Var) {p : Predicate Clock Var}
    {Λ : ClockResetSet Clock} {B : Section3.TransitionForm Clock Var}
    (hb : ConcreteContextual.catalogue.Branch p Λ B) (hok : Allowed θ p) : ReasonForm θ B := by
  obtain ⟨R,A,hr,ha,rfl⟩ := hb
  intro hs
  rcases mixed_branch_reason θ hr hok ((alpha_star ha).mp hs) with hw | hφ
  · exact Or.inl ((alpha_wait ha).mpr hw)
  · exact Or.inr ((alpha_body ha θ).mpr hφ)

theorem closure_star_origin [DecidableEq Clock] (θ : Formula Var)
    {N N' : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (hc : ConcreteContextual.catalogue.IsClosure (.ofState N) F)
    (allowed : ∀ p, Local.predicate p ∈ F.current.locals → Allowed θ p)
    (hn : F.nextPart = some N') (ht : Local.terminal ∈ N'.locals) :
    HasWait N' ∨ Local.predicate (.plain θ) ∈ F.current.locals := by
  classical
  by_contra hbad
  push Not at hbad
  let M : Section3.StateForm Clock Var :=
    { N' with locals := {l ∈ N'.locals | l ≠ Local.terminal}
              locals_finite := N'.locals_finite.subset (fun _ hl => hl.1) }
  let V : Section3.TransitionForm Clock Var := {F with nextPart := some M}
  have hNV : Section3.SyntacticallySubsumed (.ofState N) V :=
    ⟨hc.extension.current,hc.extension.outerFresh,fun _ h => by cases h⟩
  have hVF : Section3.SyntacticallySubsumed V F := by
    refine ⟨(Section3.SyntacticallySubsumed.refl F).current,?_,?_⟩
    · exact Set.disjoint_left.mpr (fun _ hr hv => hv.2 hr)
    · intro K hK
      obtain rfl := Option.some.inj hK
      exact ⟨N',hn,⟨fun _ h => h, fun _ _ h => h,fun _ h => h.1⟩,
        Set.disjoint_left.mpr (fun _ hr hv => hv.2 hr)⟩
  have hclosed : ConcreteContextual.catalogue.IsClosed V := by
    intro p hp
    rcases hc.closed p hp with hna | ⟨C,hC,hsub⟩
    · exact Or.inl hna
    · refine Or.inr ⟨C,hC,⟨hsub.current,hsub.outerFresh,?_⟩⟩
      intro K hK
      obtain ⟨L,hL,hKL,hdis⟩ := hsub.next K hK
      obtain rfl := Option.some.inj (hL.symm.trans hn)
      refine ⟨M,rfl,⟨hKL.guards,hKL.resets,?_⟩,hdis⟩
      intro l hl
      refine ⟨hKL.locals hl,?_⟩
      intro eq
      subst l
      rcases contextual_branch_reason θ hC (allowed p hp) ⟨K,hK,hl⟩ with hw | hpθ
      · obtain ⟨L,hL,c,hcg⟩ := hw
        obtain rfl := Option.some.inj (hL.symm.trans hK)
        exact hbad.1 ⟨c,hKL.guards hcg⟩
      · exact hbad.2 (hsub.current.locals hpθ)
  obtain ⟨K,hK,inc,_⟩ := (hc.minimal V hNV hclosed hVF).next N' hn
  obtain rfl := Option.some.inj hK
  exact (inc.locals ht).2 rfl

theorem derives_star_origin [DecidableEq Clock] {N N' : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (hd : Derives N F) (a b : AtomicProposition Var)
    (allowed : ∀ p, Local.predicate p ∈ F.current.locals → Allowed (body a b) p)
    (hn : F.nextPart = some N') (ht : Local.terminal ∈ N'.locals) :
    HasWait N' ∨ Local.predicate (.plain (body a b)) ∈ F.current.locals := by
  cases hd with
  | original hc _ => exact closure_star_origin _ hc allowed hn ht
  | resolved d hi hf _ => exact resolved_star_origin d hi hf a b allowed hn ht

theorem currentGuard_boundary {c : Clock} {m : Marker} {Γ : MixedJ Clock Var} :
    currentGuards Γ ⊆ currentGuards (withBoundaryGuard c m Γ) := by
  cases m with
  | closed => exact Set.Subset.rfl
  | «open» => exact Set.subset_union_right

theorem resolve_current_guards [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (d : Resolve J H A) : currentGuards J ⊆ currentGuards H := by
  induction d with
  | leaf => exact Set.Subset.rfl
  | conj _ _ ih ik => exact Set.union_subset_union ih ik
  | reset _ _ ih | unusedReset _ _ _ _ _ ih => exact ih
  | structural hs _ ih => exact hs.currentGuards_eq ▸ ih
  | expandSolo => exact Set.empty_subset _
  | expandCtx _ _ _ _ ih =>
    exact fun g hg => Or.inr (ih (Or.inr (hg.elim False.elim id)))
  | boundaryRequired _ _ _ ih | boundaryOptional _ _ _ ih =>
    simp only [currentGuards,Set.empty_union,Set.union_empty] at ih ⊢
    exact currentGuard_boundary.trans ih

theorem derives_guards [DecidableEq Clock] {N : Section3.StateForm Clock Var}
    {F : Section3.TransitionForm Clock Var} (hd : Derives N F) :
    N.guards ⊆ F.current.guards := by
  cases hd with
  | original hc _ => exact hc.extension.current.guards
  | resolved d hi hf _ =>
    change (Section3.TransitionForm.ofState N).current.guards ⊆ F.current.guards
    rw [hi.currentGuards_eq,hf.currentGuards_eq]
    exact resolve_current_guards d

theorem terminal_edge_reason [DecidableEq Clock] [Infinite Clock] (a b : AtomicProposition Var)
    (X : Set Var) (input : Formula.NormalizedInput Var) (hroot : input.val = root a b)
    {F G : Section3.TransitionForm Clock Var} {l : EdgeLabel Clock}
    (he : (F,l,G) ∈ (localClosureGraph X input).edges)
    (ht : Local.terminal ∈ (localClosureGraph X input).label G) :
    l = JudgementTableau.incoming G ∧
    (HasWait G.current ∨ Local.predicate (.plain (body a b)) ∈ F.current.locals) := by
  obtain ⟨φ,hφ⟩ := input
  change φ = root a b at hroot
  subst φ
  let input : Formula.NormalizedInput Var := ⟨root a b,hφ⟩
  obtain ⟨N,hn,hG,hterm,_⟩ := terminal_entry_generator X input he ht
  rcases he.1 with old | added
  · obtain ⟨⟨_,hF⟩,_,M,hM,hd,hl⟩ := old.1
    refine ⟨hl,?_⟩
    have hInv := old.2.1.2.1.1
    rcases derives_star_origin hF a b (fun p hp =>
      inventory_allowed a b p (hInv hp)) hn hterm with hw | hb
    · rcases hw with ⟨c,hc⟩
      exact Or.inl ⟨c,derives_guards hG hc⟩
    · exact Or.inr hb
  · have hE : G = emptyMode := added.2.2.2
    subst G
    change Local.terminal ∈ (withEmptyContinuation X input).label (emptyMode : Section3.TransitionForm Clock Var) at ht
    rw [empty_label] at ht
    exact ht.elim

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for ax in ← Lean.collectAxioms ``terminal_edge_reason do
    unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.Section4.Finiteness.TerminalObligationAudit

/- TerminalPulseSemantics -/
namespace STLTableau.Section4.Finiteness.PulseTerminal
open Section3
variable {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
variable (X : Set Var) (root : Formula.NormalizedInput Var)
local notation "T" => (inputTableau (Clock := Clock) X root)
local notation "U" => (localClosureGraph (Clock := Clock) X root)
local notation "Tr" => Section3.TransitionForm Clock Var
local notation "labs" => (JudgementTableau.labels (Clock := Clock) (Var := Var))
local notation "hfin" => (JudgementTableau.labels_finite (Clock := Clock) (Var := Var))

private theorem empty_dead {l : EdgeLabel Clock} {s : Tr} (he : (emptyMode,l,s) ∈ (U).edges) : False := by
  rcases he.1 with old | added
  · obtain ⟨_,_,_,hn,_,_⟩ := old.1
    cases hn
  · exact added.2.1 rfl

private theorem no_valid_from_empty {p : Path Clock Tr} (hv : p.valid U)
    (hf : p.firstState = emptyMode) : p.lastState = emptyMode := by
  cases p with
  | last => exact hf
  | step l s p =>
    change s = emptyMode at hf
    subst s
    exact (empty_dead X root hv.2.2).elim

private theorem valid_old_of_last_not_empty (p : Path Clock Tr) (hv : p.valid U)
    (hq : p.firstState ∈ (T).states) (hlast : p.lastState ≠ emptyMode) : p.valid T := by
  induction p with
  | last => exact hq
  | step l s p ih =>
    rcases hv.2.2.1 with old | added
    · exact ⟨hq,ih hv.2.1 old.2.2 hlast,old⟩
    · exact (hlast (no_valid_from_empty X root (p := p) hv.2.1 added.2.2.2)).elim

theorem same_path_old_of_terminal (p : Path Clock Tr) (hr : p.run U) (ha : p.accepting U)
    (ht : Local.terminal ∈ (U).label p.lastState) : p.run T ∧ p.accepting T := by
  have hn : p.lastState ≠ emptyMode := by
    intro h
    change Local.terminal ∈ (withEmptyContinuation (Clock := Clock) X root).label p.lastState at ht
    rw [h,empty_label] at ht
    exact ht.elim
  have hv := valid_old_of_last_not_empty X root p hr.1 hr.2.1.2 hn
  exact ⟨⟨hv,hr.2.1⟩,hv,ha.2.1.resolve_left hn⟩

theorem fullTrace_of_terminal_run (p : Path Clock Tr) (hr : p.run U) (ha : p.accepting U)
    (ht : Local.terminal ∈ (U).label p.lastState) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (hs : (p.trace labs hfin).holds σ P α ⟨0,by omega⟩) :
    (JudgementTableau.fullTrace p).holds σ P α ⟨0,by omega⟩ := by
  obtain ⟨hr',ha'⟩ := same_path_old_of_terminal X root p hr ha ht
  have hrun := ((Subgraph.run_iff _ _ p).mp hr').1
  have hacc := ((Subgraph.accepting_iff _ _ p).mp ha').1
  have hi : (Section3.StateForm.ofLocal (.predicate (.plain root.val))).EvaluatedNumeric
      σ P α ⟨0,by omega⟩ := by
    intro l hl
    have he : l = .predicate (.plain root.val) := hl
    subst l
    intro hk
    trivial
  exact (JudgementTableau.fullTrace_and_root_of_accepting_run Derives derives_localLaws
    _ _ _ p hrun hacc σ P α ⟨0,by omega⟩ hi hs).1

/- The last pair of a path, with its incoming label exposed. -/
inductive LastPair {C V : Type*} (F G : Section3.TransitionForm C V)
    (incomingG : EdgeLabel C) : Path C (Section3.TransitionForm C V) → Prop where
  | here l : LastPair F G incomingG (.step l F (.last incomingG G))
  | there {p} l s (hp : LastPair F G incomingG p) : LastPair F G incomingG (.step l s p)

omit [DecidableEq Clock] [Infinite Clock] in
theorem terminal_pair_no_fullTrace (θ : Formula Var) (σ : FiniteSignal Var)
    (hhor : σ.horizon = 2) (hθ : ∀ t : σ.Time, 1 < t.val → ¬ σ.Satisfies θ t)
    (P : IntervalPartition σ.domain) {F G : Tr} {l : EdgeLabel Clock} {p : Path Clock Tr}
    (hp : LastPair F G l p) (ht : Local.terminal ∈ G.current.locals)
    (reason : (∃ c, (⟨c,.le,0⟩ : Guard Clock) ∈ l.guards) ∨
      Local.predicate (.plain θ) ∈ F.current.locals)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    ¬ (JudgementTableau.fullTrace p).holds σ P α k := by
  induction hp generalizing α k with
  | here lF =>
    intro h
    change _ ∧ (if hk : k.val < P.size then _ else False) at h
    by_cases hk : k.val < P.size
    · simp only [dif_pos hk] at h
      let i : Fin P.size := ⟨k.val,hk⟩
      have last : i.val+1 = P.size := h.2.2 .terminal ht
      obtain ⟨x,hx⟩ := P.nonempty i
      have hxD : x ∈ σ.domain := by
        rw [← P.covers]
        exact Set.mem_iUnion.mpr ⟨i,hx⟩
      let t : σ.Time := ⟨(max 1 x + 2)/2,by
        have hu : max (1:ℝ) x < 2 := max_lt (by norm_num) (hxD.2.trans_eq hhor)
        constructor
        · linarith [le_max_left (1:ℝ) x]
        · rw [hhor]; linarith⟩
      have hxt : x < t.val := by
        have hu : max (1:ℝ) x < 2 := max_lt (by norm_num) (hxD.2.trans_eq hhor)
        change x < (max 1 x+2)/2
        linarith [le_max_right (1:ℝ) x]
      have ht1 : 1 < t.val := by
        change _ < (max 1 x+2)/2
        linarith [le_max_left (1:ℝ) x]
      have hmem := P.mem_last_of_le i last hx t.property hxt.le
      rcases reason with ⟨c,hc⟩ | hφ
      · have hg := h.2.1 _ hc
        change lF.resets.apply α c + STLTableau.Judgement.duration P i ≤ (0 : NNReal) at hg
        have hpos : 0 < (STLTableau.Judgement.duration P i : ℝ) := by
          change 0 < (P.interval i).right - (P.interval i).left
          linarith [MarkedInterval.left_le_of_mem hx, MarkedInterval.le_right_of_mem hmem]
        -- The actual pre-next reset map is lF.resets, not necessarily F.current.resets.
        exact False.elim ((not_le_of_gt (show 0 < (lF.resets.apply α c : NNReal) +
          STLTableau.Judgement.duration P i from add_pos_of_nonneg_of_pos zero_le
            (by exact_mod_cast hpos))) hg)
      · have hv := h.1.2 (.predicate (.plain θ)) hφ
        simp only [Local.holds,Local.toJudgement,Section3.Judgement.holds,dif_pos hk,
          Predicate.holds,STLTableau.predicateSatisfies] at hv
        exact hθ t ht1 (hv t hmem)
    · simpa only [dif_neg hk] using h.2
  | there lF s hpair ih =>
    intro h
    change _ ∧ (if hk : k.val < P.size then _ else False) at h
    by_cases hk : k.val < P.size
    · simp only [dif_pos hk] at h
      exact ih _ _ h.2
    · simpa only [dif_neg hk] using h.2

private theorem pair_of_step (l : EdgeLabel Clock) (s : Tr) (p : Path Clock Tr)
    (hv : (Path.step l s p).valid U) (ht : Local.terminal ∈ (U).label p.lastState) :
    ∃ F G d, LastPair F G d (.step l s p) ∧ (F,d,G) ∈ (U).edges ∧
      Local.terminal ∈ (U).label G := by
  induction p generalizing l s with
  | last d G =>
    exact ⟨s,G,d,.here l,hv.2.2,ht⟩
  | step d G p ih =>
    obtain ⟨A,B,l',hp,he,hh⟩ := ih d G hv.2.1 ht
    exact ⟨A,B,l',.there l s hp,he,hh⟩

theorem no_terminal_run (a b : AtomicProposition Var)
    (hroot : root.val = TerminalObligationAudit.root a b)
    (ρ : FiniteSignal Var) (hhor : ρ.horizon = 2)
    (hθ : ∀ t : ρ.Time, 1 < t.val → ¬ρ.Satisfies (TerminalObligationAudit.body a b) t)
    (p : Path Clock Tr) (hr : p.run U) (ha : p.accepting U)
    (ht : Local.terminal ∈ (U).label p.lastState) (P : IntervalPartition ρ.domain)
    (α : ClockValuation Clock) :
    ¬(p.trace labs hfin).holds ρ P α ⟨0,by omega⟩ := by
  intro hs
  have hfull := fullTrace_of_terminal_run X root p hr ha ht ρ P α hs
  cases p with
  | last l F =>
    exact finiteRootTableau_initial_nonterminal X root.val (l,F) hr.2.1 ht
  | step l F p =>
    obtain ⟨A,B,d,hpair,he,hsB⟩ := pair_of_step X root l F p ha.1 ht
    obtain ⟨hlabel,hreason⟩ := TerminalObligationAudit.terminal_edge_reason a b X root hroot he hsB
    apply terminal_pair_no_fullTrace (TerminalObligationAudit.body a b) ρ hhor hθ P hpair hsB.1 _ α _ hfull
    rcases hreason with hwait | hb
    · exact Or.inl (hlabel ▸ hwait)
    · exact Or.inr hb

theorem no_terminal_execution (a b : AtomicProposition Var)
    (hroot : root.val = TerminalObligationAudit.root a b)
    (ρ : FiniteSignal Var) (hhor : ρ.horizon = 2)
    (hθ : ∀ t : ρ.Time, 1 < t.val → ¬ρ.Satisfies (TerminalObligationAudit.body a b) t)
    (h : (U).TranslationReady) {σ : FiniteSignal (U).TypedVar}
    (e : ((U).typedAutomaton h 2).Execution σ) (proj : (U).TypedProjectsTo σ ρ)
    (goal : e.finalState.val.1 ∈ (U).goalModes) :
    e.finalState.val.1 ∉ (U).terminalModes := by
  intro term
  let i : Fin e.count := ⟨e.count-1,by have := e.nonempty; omega⟩
  have hh : σ.horizon = 2 := proj.1.trans hhor
  obtain ⟨xs,hp⟩ := (U).exists_beforeFlow h 2 e i
  obtain ⟨l,hi,_,_,_,_,_⟩ := e.initial_mem
  have hinit := finiteRootTableau_initial_nonterminal X root.val _ hi.1
  have ho := ((U).ordinary_visits_of_initial h 2 e hh hinit hp).2
  have lastOrd : (e.finish i).val.1 ∉ (U).terminalModes := (e.continuousStep i).1 ▸ ho
  have tail : Relation.TransGen ((U).typedAutomaton h 2).DiscreteStep (e.finish i) e.finalState := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp e.finalSteps with he | he
    · exact (lastOrd (he ▸ term)).elim
    · exact he
  have jump : ((U).typedAutomaton h 2).DiscreteStep (e.finish i) e.finalState := by
    rcases (U).typed_boundary_block h 2 tail with hj | ⟨s,hin,_,hout⟩
    · exact hj
    · have hend := (U).typed_terminal_cut h 2 e hh hout term
      have htime := ((U).typed_jump_global h 2 hin).symm.trans
        (((U).typed_jump_global h 2 hout).symm.trans (((U).typed_final_time h 2 e).trans hend))
      have hs := (U).typed_horizon_jump_target h 2 hin htime
      obtain ⟨l₁,he,_,_⟩ := (U).typed_edge_clock_reset h 2 hin
      obtain ⟨l₂,he',_,_⟩ := (U).typed_edge_clock_reset h 2 hout
      have heq := (terminal_successor_empty X root he hs he').2
      change Local.terminal ∈ (withEmptyContinuation (Clock := Clock) X root).label
        e.finalState.val.1.val at term
      rw [heq,empty_label] at term
      exact term.elim
  obtain ⟨P,p,_,hr,ha,hlast,htrace⟩ := (U).run_on_terminal_cut h 2 e ρ proj hp jump term
    goal hh hinit hfin (localClosure_closed X root) (localClosure_visits_ready X root h e hp 2)
    (localClosure_terminal_labels X root _ term)
  have hstar : Local.terminal ∈ (U).label p.lastState := hlast ▸ term
  exact no_terminal_run X root a b hroot ρ hhor hθ p hr ha hstar P (fun _ => 0) (htrace _)

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for ax in ← Lean.collectAxioms ``no_terminal_execution do
    unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.Section4.Finiteness.PulseTerminal

/- TailFrozenGoal -/
namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)

/-- Hold signal coordinates and the marker bit fixed; advance all clocks. -/
def goalAdvance (v : T.TypedVar → ℝ) (dt : ℝ) : T.TypedVar → ℝ
  | .inl (.inl x) => v (.inl (.inl x))
  | .inl (.inr x) => v (.inl (.inr x)) + dt
  | .inr false => v (.inr false) + dt
  | .inr true => v (.inr true)

@[simp] theorem goalAdvance_zero (v : T.TypedVar → ℝ) : T.goalAdvance v 0 = v := by
  funext x
  rcases x with (x|x) | b
  · rfl
  · simp [goalAdvance]
  · cases b <;> simp [goalAdvance]

theorem goalAdvance_inv (h : T.TranslationReady) (τ : ℝ)
    (s : (T.typedAutomaton h τ).State) (dt : ℝ)
    (hτ : s.val.2 (.inl T.globalClock) + dt ≤ τ) :
    (s.val.1,T.goalAdvance s.val.2 dt) ∈ (T.typedAutomaton h τ).invariant := by
  refine ⟨s.property.1,fun _ => hτ,?_,s.property.2.2.2⟩
  intro a ha
  obtain ⟨hv,hp⟩ := s.property.2.2.1 a ha
  exact ⟨hv,hp⟩

def goalAdvanceEnd (h : T.TranslationReady) (τ : ℝ)
    (s : (T.typedAutomaton h τ).State) (r : NNReal)
    (hτ : s.val.2 (.inl T.globalClock) + r ≤ τ) : (T.typedAutomaton h τ).State :=
  ⟨(s.val.1,T.goalAdvance s.val.2 r),T.goalAdvance_inv h τ s r hτ⟩

theorem goalAdvance_continuous (h : T.TranslationReady) (τ : ℝ)
    (s : (T.typedAutomaton h τ).State) (r : NNReal)
    (hτ : s.val.2 (.inl T.globalClock) + r ≤ τ) :
    (T.typedAutomaton h τ).ContinuousStep s (T.goalAdvanceEnd h τ s r hτ) r
      (fun dt => T.goalAdvance s.val.2 dt.val) := by
  refine ⟨rfl,T.goalAdvance_zero _,rfl,?_⟩
  intro dt
  refine ⟨⟨fun _ => rfl,rfl,rfl,rfl⟩,?_⟩
  apply T.goalAdvance_inv
  linarith [dt.property.2]

/-- Replace the unobserved suffix, with the final post-jump state supplying
the new flow's initial value at the shared boundary. -/
noncomputable def freezeAug (aug : FiniteSignal T.TypedVar)
    (v : T.TypedVar → ℝ) (entry : ℝ) : FiniteSignal T.TypedVar :=
  ⟨aug.horizon,aug.horizon_pos,fun t =>
    if t.val < entry then aug.value t else T.goalAdvance v (t.val-entry)⟩

theorem freezeAug_before (aug : FiniteSignal T.TypedVar) (v : T.TypedVar → ℝ)
    (entry : ℝ) (t : aug.Time) (ht : t.val < entry) :
    (T.freezeAug aug v entry).value t = aug.value t := by simp [freezeAug,ht]

theorem freezeAug_after (aug : FiniteSignal T.TypedVar) (v : T.TypedVar → ℝ)
    (entry : ℝ) (t : aug.Time) (ht : entry ≤ t.val) :
    (T.freezeAug aug v entry).value t = T.goalAdvance v (t.val-entry) := by
  simp [freezeAug,not_lt.mpr ht]

end STLTableau.Section4.Tableau

namespace STLTableau.TailDependenceAudit
open Section4

noncomputable def frozen (T S : ℝ) : FiniteSignal Bool :=
  ⟨2,by norm_num,fun t b => if b then -(max 0 (t.val-S)) else -|min t.val T-1|⟩

theorem frozen_before {T S : ℝ} (hTS : T ≤ S) (t : σ.Time) (ht : t.val ≤ T) :
    (frozen T S).value t = σ.value t := by
  funext x
  cases x
  · change -|min t.val T-1| = -|t.val-1|
    rw [min_eq_left ht]
  · change -max 0 (t.val-S) = 0
    rw [max_eq_left (by linarith),neg_zero]

theorem frozen_middle {T S : ℝ} (t u : σ.Time) (hu : u.val = T)
    (hlt : T ≤ t.val) (hut : t.val ≤ S) : (frozen T S).value t = σ.value u := by
  funext x
  cases x
  · change -|min t.val T-1| = -|u.val-1|
    rw [min_eq_right hlt,hu]
  · change -max 0 (t.val-S) = 0
    rw [max_eq_left (by linarith),neg_zero]

theorem frozen_false {T S : ℝ} (_hT : 0 < T) (hTS : T < S)
    (hS : S < 2) (hST : S < 2*T) : ¬ (frozen T S).Satisfies ψ ⟨0,by norm_num [frozen]⟩ := by
  intro hr
  let t : (frozen T S).Time := ⟨S/2,by change 0 ≤ _ ∧ _ < 2; constructor <;> linarith⟩
  have ho := (FiniteSignal.satisfies_always_iff (frozen T S) I body _).1 hr t
    (by change 0 ≤ S/2-0 ∧ S/2-0 ≤ 1; constructor <;> linarith)
  rcases (FiniteSignal.satisfies_or (frozen T S) p (.eventually J q) t).1 ho with hp | hf
  · change -|min (S/2) T-1| ≥ 0 at hp
    rw [min_eq_left (by linarith),abs_of_neg (by linarith)] at hp
    linarith
  · obtain ⟨u,hw,hq⟩ := (FiniteSignal.satisfies_eventually_iff (frozen T S) J q t).1 hf
    change 1 ≤ u.val-S/2 ∧ u.val-S/2 ≤ 2 at hw
    change -max 0 (u.val-S) ≥ 0 at hq
    linarith [le_max_right (0 : ℝ) (u.val-S), hw.1]

theorem freezing_length_exists {T : ℝ} (hT : 0 < T) (hτ : T < 2) :
    ∃ S, T < S ∧ S < 2 ∧ S < 2*T := by
  obtain ⟨S, hTS, hlim⟩ := exists_between (lt_min hτ (by linarith : T < 2*T))
  exact ⟨S,hTS,(lt_min_iff.mp hlim).1,(lt_min_iff.mp hlim).2⟩

theorem frozen_proj {Clock State : Type*} (G : Tableau Clock Bool State)
    (h : G.TranslationReady) {aug : FiniteSignal G.TypedVar}
    (e : (G.typedAutomaton h 2).Execution aug)
    (proj : G.TypedProjectsTo aug σ) {T S : ℝ}
    (hend : T = e.boundary ⟨e.count,by omega⟩) (hT : 0 ≤ T) (hTS : T ≤ S) (hS : S < 2) :
    G.TypedProjectsThrough (G.freezeAug aug e.finalState.val.2 T) (frozen T S) S := by
  refine ⟨hS.le,?_⟩
  intro t u he hcut x
  let u' : σ.Time := u
  by_cases ht : t.val < T
  · rw [G.freezeAug_before aug _ T (show aug.Time from t) ht]
    exact (proj.2 t u' he x).trans
      (congrFun (frozen_before hTS u' (by change u.val ≤ T; linarith)) x.val).symm
  · let t0 : aug.Time := ⟨T,hT,by rw [proj.1]; change T < 2; linarith⟩
    let u0 : σ.Time := ⟨T,hT,by change T < 2; linarith⟩
    rw [G.freezeAug_after aug _ T (show aug.Time from t) (le_of_not_gt ht)]
    change e.finalState.val.2 (.inl (.inl x)) = (frozen T S).value u x.val
    rw [← e.final_signal_eq t0 hend]
    exact (proj.2 t0 u0 rfl x).trans
      (congrFun (frozen_middle u' u0 rfl (by change T ≤ u.val; linarith) hcut.le) x.val).symm

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for n in #[``Section4.Tableau.goalAdvance_continuous,``frozen_false,``frozen_proj] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do throwError "{n} uses unexpected axiom {ax}"
end STLTableau.TailDependenceAudit

/- TailNoOrdinaryGoal -/
namespace STLTableau.TailDependenceAudit
open Section4 Finiteness
local notation "G" => localClosureGraph (Clock := Nat) (Set.univ : Set Bool) tailInput

private theorem no_positive_start (hg : (G).TranslationReady) {aug : FiniteSignal (G).TypedVar}
    (e : ((G).typedAutomaton hg 2).Execution aug) (proj : (G).TypedProjectsTo aug σ)
    (i : Fin e.count) : (e.start i).val.1 ∉ (G).goalModes := by
  intro goal
  let L := e.boundary i.castSucc
  let R := e.boundary i.succ
  let cut := (L+R)/2
  have hLR : L < R := e.increasing Fin.castSucc_lt_succ
  have hh : aug.horizon = 2 := proj.1
  have hR : R ≤ 2 := (e.increasing.monotone (Fin.le_last i.succ)).trans
    (e.last_le_horizon.trans_eq hh)
  have hL : 0 ≤ L := (e.start_time_mem_domain i).1
  have hcut : L < cut := by dsimp [cut]; linarith
  have hcut' : cut < R := by dsimp [cut]; linarith
  have hcutτ : cut < 2 := hcut'.trans_le hR
  have hw : (G).TypedProjectsThrough aug (σ' cut) cut := by
    refine ⟨hcutτ.le,?_⟩
    intro t u he hu x
    exact (proj.2 t (show σ.Time from u) he x).trans
      (congrFun (same_through cut (show σ.Time from u) hu.le) x.val).symm
  exact changed_false cut (hL.trans hcut.le) hcutτ
    (early_goal_forces_prefix_truth _ tailInput hg e i hcut hcut'.le goal hh (σ' cut) hw)

/-- For this particular signal, even a goal reached instantaneously by a
nonempty final jump chain must be terminal. No bound on chain length is used. -/
theorem goal_must_be_terminal (hg : (G).TranslationReady) {aug : FiniteSignal (G).TypedVar}
    (e : ((G).typedAutomaton hg 2).Execution aug) (proj : (G).TypedProjectsTo aug σ)
    (goal : e.finalState.val.1 ∈ (G).goalModes) : e.finalState.val.1 ∈ (G).terminalModes := by
  by_contra ord
  let i : Fin e.count := ⟨e.count-1,by have := e.nonempty; omega⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp e.finalSteps with ef | chain
  · have eq : e.finalState = e.finish i := ef
    rw [eq,← (e.continuousStep i).1] at goal
    exact no_positive_start hg e proj i goal
  · let T := e.boundary ⟨e.count,by omega⟩
    have ht : e.finalState.val.2 (.inl (G).globalClock) = T :=
      (G).typed_final_time hg 2 e
    obtain ⟨prev,_,jump⟩ := Relation.TransGen.tail'_iff.mp chain
    obtain ⟨_,_,_,_,_,_,_,_,_,htest,_⟩ := jump
    have hTτ : T < 2 := by
      by_contra! h
      exact ord (htest.mpr (ht ▸ h))
    have hT : 0 < T := by
      rw [← e.first_zero]
      apply e.increasing
      exact e.nonempty
    obtain ⟨S,hTS,hSτ,hST⟩ := freezing_length_exists hT hTτ
    let r : NNReal := ⟨S-T,by linarith⟩
    have hlen : T+(r : ℝ) = S := by change T+(S-T)=S; ring
    have hrpos : 0 < r := by change 0 < S-T; linarith
    have hh : aug.horizon = 2 := proj.1
    have hclock : e.finalState.val.2 (.inl (G).globalClock) + r ≤ 2 := by linarith
    let newAug := (G).freezeAug aug e.finalState.val.2 T
    have hhor : T+(r : ℝ) ≤ newAug.horizon := by
      change T+(r : ℝ) ≤ aug.horizon
      rw [hh,hlen]; exact hSτ.le
    let b := (G).goalAdvanceEnd hg 2 e.finalState r hclock
    let γ := fun dt : Set.Icc (0 : ℝ) r => (G).goalAdvance e.finalState.val.2 dt.val
    have hcont := (G).goalAdvance_continuous hg 2 e.finalState r hclock
    obtain ⟨e',j,hstart,hleft,hright⟩ := e.append_observed_flow newAug T rfl r hrpos hhor b γ
      hcont chain (by
        intro t u he hu
        rw [(G).freezeAug_before aug _ T (show aug.Time from t) hu]
        exact congrArg aug.value (Subtype.ext he)) (by
        intro t hl hr
        exact (G).freezeAug_after aug _ T (show aug.Time from t) hl)
    have eqgoal : (e'.start j).val.1 ∈ (G).goalModes := hstart ▸ goal
    have hlt : e'.boundary j.castSucc < S := hleft ▸ hTS
    have hle : S ≤ e'.boundary j.succ := by rw [hright,hlen]
    have proj' := frozen_proj (G) hg e proj rfl hT.le hTS.le hSτ
    have good := early_goal_forces_prefix_truth _ tailInput hg e' j hlt hle eqgoal hh
      (frozen T S) proj'
    exact frozen_false hT hTS hSτ hST good

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for ax in ← Lean.collectAxioms ``goal_must_be_terminal do
    unless allowed.contains ax do throwError "unexpected axiom {ax}"
end STLTableau.TailDependenceAudit
namespace STLTableau.TailDependenceAudit
open Section4 Finiteness
noncomputable abbrev G := localClosureGraph (Clock := Nat) (Set.univ : Set Bool) tailInput
theorem translationReady : G.TranslationReady :=
  localClosure_ready _ _ (finiteRootTableau_translationReady _ Set.finite_univ _ (by simp))

theorem no_goal_trajectory : ¬ ∃ aug : FiniteSignal G.TypedVar,
    G.TypedProjectsTo aug σ ∧ (G.typedAutomaton translationReady 2).Reaches aug G.goalModes := by
  rintro ⟨aug,proj,e,goal⟩
  have hterm := goal_must_be_terminal translationReady e proj goal
  apply PulseTerminal.no_terminal_execution (Clock := Nat) (Set.univ : Set Bool) tailInput
    (a false) (a true) rfl σ rfl _ translationReady e proj goal hterm
  intro t ht
  exact fun hb => (not_le_of_gt ht) ((body_iff t).mp hb)

theorem forward_translation_counterexample :
    SignalAtomRightContinuous σ ψ ∧ G.recognizes JudgementTableau.labels_finite σ stablePart ∧
      ¬ ∃ aug : FiniteSignal G.TypedVar, G.TypedProjectsTo aug σ ∧
        (G.typedAutomaton translationReady 2).Reaches aug G.goalModes :=
  ⟨wellBehaved_actual,
    (localClosure_recognizes_iff_original (Set.univ : Set Bool) tailInput σ stablePart).2
      original_recognizes,no_goal_trajectory⟩

run_elab do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for ax in ← Lean.collectAxioms ``forward_translation_counterexample do
    unless allowed.contains ax do throwError "unexpected axiom {ax}"

end STLTableau.TailDependenceAudit

namespace STLTableau.TailDependenceAudit
open Section4.Finiteness
/-- For the same recognized signal, goal reachability fails in
`typedAutomaton` and holds in `endPositionAutomaton`. -/
theorem old_fails_new_reaches :
    (¬ ∃ aug : FiniteSignal G.TypedVar, G.TypedProjectsTo aug σ ∧
      (G.typedAutomaton translationReady 2).Reaches aug G.goalModes) ∧
    (∃ aug : FiniteSignal G.TypedVar, G.TypedProjectsTo aug σ ∧
      (G.endPositionAutomaton translationReady 2).Reaches aug G.goalModes) := by
  refine ⟨no_goal_trajectory,?_⟩
  apply endPosition_forward (Set.univ : Set Bool) tailInput translationReady σ wellBehaved_actual
    _ stablePart forward_translation_counterexample.2.1
  intro b hb
  rcases atom_cases hb with rfl | rfl <;> rfl

run_elab do
  for ax in ← Lean.collectAxioms ``old_fails_new_reaches do
    unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
      throwError "unexpected axiom {ax}"
end STLTableau.TailDependenceAudit
