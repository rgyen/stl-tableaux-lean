import STLTableaux.Finiteness.Derivation.BoundaryExtension
import STLTableaux.Closure.Correctness.MixedConcreteClosure
import STLTableaux.Rules.Unbounded.UnboundedCorrectness
import STLTableaux.Semantics.Invariants.NumericInvariant

/-! Finite derivations for resolving judgements in context. The constructors
record syntactic steps. The invariant obligations of their occurrences are
stated separately. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}
abbrev MixedJ := Section3.Judgement

/-- A branch of one of the concrete expansion rules, before normalization. -/
inductive RawBranch [DecidableEq Clock] : Predicate Clock Var → MixedJ Clock Var → Prop
  | finite {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
      (rule : STLTableau.ConcreteRule p R) {B : STLTableau.Judgement Clock Var}
      (member : B ∈ R.branches) : RawBranch (Predicate.ofFinite p) (Judgement.ofFinite B)
  | infinite {p : UnboundedClocked.Predicate Clock Var}
      {Bs : List (UnboundedClocked.Node Clock Var)} (rule : UnboundedClocked.ConcreteRule p Bs)
      {B : UnboundedClocked.Node Clock Var} (member : B ∈ Bs) :
      RawBranch (Predicate.ofUnbounded p) (Judgement.ofUnbounded B)
  | opening (c : Clock) (m : Marker) (kind : TemporalKind) (a : NNReal) (φ : Formula Var) :
      RawBranch (.plain (UnboundedClocked.formula kind a φ))
        (Judgement.ofUnbounded (UnboundedClocked.opening c m kind a φ))

/-- Soundness follows from the expansion-rule soundness theorems. -/
theorem RawBranch.sound [DecidableEq Clock] {p : Predicate Clock Var} {B : MixedJ Clock Var}
    (h : RawBranch p B) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : ∀ hk : k.1 < P.size, p.Invariant σ P α k hk)
    (hs : Judgement.holds σ P α k B) : Judgement.holds σ P α k (.predicate p) := by
  cases h with
  | @finite p₀ R rule B₀ member =>
      apply (Judgement.holds_ofFinite σ P α k (.predicate p₀)).2
      apply STLTableau.rule_sound rule σ P α k
      · intro hk
        cases p₀ <;> exact hi hk
      · exact ⟨_, member, (Judgement.holds_ofFinite σ P α k _).1 hs⟩
  | @infinite p₀ Bs rule B₀ member =>
      apply (Judgement.holds_ofUnbounded σ P α k (.predicate p₀)).2
      apply UnboundedClocked.rule_sound rule σ P α k
      · intro hk
        cases p₀ <;> exact hi hk
      · exact ⟨_, member, (Judgement.holds_ofUnbounded σ P α k _).1 hs⟩
  | opening c m kind a φ =>
      have hp := (UnboundedClocked.opening_correct σ P α k c kind a φ).2
        ⟨m, (Judgement.holds_ofUnbounded σ P α k _).1 hs⟩
      exact (Judgement.holds_ofUnbounded σ P α k _).2 hp

/-- All names, including reset bindings and next guards, for syntactic freshness. -/
def syntaxClocks : MixedJ Clock Var → Set Clock
  | .terminal | .marker _ | .predicate (.plain _) => ∅
  | .clock c _ _ | .predicate (.upper c _ _ _ _) => {c}
  | .predicate (.bounded c d _ _ _ _ _) => {c,d}
  | .conj J K => syntaxClocks J ∪ syntaxClocks K
  | .next J => syntaxClocks J
  | .reset R J => R.clocks ∪ syntaxClocks J

def resetNames : MixedJ Clock Var → Set Clock
  | .reset R J => R.clocks ∪ resetNames J
  | .conj J K => resetNames J ∪ resetNames K
  | .next J => resetNames J
  | _ => ∅

/-- Newly bound names must be fresh against every name in the pending context.
Resets of a source predicate's own clocks are not new introductions. -/
def FreshFor (p : Predicate Clock Var) (B Γ : MixedJ Clock Var) : Prop :=
  Disjoint (resetNames B \ syntaxClocks (.predicate p))
    (syntaxClocks Γ ∪ syntaxClocks (.predicate p))

/-- The same whole-syntax freshness test with an explicitly absent context.
No dummy truth judgement or extra clock represents the empty context. -/
def FreshWithoutContext (p : Predicate Clock Var) (B : MixedJ Clock Var) : Prop :=
  Disjoint (resetNames B \ syntaxClocks (.predicate p)) (syntaxClocks (.predicate p))

/-- Whole-body disjointness makes the reset act identically on free names. -/
theorem reset_apply_agrees_on_free (R : ClockResetSet Clock) (J : MixedJ Clock Var)
    (hd : Disjoint R.clocks J.freeClocks) (α : ClockValuation Clock) :
    ∀ c ∈ J.freeClocks, R.apply α c = α c := by
  intro c hc
  cases hr : R.value c with
  | none => simp only [ClockResetSet.apply,hr]
  | some v => exact False.elim (Set.disjoint_left.1 hd ⟨v,hr⟩ hc)

/-- Least syntactic congruence for associativity, commutativity, and
idempotence of conjunction and the scoped reset laws. `StructuralEq` is an
alias for this relation. -/
inductive ACIdem : MixedJ Clock Var → MixedJ Clock Var → Prop
  | refl (J) : ACIdem J J
  | symm {J K} : ACIdem J K → ACIdem K J
  | trans {J K L} : ACIdem J K → ACIdem K L → ACIdem J L
  | assoc (J K L) : ACIdem (.conj (.conj J K) L) (.conj J (.conj K L))
  | comm (J K) : ACIdem (.conj J K) (.conj K J)
  | idem (J) : ACIdem (.conj J J) J
  | conj {J J' K K'} : ACIdem J J' → ACIdem K K' → ACIdem (.conj J K) (.conj J' K')
  | reset (R) {J K} : ACIdem J K → ACIdem (.reset R J) (.reset R K)
  | resetDistrib (R) (J K) :
      ACIdem (.reset R (.conj J K)) (.conj (.reset R J) (.reset R K))
  | resetUnused (R) (J) : Disjoint R.clocks J.freeClocks → ACIdem (.reset R J) J
  | resetNested (R S) (J) : ACIdem (.reset R (.reset S J)) (.reset (S.union R) J)

abbrev StructuralEq := @ACIdem


theorem ACIdem.holds_iff {J K : MixedJ Clock Var} (h : ACIdem J K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Judgement.holds σ P α k J ↔ Judgement.holds σ P α k K := by
  induction h generalizing α with
  | refl => rfl
  | symm h ih => exact (ih α).symm
  | trans h g ih ig => exact (ih α).trans (ig α)
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr (ih α) (ig α)
  | reset R h ih => exact ih (R.apply α)
  | resetDistrib R J K => rfl
  | resetUnused R J hd =>
      exact Judgement.holds_congr_of_agree (reset_apply_agrees_on_free R J hd α) σ P k
  | resetNested R S J =>
      simp only [Judgement.holds,ClockResetSet.apply_union_eq_comp]

/-- Gather an independently scoped pending requirement under a reset whose
bound values it does not use. This is the cross-parent plain-demand bridge. -/
theorem ACIdem.gather_reset_right (R : ClockResetSet Clock) (J K : MixedJ Clock Var)
    (h : Disjoint R.clocks K.freeClocks) :
    ACIdem (.conj (.reset R J) K) (.reset R (.conj J K)) :=
  .trans (.conj (.refl _) (.symm (.resetUnused R K h))) (.symm (.resetDistrib R J K))

/-- Under actual consistency, the left-biased reset maps agree in either order. -/
theorem reset_union_comm_of_consistent (R S : ClockResetSet Clock) (h : R.Consistent S) :
    R.union S = S.union R := by
  have hext : ∀ T U : ClockResetSet Clock, T.value = U.value → T = U := by
    intro T U hvalue
    cases T
    cases U
    cases hvalue
    rfl
  apply hext
  funext c
  simp only [ClockResetSet.union]
  cases hr : R.value c with
  | none => cases hs : S.value c <;> rfl
  | some v =>
      cases hs : S.value c with
      | none => rfl
      | some w =>
          have he : v = w := h c v w hr hs
          cases he
          rfl

/-- Splitting compatible paired resets retains the requested outer order. -/
theorem ACIdem.split_consistent_resets (R S : ClockResetSet Clock) (J : MixedJ Clock Var)
    (h : R.Consistent S) : ACIdem (.reset (R.union S) J) (.reset R (.reset S J)) := by
  rw [reset_union_comm_of_consistent R S h]
  exact .symm (.resetNested R S J)

/-- Conjunct occurrence never crosses a next or reset boundary. -/
inductive Conjunct : MixedJ Clock Var → MixedJ Clock Var → Prop
  | here (J) : Conjunct J J
  | left {J K L} : Conjunct J L → Conjunct (.conj J K) L
  | right {J K L} : Conjunct K L → Conjunct (.conj J K) L

/-- The exact reset value used by a temporal check branch. -/
def lowerEndpoint : TimeInterval → NNReal
  | .bounded I => ⟨I.lower,I.lower_nonnegative⟩
  | .unbounded a => a

/-- Frozen successors of actual defer or check schemas. Check resets use
precisely the interval lower endpoint and retain the current marker. -/
inductive FrozenOccurrence [DecidableEq Clock] : MixedJ Clock Var → Clock → Clock →
    Marker → Marker → TemporalKind → TimeInterval → Formula Var → Prop
  | defer {N c d m ℓ kind I φ} :
      Conjunct N (.reset (ClockResetSet.singleton d 0)
        (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.marker ℓ))) →
      FrozenOccurrence N c d m ℓ kind I φ
  | check {N c d ℓ kind I φ} :
      Conjunct N (.reset ((ClockResetSet.singleton c (lowerEndpoint I)).union
        (ClockResetSet.singleton d 0))
        (.conj (.predicate (.bounded c d ℓ (¬ₘ ℓ) kind I φ)) (.marker ℓ))) →
      FrozenOccurrence N c d ℓ ℓ kind I φ

/-- A branch for the `↑` form with its next judgement and the reset and
marker occurrence in that judgement. -/
structure FrozenByUpper [DecidableEq Clock] (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) where
  distinct : c ≠ d
  sourceMarker : Marker
  branch : MixedJ Clock Var
  nextBody : MixedJ Clock Var
  actual : RawBranch (.upper c sourceMarker kind I φ) branch
  nextOccurrence : Conjunct branch (.next nextBody)
  frozenOccurrence : FrozenOccurrence nextBody c d m ℓ kind I φ

/-- Concrete frozen-successor certificates exist for each literal defer family.
The certificate contains actual rule membership and exact syntax occurrences. -/
def FrozenByUpper.defer [DecidableEq Clock] (c d : Clock) (m ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (hcd : c ≠ d) :
    FrozenByUpper c d m ℓ kind I φ := by
  cases I with
  | bounded I =>
      cases kind with
      | always =>
          refine ⟨hcd,m,Judgement.ofFinite (ExpansionRule.upperAlways_defer c d m ℓ I φ),
            _,.finite (.upperAlways c d m I φ hcd) ?_,.here _,.defer (.right (.here _))⟩
          cases ℓ <;> simp [ExpansionRule.upperAlways]
      | eventually =>
          refine ⟨hcd,m,Judgement.ofFinite (ExpansionRule.upperEventually_defer c d m ℓ I φ),
            _,.finite (.upperEventually c d m I φ hcd) ?_,.here _,.defer (.right (.here _))⟩
          cases ℓ <;> simp [ExpansionRule.upperEventually]
  | unbounded a =>
      cases kind with
      | always =>
          refine ⟨hcd,m,Judgement.ofUnbounded (UnboundedClocked.upperAlwaysDefer c d m ℓ a φ),
            _,.infinite (.upperAlways c d m a φ hcd) ?_,.here _,.defer (.right (.here _))⟩
          cases ℓ <;> simp [UnboundedClocked.upperAlwaysBranches]
      | eventually =>
          refine ⟨hcd,m,Judgement.ofUnbounded (UnboundedClocked.upperEventuallyDefer c d m ℓ a φ),
            _,.infinite (.upperEventually c d m a φ hcd) ?_,.here _,.defer (.here _)⟩
          cases ℓ <;> simp [UnboundedClocked.upperEventuallyBranches]

/-- Every enabled literal check branch supplies the paired frozen shape.
Eventuality's zero-lower branch is plain rather than a check and is excluded
by the syntactic branch-list side condition, not a semantic premise. -/
def FrozenByUpper.check [DecidableEq Clock] (c d : Clock) (b ℓ : Marker)
    (kind : TemporalKind) (I : TimeInterval) (φ : Formula Var) (hcd : c ≠ d)
    (henabled : kind = .always ∨ lowerEndpoint I ≠ 0) :
    FrozenByUpper c d ℓ ℓ kind I φ := by
  cases I with
  | bounded I =>
      cases kind with
      | always =>
          refine ⟨hcd,b,Judgement.ofFinite (ExpansionRule.upperAlways_check c d b ℓ I φ),
            _,.finite (.upperAlways c d b I φ hcd) ?_,.right (.here _),
            .check (.right (.here _))⟩
          cases ℓ <;> simp [ExpansionRule.upperAlways]
      | eventually =>
          have ha : I.lower ≠ 0 := by
            intro hzero
            have haNN : lowerEndpoint (.bounded I) ≠ 0 := henabled.resolve_left (by decide)
            exact haNN (Subtype.ext hzero)
          refine ⟨hcd,b,Judgement.ofFinite (ExpansionRule.upperEventually_check c d b ℓ I φ),
            _,.finite (.upperEventually c d b I φ hcd) ?_,.right (.here _),
            .check (.right (.here _))⟩
          cases ℓ <;> simp [ExpansionRule.upperEventually,ha]
  | unbounded a =>
      cases kind with
      | always =>
          refine ⟨hcd,b,Judgement.ofUnbounded (UnboundedClocked.upperAlwaysCheck c d b ℓ a φ),
            _,.infinite (.upperAlways c d b a φ hcd) ?_,.right (.here _),
            .check (.right (.here _))⟩
          cases ℓ <;> simp [UnboundedClocked.upperAlwaysBranches]
      | eventually =>
          have ha : a ≠ 0 := henabled.resolve_left (by decide)
          refine ⟨hcd,b,Judgement.ofUnbounded (UnboundedClocked.upperEventuallyCheck c d b ℓ a φ),
            _,.infinite (.upperEventually c d b a φ hcd) ?_,.right (.here _),
            .check (.right (.here _))⟩
          cases ℓ <;> simp [UnboundedClocked.upperEventuallyBranches,ha]

/-- Only atomic current requirements or a literal next requirement may stop. -/
inductive ResolutionLeaf : MixedJ Clock Var → Prop
  | terminal : ResolutionLeaf .terminal
  | clock (c r a) : ResolutionLeaf (.clock c r a)
  | marker (m) : ResolutionLeaf (.marker m)
  | atomic (p) : p.IsAtomic → ResolutionLeaf (.predicate p)
  | next (N) : ResolutionLeaf (.next N)

/-- Add only the strict zero comparison; the closed case is automatic for
nonnegative clock values and needs no guard or new truth syntax. -/
def withBoundaryGuard (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) : MixedJ Clock Var :=
  match b with
  | .closed => Γ
  | .open => .conj (.clock c .gt 0) Γ

theorem withBoundaryGuard_holds (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    Judgement.holds σ P α k (withBoundaryGuard c b Γ) ↔
      (0 : ℝ) <[b] (α c : ℝ) ∧ Judgement.holds σ P α k Γ := by
  cases b with
  | «open» => simp [withBoundaryGuard, Judgement.holds, ClockRelation.Holds]
  | closed =>
      simp only [withBoundaryGuard, markedLT_closed]
      exact (and_iff_right (α c).coe_nonneg).symm

/-- A finite declarative proof tree. The last two indices are the full output
and its atomic/next leaves. Expansion retains its source only after the child
resolves the selected branch together with the entire other pending context.
There is deliberately no reflexive non-atomic leaf. -/
inductive Resolve [DecidableEq Clock] :
    MixedJ Clock Var → MixedJ Clock Var → MixedJ Clock Var → Type _
  | leaf {J} : ResolutionLeaf J → Resolve J J J
  | conj {J K H G A B} : Resolve J H A → Resolve K G B →
      Resolve (.conj J K) (.conj H G) (.conj A B)
  | reset (R) {J H A} : Resolve J H A → Resolve (.reset R J) (.reset R H) (.reset R A)
  | structural {J K H A} : ACIdem J K → Resolve K H A → Resolve J H A
  | expandCtx {p B Γ H A} : RawBranch p B → (¬ p.IsAtomic) → FreshFor p B Γ →
      Resolve (.conj B Γ) H A → Resolve (.conj (.predicate p) Γ) (.conj (.predicate p) H) A
  | expandSolo {p B H A} : RawBranch p B → (¬ p.IsAtomic) → FreshWithoutContext p B →
      Resolve B H A → Resolve (.predicate p) (.conj (.predicate p) H) A
  | boundaryRequired {c d m ℓ kind I φ Γ H A} : FrozenByUpper c d m ℓ kind I φ →
      (d ∉ Γ.freeClocks) →
      Resolve (.conj (.predicate (.upper c m kind I φ))
        (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A →
      Resolve (.reset (ClockResetSet.singleton d 0)
        (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
          (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))) H A
  | boundaryOptional {c d m ℓ kind I φ Γ H A} : FrozenByUpper c d m ℓ kind I φ →
      (d ∉ Γ.freeClocks) →
      Resolve (.conj (.predicate (.upper c m kind I φ))
        (.conj (.marker ℓ) (withBoundaryGuard c (Marker.imp ℓ m) Γ))) H A →
      Resolve (.reset (ClockResetSet.singleton d 0)
        (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ)) (.conj (.marker ℓ) Γ))) H A
  | unusedReset {J H A} (d : Clock) (v : NNReal) : (d ∉ J.freeClocks) →
      (d ∉ H.freeClocks) → Resolve J H A → Resolve (.reset (ClockResetSet.singleton d v) J) H A

/-- A concrete singleton non-atomic root is resolvable without a fake empty
context: select the actual conjunction branch and stop at its atomic operands. -/
def Resolve.atomic_plainAnd [DecidableEq Clock] (φ ψ : Formula Var)
    (hφ : (Predicate.plain φ : Predicate Clock Var).IsAtomic)
    (hψ : (Predicate.plain ψ : Predicate Clock Var).IsAtomic) :
    Resolve (Clock := Clock) (.predicate (.plain (.and φ ψ)))
      (.conj (.predicate (.plain (.and φ ψ)))
        (.conj (.predicate (.plain φ)) (.predicate (.plain ψ))))
      (.conj (.predicate (.plain φ)) (.predicate (.plain ψ))) := by
  refine .expandSolo (.finite (.plainAnd φ ψ)
    (B := .conj (.predicate (.plain φ)) (.predicate (.plain ψ))) ?_) ?_ ?_
    (.conj (.leaf (.atomic _ hφ)) (.leaf (.atomic _ hψ)))
  · simp [ExpansionRule.plainAnd]
  · simp [Predicate.IsAtomic]
  · simp [FreshWithoutContext,resetNames,Judgement.ofFinite]

/-- Evaluated rule occurrences belong in theorem
hypotheses, never in signal-independent resolution constructors. -/
def Resolve.Evaluated [DecidableEq Clock] {J H A : MixedJ Clock Var} (D : Resolve J H A)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop :=
  match D with
  | .leaf _ => True
  | .conj D E => D.Evaluated σ P α k ∧ E.Evaluated σ P α k
  | .reset R D => D.Evaluated σ P (R.apply α) k
  | .structural _ D => D.Evaluated σ P α k
  | @Resolve.expandCtx _ _ _ p _ _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Invariant σ P α k hk) ∧ D.Evaluated σ P α k
  | @Resolve.expandSolo _ _ _ p _ _ _ _ _ _ D =>
      (∀ hk : k.1 < P.size, p.Invariant σ P α k hk) ∧ D.Evaluated σ P α k
  | .boundaryRequired _ _ D => D.Evaluated σ P α k
  | .boundaryOptional _ _ D => D.Evaluated σ P α k
  | .unusedReset _ _ _ _ D => D.Evaluated σ P α k

theorem recover_boundary_input [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (c d : Clock) (m ℓ : Marker) (kind : TemporalKind) (I : TimeInterval)
    (φ : Formula Var) (Γ : MixedJ Clock Var) (hcd : c ≠ d) (hdΓ : d ∉ Γ.freeClocks)
    (hc : (0 : ℝ) <[Marker.imp ℓ m] (α c : ℝ))
    (hs : Judgement.holds σ P α k
      (.conj (.predicate (.upper c m kind I φ)) (.conj (.marker ℓ) Γ))) :
    Judgement.holds σ P α k (.reset (ClockResetSet.singleton d 0)
      (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))) := by
  have hm : ∀ hk : k.1 < P.size, ℓ = (P.interval ⟨k.1,hk⟩).leftBoundary := by
    intro hk
    exact (show (P.interval ⟨k.1,hk⟩).leftBoundary = ℓ from
      by simpa only [Judgement.holds, dif_pos hk] using hs.2.1).symm
  have he := boundary_merge_remove_right_reset σ P α k ClockResetSet.empty
    c d m ℓ kind I φ (.conj (.marker ℓ) Γ) hcd
    (by simpa only [Section3.Judgement.freeClocks, Set.mem_union,
      Set.mem_empty_iff_false, false_or] using hdΓ) hm hc
  have he' : Judgement.holds σ P α k (.reset (ClockResetSet.singleton d 0)
      (.conj (.conj (.predicate (.bounded c d m (¬ₘ ℓ) kind I φ))
        (.predicate (.plain (timedFormula kind I φ)))) (.conj (.marker ℓ) Γ))) ↔
      Judgement.holds σ P α k
        (.conj (.predicate (.upper c m kind I φ)) (.conj (.marker ℓ) Γ)) := by
    simpa only [Judgement.holds, ClockResetSet.apply_empty] using he
  exact he'.2 hs

/-- Backward recovery from the tree's atomic/next leaves recovers both its
input and all retained source annotations. Rule occurrence invariants are
explicit theorem hypotheses; strict boundary comparisons are actual child guards.
No path invariant propagation is assumed or claimed here. -/
theorem Resolve.recover [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hi : D.Evaluated σ P α k) (hs : Judgement.holds σ P α k A) :
    Judgement.holds σ P α k J ∧ Judgement.holds σ P α k H := by
  induction D generalizing α with
  | leaf h => exact ⟨hs,hs⟩
  | conj D E ih ig =>
      obtain ⟨hJ,hH⟩ := ih α hi.1 hs.1
      obtain ⟨hK,hG⟩ := ig α hi.2 hs.2
      exact ⟨⟨hJ,hK⟩,⟨hH,hG⟩⟩
  | reset R D ih => exact ih (R.apply α) hi hs
  | structural h D ih =>
      obtain ⟨hK,hH⟩ := ih α hi hs
      exact ⟨(h.holds_iff σ P α k).2 hK,hH⟩
  | expandCtx hb hn hf D ih =>
      obtain ⟨hBG,hH⟩ := ih α hi.2 hs
      have hp := hb.sound σ P α k hi.1 hBG.1
      exact ⟨⟨hp,hBG.2⟩,⟨hp,hH⟩⟩
  | expandSolo hb hn hf D ih =>
      obtain ⟨hB,hH⟩ := ih α hi.2 hs
      have hp := hb.sound σ P α k hi.1 hB
      exact ⟨hp,⟨hp,hH⟩⟩
  | boundaryRequired frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      exact ⟨recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩,hH⟩
  | boundaryOptional frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hi hs
      obtain ⟨hc,hΓ⟩ := (withBoundaryGuard_holds σ P α k _ _ _).1 hU.2.2
      have hraw := recover_boundary_input σ P α k _ _ _ _ _ _ _ _
        frozen.distinct hdΓ hc ⟨hU.1,hU.2.1,hΓ⟩
      exact ⟨⟨hraw.1.1,hraw.2⟩,hH⟩
  | unusedReset d v hdJ hdH D ih =>
      obtain ⟨hJ,hH⟩ := ih α hi hs
      exact ⟨(unused_singleton_reset σ P α k d v _ hdJ).2 hJ,hH⟩

/-- Raw non-predicate truth depends only on syntactically free clocks,
including guards below next. Predicate truth is never used in this lemma. -/
theorem nonPredicate_congr_of_agree {J : MixedJ Clock Var} {α β : ClockValuation Clock}
    (h : ∀ c ∈ J.freeClocks, α c = β c) (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (k : STLTableau.Judgement.Position P) :
    Judgement.nonPredicateHolds σ P α k J ↔ Judgement.nonPredicateHolds σ P β k J := by
  induction J generalizing α β k with
  | terminal => rfl
  | marker => rfl
  | predicate => rfl
  | clock c r a =>
      have hc := h c (by simp [Section3.Judgement.freeClocks])
      simp only [Judgement.nonPredicateHolds,hc]
  | conj J K ih ig =>
      exact and_congr (ih (fun c hc => h c (Or.inl hc)) k)
        (ig (fun c hc => h c (Or.inr hc)) k)
  | next J ih =>
      simp only [Judgement.nonPredicateHolds]
      split
      · apply ih
        intro c hc
        simp only [ClockResetSet.elapse,h c hc]
      · rfl
  | reset R J ih =>
      apply ih
      intro c hc
      cases hr : R.value c with
      | some v => simp [ClockResetSet.apply,hr]
      | none =>
          have hnot : c ∉ R.clocks := by
            rintro ⟨v,hv⟩
            rw [hr] at hv
            cases hv
          simpa only [ClockResetSet.apply,hr] using h c ⟨hc,hnot⟩

theorem nonPredicate_unused_singleton_reset [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (d : Clock) (v : NNReal) (J : MixedJ Clock Var) (hd : d ∉ J.freeClocks) :
    Judgement.nonPredicateHolds σ P α k (.reset (ClockResetSet.singleton d v) J) ↔
    Judgement.nonPredicateHolds σ P α k J := by
  change Judgement.nonPredicateHolds σ P ((ClockResetSet.singleton d v).apply α) k J ↔ _
  apply nonPredicate_congr_of_agree
  intro c hc
  exact ClockResetSet.apply_singleton_of_ne v α (by
    intro h
    subst c
    exact hd hc)

theorem ACIdem.nonPredicate_iff {J K : MixedJ Clock Var} (h : ACIdem J K)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) :
    Judgement.nonPredicateHolds σ P α k J ↔ Judgement.nonPredicateHolds σ P α k K := by
  induction h generalizing α with
  | refl => rfl
  | symm h ih => exact (ih α).symm
  | trans h g ih ig => exact (ih α).trans (ig α)
  | assoc => exact and_assoc
  | comm => exact and_comm
  | idem => exact and_self_iff
  | conj h g ih ig => exact and_congr (ih α) (ig α)
  | reset R h ih => exact ih (R.apply α)
  | resetDistrib R J K => rfl
  | resetUnused R J hd =>
      exact nonPredicate_congr_of_agree (reset_apply_agrees_on_free R J hd α) σ P k
  | resetNested R S J =>
      simp only [Judgement.nonPredicateHolds,ClockResetSet.apply_union_eq_comp]

theorem withBoundaryGuard_nonPredicate (σ : FiniteSignal Var)
    (P : IntervalPartition σ.domain) (α : ClockValuation Clock)
    (k : STLTableau.Judgement.Position P) (c : Clock) (b : Marker) (Γ : MixedJ Clock Var) :
    Judgement.nonPredicateHolds σ P α k (withBoundaryGuard c b Γ) ↔
      (0 : ℝ) <[b] (α c : ℝ) ∧ Judgement.nonPredicateHolds σ P α k Γ := by
  cases b with
  | «open» => simp [withBoundaryGuard,Judgement.nonPredicateHolds,ClockRelation.Holds]
  | closed =>
      simp only [withBoundaryGuard,markedLT_closed]
      exact (and_iff_right (α c).coe_nonneg).symm

/-- Unconditional backward recovery of guards, resets, markers and next
non-predicate requirements. It needs no rule invariant, temporal truth or
assumed boundary comparison. This is the first independent ingredient for
future initial-path numeric propagation. -/
theorem Resolve.nonPredicate_recover [DecidableEq Clock] {J H A : MixedJ Clock Var}
    (D : Resolve J H A) (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P)
    (hs : Judgement.nonPredicateHolds σ P α k A) :
    Judgement.nonPredicateHolds σ P α k J ∧ Judgement.nonPredicateHolds σ P α k H := by
  induction D generalizing α with
  | leaf h => exact ⟨hs,hs⟩
  | conj D E ih ig =>
      obtain ⟨hJ,hH⟩ := ih α hs.1
      obtain ⟨hK,hG⟩ := ig α hs.2
      exact ⟨⟨hJ,hK⟩,⟨hH,hG⟩⟩
  | reset R D ih => exact ih (R.apply α) hs
  | structural h D ih =>
      obtain ⟨hK,hH⟩ := ih α hs
      exact ⟨(h.nonPredicate_iff σ P α k).2 hK,hH⟩
  | expandCtx hb hn hf D ih =>
      obtain ⟨hBG,hH⟩ := ih α hs
      exact ⟨⟨trivial,hBG.2⟩,⟨trivial,hH⟩⟩
  | expandSolo hb hn hf D ih =>
      obtain ⟨_,hH⟩ := ih α hs
      exact ⟨trivial,⟨trivial,hH⟩⟩
  | @boundaryRequired c d m ℓ kind I φ Γ H A frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      obtain ⟨_,hΓ⟩ := (withBoundaryGuard_nonPredicate σ P α k _ _ _).1 hU.2.2
      have hreset := (nonPredicate_unused_singleton_reset σ P α k d 0 Γ hdΓ).2 hΓ
      exact ⟨⟨⟨trivial,trivial⟩,hU.2.1,hreset⟩,hH⟩
  | @boundaryOptional c d m ℓ kind I φ Γ H A frozen hdΓ D ih =>
      obtain ⟨hU,hH⟩ := ih α hs
      obtain ⟨_,hΓ⟩ := (withBoundaryGuard_nonPredicate σ P α k _ _ _).1 hU.2.2
      have hreset := (nonPredicate_unused_singleton_reset σ P α k d 0 Γ hdΓ).2 hΓ
      exact ⟨⟨trivial,hU.2.1,hreset⟩,hH⟩
  | unusedReset d v hdJ hdH D ih =>
      obtain ⟨hJ,hH⟩ := ih α hs
      exact ⟨(nonPredicate_unused_singleton_reset σ P α k d v _ hdJ).2 hJ,hH⟩

end STLTableau.Section4.Finiteness
