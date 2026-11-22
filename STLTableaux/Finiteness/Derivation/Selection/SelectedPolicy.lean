import STLTableaux.Finiteness.Derivation.Pending.PendingAllocatedChild
import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryBackward
import STLTableaux.Finiteness.Derivation.Pending.PendingMaximalSelection
import STLTableaux.Finiteness.Derivation.Pending.PendingBoundaryChild
import STLTableaux.Finiteness.Derivation.CanonicalResetMap

/-! Internal finite selected-derivation certificates. These do not add a
rule to the tableau. Semantic eligibility is a theorem input; tree constructors
contain only actual syntax, rule witnesses and maximal-selection evidence. -/
namespace STLTableau.Section4.Finiteness
open Section3
open scoped STL
variable {Clock Var : Type*}

def IsBoundedPredicate : Predicate Clock Var → Prop
  | .bounded _ _ _ _ _ _ _ => True
  | _ => False

structure Eligibility
    [DecidableEq Clock] (E : Set (Predicate Clock Var))
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (U : Set Clock)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain)
    (α : ClockValuation Clock) (k : STLTableau.Judgement.Position P) : Prop where
  bounded : ∀p∈E, IsBoundedPredicate p
  unique_formula : ∀p∈E, ∀q∈E, p.formula=q.formula → p=q
  current : ∀p∈E, Local.predicate p ∈ owned.locals →
    ∃c d m ℓ kind I φ,
      p = .bounded c d m (¬ₘ ℓ) kind I φ ∧
      Nonempty (FrozenByUpper c d m ℓ kind I φ) ∧ Local.marker ℓ ∈ owned.locals ∧
      R.value d = some 0 ∧
      Judgement.holds σ P (R.apply α) k (.predicate (.plain (timedFormula kind I φ))) ∧
      (0 : ℝ) <[Marker.imp ℓ m] ((R.apply α) c : ℝ) ∧
      (Marker.imp ℓ m = ○ → c∈U)

def MaximalSource (locals : List (Local Clock Var)) (p : Predicate Clock Var) : Prop :=
  ¬p.IsAtomic ∧ ∀q, Local.predicate q∈locals → ¬q.IsAtomic → q.complexity≤p.complexity

def OrdinaryAllowed (E : Set (Predicate Clock Var)) (locals : List (Local Clock Var))
    (p : Predicate Clock Var) : Prop :=
  p∉E ∧ ¬∃q∈E, Local.predicate q∈locals ∧ p = .plain q.formula

noncomputable def ordinarySelectedInput (R : ClockResetSet Clock)
    (remaining : List (Local Clock Var)) (B : MixedJ Clock Var)
    (residual : Option (MixedJ Clock Var)) : MixedJ Clock Var :=
  match residual with
  | none => B
  | some Γ => .conj B (.reset (copyActiveResets R remaining) Γ)

def ordinarySelectedFresh [DecidableEq Clock] (p : Predicate Clock Var)
    (R : ClockResetSet Clock) (remaining : List (Local Clock Var))
    (B : MixedJ Clock Var) (residual : Option (MixedJ Clock Var)) : Prop :=
  match residual with
  | none => FreshWithoutContext p B
  | some Γ => FreshFor p B (.reset (copyActiveResets R remaining) Γ)

structure OrdinaryChoice [DecidableEq Clock] (E : Set (Predicate Clock Var))
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) where
  p : Predicate Clock Var
  left : List (Local Clock Var)
  right : List (Local Clock Var)
  split : owned.locals = left ++ Local.predicate p :: right
  maximal : MaximalSource owned.locals p
  allowed : OrdinaryAllowed E owned.locals p
  x : Clock
  fresh_name : x∉W
  B : MixedJ Clock Var
  branch : RawBranch p B
  fresh : ordinarySelectedFresh p R (left++right) B
    (foldCurrent ((left++right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))
  reset_support : resetNames B ⊆ syntaxClocks (.predicate p) ∪ {x}
  childR : ClockResetSet Clock
  childW : Set Clock
  child : OwnedPending (ordinarySelectedInput R (left++right) B
    (foldCurrent ((left++right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))) childR childW
  grows : W ⊆ childW
  reset_origin : childR=currentResetMap (ordinarySelectedInput R (left++right) B
    (foldCurrent ((left++right).map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next)))
  old_absorption : ∀ c∈W, (childR.union R).value c = R.value c
  agreement : ∀ c∈activeSupport (left++right), childR.value c = R.value c
  fixed_guard_support : ∀ U, U⊆W → Disjoint R.clocks U → Disjoint childR.clocks U

structure BoundaryChoice [DecidableEq Clock] (E : Set (Predicate Clock Var))
    {J : MixedJ Clock Var} {R : ClockResetSet Clock} {W : Set Clock}
    (owned : OwnedPending J R W) (required : Bool) where
  c : Clock
  d : Clock
  m : Marker
  ell : Marker
  kind : TemporalKind
  I : TimeInterval
  phi : Formula Var
  left : List (Local Clock Var)
  right : List (Local Clock Var)
  rest : List (Local Clock Var)
  split : owned.locals = left ++ Local.predicate (.bounded c d m (¬ₘ ell) kind I phi) :: right
  selection : (left++right).Perm (if required then
    .predicate (.plain (timedFormula kind I phi)) :: .marker ell :: rest else .marker ell :: rest)
  eligible : Predicate.bounded c d m (¬ₘ ell) kind I phi ∈ E
  maximal : MaximalSource owned.locals
    (if required then .plain (timedFormula kind I phi) else .bounded c d m (¬ₘ ell) kind I phi)
  right_zero : R.value d = some 0
  frozen : FrozenByUpper c d m ell kind I phi
  Gamma : MixedJ Clock Var
  residual : Gamma = prependCurrent (.marker ell)
    (foldCurrent (rest.map Local.toJudgement ++ owned.nextInputs.map Section3.Judgement.next))
  child : OwnedPending
    (boundaryReplacementChild c m ell kind I phi (.reset (copyActiveResets R (left++right)) Gamma))
    (copyActiveResets R (left++right)) W

/-- The full/erased indices are the actual recursively assembled raw outputs.
The optional constructor forces the upper expansion before its child tree. -/
inductive SelectedTree [DecidableEq Clock] (E : Set (Predicate Clock Var)) (U : Set Clock) :
    {J : MixedJ Clock Var} → {R : ClockResetSet Clock} → {W : Set Clock} →
    OwnedPending J R W → MixedJ Clock Var → MixedJ Clock Var → Type _
  | zero {J R W} (owned : OwnedPending J R W) (hzero : pendingWeight owned.canonical = 0) :
      SelectedTree E U owned owned.canonical owned.canonical
  | ordinary {J R W H Er} (owned : OwnedPending J R W) (choice : OrdinaryChoice E owned)
      (tail : SelectedTree E U choice.child H Er) :
      SelectedTree E U owned
        (outsidePending owned.guards R (.conj (.predicate choice.p) H))
        (outsidePending owned.guards R Er)
  | required {J R W H Er} (owned : OwnedPending J R W) (choice : BoundaryChoice E owned true)
      (tail : SelectedTree E U choice.child H Er) :
      SelectedTree E U owned (outsidePending owned.guards R H) (outsidePending owned.guards R Er)
  | optional {J R W H Er} (owned : OwnedPending J R W) (choice : BoundaryChoice E owned false)
      (upper : OrdinaryChoice E choice.child)
      (forced : upper.p = .upper choice.c choice.m choice.kind choice.I choice.phi)
      (tail : SelectedTree E U upper.child H Er) :
      SelectedTree E U owned
        (outsidePending owned.guards R
          (outsidePending choice.child.guards (copyActiveResets R (choice.left++choice.right))
            (.conj (.predicate upper.p) H)))
        (outsidePending owned.guards R
          (outsidePending choice.child.guards (copyActiveResets R (choice.left++choice.right)) Er))

end STLTableau.Section4.Finiteness
