import STLTableaux.Finiteness.Derivation.Pending.PendingComplexity
import STLTableaux.Finiteness.Derivation.DerivationNormalizationSoundness

/-! Syntactic invariants for pending judgements. An empty conjunction
is represented by `none`. -/
namespace STLTableau.Section4.Finiteness
open Section3
variable {Clock Var : Type*}

/-- Conjoin present syntax; an absent component introduces no judgement. -/
def optionalConj : Option (MixedJ Clock Var) → Option (MixedJ Clock Var) → Option (MixedJ Clock Var)
  | none, K => K
  | J, none => J
  | some J, some K => some (.conj J K)

def foldCurrent : List (MixedJ Clock Var) → Option (MixedJ Clock Var)
  | [] => none
  | J :: Js => optionalConj (some J) (foldCurrent Js)

/-- Current guards stay outside the common inherited reset. Existing future
requirements remain literal next leaves; their internal reset scopes stay put. -/
def canonicalSyntax (R : ClockResetSet Clock) (guards : List (Section3.Guard Clock))
    (locals : List (Section3.Local Clock Var)) (nextInputs : List (MixedJ Clock Var)) :
    Option (MixedJ Clock Var) :=
  optionalConj (foldCurrent (guards.map (fun g => g.toJudgement)))
    ((foldCurrent (locals.map Local.toJudgement ++ nextInputs.map Section3.Judgement.next)).map (Section3.Judgement.reset R))

def noNext : MixedJ Clock Var → Prop
  | .next _ => False
  | .conj J K => noNext J ∧ noNext K
  | .reset _ J => noNext J
  | _ => True

/-- Private ownership is the support of distinct live current predicates.
It permits clock-free plain duplicates to be collected and places no ban on
outside current guards reading a source clock. -/
def privateCurrent (locals : List (Section3.Local Clock Var)) : Prop :=
  ∀ p q : Predicate Clock Var, Local.predicate p ∈ locals → Local.predicate q ∈ locals →
    p ≠ q → Disjoint (syntaxClocks (.predicate p)) (syntaxClocks (.predicate q))

def currentNextSeparate (locals : List (Section3.Local Clock Var))
    (nextInputs : List (MixedJ Clock Var)) : Prop :=
  ∀ (p : Predicate Clock Var) K, Local.predicate p ∈ locals → K ∈ nextInputs →
    Disjoint (syntaxClocks (.predicate p)) (syntaxClocks K)

/-- A canonical presentation of the GIVEN pending source. All fields concern
actual syntax, finite support, input safety, or a directed collection step.
No field asserts existence of a completed resolver or a target label bound. -/
structure OwnedPending (J : MixedJ Clock Var) (R : ClockResetSet Clock) (W : Set Clock) where
  guards : List (Section3.Guard Clock)
  locals : List (Section3.Local Clock Var)
  nextInputs : List (MixedJ Clock Var)
  canonical : MixedJ Clock Var
  shape : canonicalSyntax R guards locals nextInputs = some canonical
  regroup : ACIdem J canonical
  regroup_nonincrease : pendingWeight canonical ≤ pendingWeight J
  locals_nodup : locals.Nodup
  private_sources : privateCurrent locals
  source_next : currentNextSeparate locals nextInputs
  next_private : nextInputs.Pairwise (fun K L => Disjoint (syntaxClocks K) (syntaxClocks L))
  next_flat : ∀ K ∈ nextInputs, noNext K
  absent_body_reset : locals = [] → nextInputs = [] → R = ClockResetSet.empty
  input_safe : ∃ F₀, SafeNormalization canonical F₀
  finite_budget : W.Finite
  covers_input : (syntaxClocks J ∪ syntaxClocks canonical) ∪ R.clocks ⊆ W

theorem empty_reset_clocks : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
  ext c
  constructor
  · rintro ⟨a,h⟩
    change (none : Option NNReal) = some a at h
    cases h
  · intro h
    cases h

/-- Clock-free initial formulas establish ownership without any clock or
neutral-current requirement. The empty common reset is explicit and harmless. -/
def OwnedPending.plain_root (φ : Formula Var) :
    OwnedPending (Section3.Judgement.predicate (.plain φ) : MixedJ Clock Var) ClockResetSet.empty ∅ := by
  refine ⟨[],[.predicate (.plain φ)],[],.reset ClockResetSet.empty (.predicate (.plain φ)),
    rfl,?_,?_,by simp,?_,?_,by simp,?_,?_,?_,Set.finite_empty,?_⟩
  · exact .symm (.resetUnused ClockResetSet.empty _ (by
      change Disjoint ClockResetSet.empty.clocks ∅
      exact Set.disjoint_empty _))
  · exact le_rfl
  · intro p q hp hq hne
    have hp' : p = .plain φ := by simpa using hp
    have hq' : q = .plain φ := by simpa using hq
    exact False.elim (hne (hp'.trans hq'.symm))
  · intro p K hp hK
    cases hK
  · intro K hK
    cases hK
  · intro hlocals
    cases hlocals
  · refine ⟨_,.reset ClockResetSet.empty (.predicate _) ?_⟩
    apply Set.disjoint_left.2
    intro c hc hg
    obtain ⟨g,hg,_⟩ := hg
    exact False.elim hg
  · simp only [syntaxClocks,empty_reset_clocks,Set.union_empty ]
    exact Set.Subset.refl _

/-- Prefix a present requirement without inventing a neutral judgement. -/
def prependCurrent (J : MixedJ Clock Var) : Option (MixedJ Clock Var) → MixedJ Clock Var
  | none => J
  | some K => .conj J K

noncomputable def optionalWeight : Option (MixedJ Clock Var) → ℕ
  | none => 0
  | some J => pendingWeight J

theorem foldCurrent_cons (J : MixedJ Clock Var) (Js : List (MixedJ Clock Var)) :
    foldCurrent (J :: Js) = some (prependCurrent J (foldCurrent Js)) := by
  cases h : foldCurrent Js <;> simp only [foldCurrent,h,optionalConj,prependCurrent]

theorem foldCurrent_none_iff (Js : List (MixedJ Clock Var)) :
    foldCurrent Js = none ↔ Js = [] := by
  cases Js with
  | nil => simp [foldCurrent]
  | cons J Js => rw [foldCurrent_cons]; simp

/-- Expose an actual selected pending occurrence, retaining all other syntax.
The equation counts its multiplicity exactly; this uses no unrestricted
weight-invariance claim about StructuralEq (idempotence can decrease weight). -/
theorem foldCurrent_expose (Js : List (MixedJ Clock Var)) (J K : MixedJ Clock Var)
    (hfold : foldCurrent Js = some J) (hmem : K ∈ Js) :
    ∃ Γ, ACIdem J (prependCurrent K Γ) ∧
      pendingWeight J = pendingWeight K + optionalWeight Γ := by
  induction Js generalizing J with
  | nil => cases hmem
  | cons L Ls ih =>
      rw [foldCurrent_cons] at hfold
      have he : prependCurrent L (foldCurrent Ls) = J := Option.some.inj hfold
      subst J
      rcases List.mem_cons.mp hmem with he | hmem
      · subst K
        refine ⟨foldCurrent Ls,.refl _,?_⟩
        cases h : foldCurrent Ls <;> simp [prependCurrent,optionalWeight,pendingWeight]
      · cases htail : foldCurrent Ls with
        | none =>
            have hempty := (foldCurrent_none_iff Ls).1 htail
            subst Ls
            cases hmem
        | some T =>
            obtain ⟨Γ,hΓ,hweight⟩ := ih T htail hmem
            cases Γ with
            | none =>
                refine ⟨some L,?_,?_⟩
                · exact .trans (.conj (.refl L) hΓ) (.comm L K)
                · simp only [prependCurrent,optionalWeight,pendingWeight] at hweight ⊢
                  omega
            | some G =>
                refine ⟨some (.conj L G),?_,?_⟩
                · exact .trans (.conj (.refl L) hΓ)
                    (.trans (.symm (.assoc L K G))
                      (.trans (.conj (.comm L K) (.refl G)) (.assoc K L G)))
                · simp only [prependCurrent,optionalWeight,pendingWeight] at hweight ⊢
                  omega

end STLTableau.Section4.Finiteness
