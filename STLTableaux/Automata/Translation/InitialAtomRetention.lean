import STLTableaux.Automata.Translation.EmptyContinuationSupport

/-! Unclocked atomic predicates in the current part cannot be removed by structural normalization or
resolution. In particular, translating an atomic input really constrains
the initial state of the translated automaton, before any initial discrete steps. -/
namespace STLTableau.Section4.Finiteness.InitialAtomRetention
open Section3
variable {Clock Var : Type*}

def occurs (a : AtomicProposition Var) : MixedJ Clock Var → Prop
  | .predicate (.plain (.atom b)) => a = b
  | .conj J K => occurs a J ∨ occurs a K
  | .reset _ J => occurs a J
  | _ => False

theorem structural {J K : MixedJ Clock Var} (h : ACIdem J K) (a : AtomicProposition Var) :
    occurs a J ↔ occurs a K := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig
  | assoc => simp only [occurs]; tauto
  | comm => simp only [occurs]; tauto
  | idem => simp only [occurs]; tauto
  | conj h g ih ig => exact or_congr ih ig
  | reset R h ih => exact ih
  | resetDistrib => rfl
  | resetUnused => rfl
  | resetNested => rfl

theorem normalized {J : MixedJ Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : SafeNormalization J F) (a : AtomicProposition Var) :
    occurs a J ↔ Local.predicate (.plain (.atom a)) ∈ F.current.locals := by
  induction h with
  | terminal => simp [occurs, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | clock => simp [occurs, Section3.TransitionForm.ofState, Section3.StateForm.ofGuard]
  | marker => simp [occurs, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | predicate p =>
    cases p with
    | plain φ =>
      cases φ <;> simp [occurs, Section3.TransitionForm.ofState,
        Section3.StateForm.ofLocal, eq_comm]
    | upper => simp [occurs, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
    | bounded => simp [occurs, Section3.TransitionForm.ofState, Section3.StateForm.ofLocal]
  | conj h g hc ih ig =>
    simpa [occurs, Section3.TransitionForm.union, Section3.StateForm.union] using or_congr ih ig
  | reset R h hd ih => simpa [occurs, Section3.TransitionForm.underReset] using ih
  | next h hn ih => simp [occurs, Section3.TransitionForm.ofNextState, Section3.StateForm.empty]

variable [DecidableEq Clock]

theorem resolve {J H A : MixedJ Clock Var} (h : Resolve J H A) (a : AtomicProposition Var) :
    occurs a J → occurs a H := by
  induction h with
  | leaf => exact id
  | conj h g ih ig => exact Or.imp ih ig
  | reset R h ih => exact ih
  | structural h g ih => exact fun ha => ih ((structural h a).mp ha)
  | expandCtx branch nonatom fresh child ih =>
    intro ha
    exact ha.elim Or.inl (fun hc => Or.inr (ih (Or.inr hc)))
  | expandSolo branch nonatom fresh child ih => exact Or.inl
  | @boundaryRequired c d m ℓ kind I φ Γ H A frozen fresh child ih =>
    cases kind <;> cases ℓ <;> cases m <;>
      simp [occurs, timedFormula, Formula.always, Formula.eventually,
        withBoundaryGuard, Marker.imp] at * <;> tauto
  | @boundaryOptional c d m ℓ kind I φ Γ H A frozen fresh child ih =>
    cases ℓ <;> cases m <;>
      simp [occurs, withBoundaryGuard, Marker.imp] at * <;> tauto
  | unusedReset d v fresh freshH child ih => exact ih

theorem derives {N : Section3.StateForm Clock Var} {F : Section3.TransitionForm Clock Var}
    (h : Derives N F) (a : AtomicProposition Var)
    (ha : Local.predicate (.plain (.atom a)) ∈ N.locals) :
    Local.predicate (.plain (.atom a)) ∈ F.current.locals := by
  cases h with
  | original closure ready => exact closure.extension.current.locals ha
  | resolved D hJ hH hA =>
    exact (normalized hH a).mp (resolve D a ((normalized hJ a).mpr ha))

theorem atom_initial [Infinite Clock] (X : Set Var) (a : AtomicProposition Var)
    (l : EdgeLabel Clock) (F : Section3.TransitionForm Clock Var)
    (hi : (l, F) ∈ (finiteRootTableau (Clock := Clock) X (.atom a)).initial) :
    Local.predicate (.plain (.atom a)) ∈ JudgementTableau.labels F := by
  have hd : Derives (Section3.StateForm.ofLocal (.predicate (.plain (.atom a)))) F := hi.1.1
  exact ⟨derives hd a (by rfl), by trivial⟩

theorem empty_atom_initial [Infinite Clock] (X : Set Var) (a : AtomicProposition Var)
    (root : Formula.NormalizedInput Var) (hr : root.val = .atom a)
    (l : EdgeLabel Clock) (F : Section3.TransitionForm Clock Var)
    (hi : (l, F) ∈ (withEmptyContinuation (Clock := Clock) X root).initial) :
    Local.predicate (.plain (.atom a)) ∈
      (withEmptyContinuation (Clock := Clock) X root).label F := by
  apply atom_initial X a l F
  change (l, F) ∈ (finiteRootTableau (Clock := Clock) X root.val).initial at hi
  simpa only [hr] using hi

run_elab do
  for name in #[``structural, ``normalized, ``resolve, ``derives,
      ``atom_initial, ``empty_atom_initial] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} uses unexpected axiom {ax}"

end STLTableau.Section4.Finiteness.InitialAtomRetention
