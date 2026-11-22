import STLTableaux.Automata.Execution.PrelimExecution

namespace PrelimExecutionChecks
open STLTableau STLTableau.HybridAutomaton

def H : HybridAutomaton Unit Unit Unit where
  modes_finite := inferInstance
  variables_finite := inferInstance
  edge := ∅
  initial := Set.univ
  invariant := Set.univ
  flow := fun _ _ _ => True
  trajectory_closed := HybridFlow.Closed.unconstrained _
  jump := fun _ _ _ => False

def s : H.State := ⟨((), fun _ => 0), Set.mem_univ _⟩

noncomputable def oneFlow (σ : FiniteSignal Unit) (r : NNReal)
    (hr : 0 < (r : ℝ)) (hle : (r : ℝ) ≤ σ.horizon)
    (hs : ∀ t : σ.Time, t.val < r → σ.value t = fun _ => 0) :
    H.PrelimExecution σ where
  count := 1
  nonempty := by decide
  initialState := s
  initial_mem := Set.mem_univ _
  start := fun _ => s
  finish := fun _ => s
  boundary := fun i => if i.val = 0 then 0 else r
  first_zero := rfl
  increasing := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  last_le_horizon := hle
  duration := fun _ => r
  duration_eq := by
    intro i
    fin_cases i
    simp
  curve := fun _ _ _ => 0
  continuousStep := fun _ => ⟨rfl, rfl, rfl, fun _ => ⟨trivial, Set.mem_univ _⟩⟩
  initialSteps := .refl
  discreteSteps := by
    intro i hi
    exact False.elim (by omega)
  signal_eq := by
    intro i t ht
    fin_cases i
    exact hs t ht.2

noncomputable def constantSignal : FiniteSignal Unit :=
  ⟨2, by norm_num, fun _ _ => 0⟩

noncomputable def early : H.PrelimExecution constantSignal :=
  oneFlow constantSignal 1 (by norm_num) (by norm_num [constantSignal]) (fun _ _ => rfl)

noncomputable def atHorizon : H.PrelimExecution constantSignal :=
  oneFlow constantSignal 2 (by norm_num) (by norm_num [constantSignal]) (fun _ _ => rfl)

example : H.PrelimReaches constantSignal {()} :=
  early.reaches_of_final_mode rfl

example : atHorizon.boundary ⟨1, by decide⟩ = constantSignal.horizon := rfl

example : atHorizon.boundary atHorizon.lastIndex.castSucc < constantSignal.horizon :=
  atHorizon.entry_lt_horizon _

/-- A signal can have a different value at the unobserved stopping time. -/
noncomputable def suffixChanged : FiniteSignal Unit := by
  classical
  exact ⟨2, by norm_num, fun t _ => if t.val < 1 then 0 else 7⟩

noncomputable def prefixOnly : H.PrelimExecution suffixChanged :=
  oneFlow suffixChanged 1 (by norm_num) (by norm_num [suffixChanged]) (by
    intro t ht
    funext x
    exact if_pos ht)

example : suffixChanged.value ⟨1, by norm_num [suffixChanged]⟩ () = 7 := by
  simp [suffixChanged]

example : prefixOnly.finalState.val.2 () = 0 := rfl
end PrelimExecutionChecks
