import STLTableaux.Automata.Composition.SystemTableauComposition

namespace SystemTableauCompositionChecks
open STLTableau STLTableau.Section4

def T : Tableau Nat (Fin 2) Unit where
  realVariables := {0}
  clocks := {7}
  states := Set.univ
  edges := ∅
  initial := ∅
  final := ∅
  label := fun _ => ∅
  label_atomic := fun _ _ h => h.elim

def x : T.realVariables := ⟨0, rfl⟩
def c : T.clocks := ⟨7, rfl⟩

noncomputable def σ : FiniteSignal T.CompositionVar :=
  ⟨2, by norm_num, fun t n => match n.val with
    | .inl i => if i = 0 then t.val + 1 else 7
    | .inr (.inl (.inl _)) => 11
    | .inr (.inl (.inr _)) => t.val
    | .inr (.inr b) => if b then 1 else 2⟩

theorem same_real_name : T.systemCoordinate 0 = T.tableauCoordinate (.inl (.inl x)) :=
  T.shared_real_coordinate x

theorem real_value (t : σ.Time) : (T.systemSignal σ).value t 0 = t.val + 1 := rfl

theorem private_system_value (t : σ.Time) : (T.systemSignal σ).value t 1 = 7 := by
  change (if (1 : Fin 2) = 0 then t.val + 1 else 7) = 7
  simp

theorem monitor_real_value (t : σ.Time) :
    (T.tableauSignal σ).value t (.inl (.inl x)) = t.val + 1 := rfl

theorem monitor_clock_value (t : σ.Time) :
    (T.tableauSignal σ).value t (.inl (.inr (.inl c))) = 11 := rfl

theorem monitor_global_value (t : σ.Time) :
    (T.tableauSignal σ).value t (.inl T.globalClock) = t.val := rfl

theorem monitor_dwell_value (t : σ.Time) : (T.tableauSignal σ).value t T.dwell = 2 := rfl
theorem monitor_bit_value (t : σ.Time) : (T.tableauSignal σ).value t T.bit = 1 := rfl

theorem actual_projection : T.TypedProjectsTo (T.tableauSignal σ) (T.systemSignal σ) :=
  T.tableauSignal_projectsTo σ

example : (T.systemSignal σ).horizon = 2 ∧ (T.tableauSignal σ).horizon = 2 := ⟨rfl, rfl⟩

example : T.systemCoordinate 0 ≠ T.tableauCoordinate (.inl T.globalClock) :=
  T.monitor_clock_fresh 0 (.inr ())

example : T.systemCoordinate 1 ≠ T.tableauCoordinate T.dwell := T.monitor_bit_fresh 1 false
example : T.systemCoordinate 1 ≠ T.tableauCoordinate T.bit := T.monitor_bit_fresh 1 true

example : T.tableauCoordinate (.inl (.inr (.inl c))) ≠ T.tableauCoordinate T.bit := by
  intro equal
  have name := congrArg Subtype.val equal
  cases name

run_elab do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``same_real_name, ``real_value, ``private_system_value, ``monitor_real_value,
      ``monitor_clock_value, ``monitor_global_value, ``monitor_dwell_value,
      ``monitor_bit_value, ``actual_projection] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do throwError "{name} uses unexpected axiom {ax}"

end SystemTableauCompositionChecks
