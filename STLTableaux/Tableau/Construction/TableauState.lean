import STLTableaux.Tableau.Construction.Tableau

/-! Closure and generator pairs in Definition 4.28 (tableau construction).
A transition matches the source next-part to the successor generator and
takes its clock constraints and resets from the successor closure. -/
namespace STLTableau.Section4
variable {Clock Var : Type*}

structure ClosureState (Clock Var : Type*) where
  form : Section3.TransitionForm Clock Var
  generator : Section3.StateForm Clock Var

namespace ClosureState
def incoming (s : ClosureState Clock Var) : EdgeLabel Clock :=
  ⟨s.form.current.guards, s.form.current.guards_finite, s.form.current.resets⟩

def edge (s : ClosureState Clock Var) (e : EdgeLabel Clock)
    (t : ClosureState Clock Var) : Prop :=
  s.form.nextPart = some t.generator ∧ e = t.incoming

end ClosureState
end STLTableau.Section4
