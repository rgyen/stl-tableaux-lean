import STLTableaux.Finiteness.Bounds.TruthPartitionIntervals
import STLTableaux.Finiteness.Bounds.RightClockAge

/-! Endpoint identification at the first false successor. These lemmas connect
consecutive uniformly true partition pieces to the literal right-zero reset.
The existing stable-partition bridge identifies these with signal truth intervals;
these lemmas do not
assert that an arbitrary tableau predicate has such a history. -/
namespace STLTableau.Section4.Finiteness.TruthPartitionIntervals
variable {Clock Var : Type*}

theorem blockOf_last_of_false_successor {n : ℕ} (p : Fin n → Prop)
    (i j : Fin n) (hi : p i) (hij : j.val = i.val + 1) (hj : ¬p j) :
    (blockOf p i hi).val = i := by
  have he : IsEnd p i := by
    refine ⟨hi, ?_⟩
    intro k hk
    have hkj : k = j := Fin.ext (by omega)
    simpa only [hkj] using hj
  have hb := blockOf_unique p i hi ⟨i,he⟩ (connected_refl i hi)
  exact congrArg Subtype.val hb

/-- A right-zero reset at the first false piece records exactly the maximal
uniformly true-piece block's endpoint, including zero-duration pieces.
Identifying this block with a maximal signal truth interval additionally uses
stability. Endpoint equality alone does not identify a block's origin. -/
theorem reset_endpoint_of_false_successor [DecidableEq Clock]
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) (θ : Formula Var)
    (i : Fin P.size) (hn : i.val + 1 < P.size)
    (hi : PieceTrue σ P θ i)
    (hj : ¬PieceTrue σ P θ ⟨i.val+1,hn⟩)
    (d : Clock) (α : ClockValuation Clock) :
    RightClockAge.endpoint d (P.interval ⟨i.val+1,hn⟩).left
      ((ClockResetSet.singleton d 0).apply α) =
      endpoint σ P θ (truthBlockOf σ P θ i hi) := by
  have hb := blockOf_last_of_false_successor (PieceTrue σ P θ) i
    ⟨i.val+1,hn⟩ hi rfl hj
  change (P.interval ⟨i.val+1,hn⟩).left -
      (((ClockResetSet.singleton d 0).apply α d : NNReal) : ℝ) =
    (P.interval (blockOf (PieceTrue σ P θ) i hi).val).right
  rw [hb]
  simp only [ClockResetSet.apply,ClockResetSet.singleton,if_true,NNReal.coe_zero,sub_zero]
  exact (P.adjacent_right_eq_left i hn).symm

end STLTableau.Section4.Finiteness.TruthPartitionIntervals
