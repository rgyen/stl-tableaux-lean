import STLTableaux.Automata.Recognition.TypedVisitMarkers
import STLTableaux.Automata.Recognition.ExecutionObservation

namespace STLTableau.Section4.Tableau
variable {Clock Var State : Type*} (T : Tableau Clock Var State)
variable (h : T.TranslationReady) (τ : ℝ)
local notation "𝓗" => (T.typedAutomaton h τ)

/-- Every target of a jump at the horizon is terminal, including targets
in the last discrete block. None represents an ordinary singleton at τ. -/
theorem typed_horizon_jump_target {a b : (𝓗).State}
    (hj : (𝓗).DiscreteStep a b) (hc : a.val.2 (.inl T.globalClock) = τ) :
    b.val.1 ∈ T.terminalModes := by
  obtain ⟨_, _, _, _, _, _, _, hg, _, ht, _⟩ := hj
  exact ht.mpr (hg.trans hc).ge

/-- No suffix and no interval for the terminal jump. The last positive
flow ends at τ; the original visit markers determine every left boundary. -/
theorem terminal_cut_partition {σ : FiniteSignal T.TypedVar}
    (e : (𝓗).Execution σ) (hh : σ.horizon = τ) {a : (𝓗).State}
    (hj : (𝓗).DiscreteStep a e.finalState) (ht : e.finalState.val.1 ∈ T.terminalModes) :
    let i : Fin e.count := ⟨e.count - 1, by have := e.nonempty; omega⟩
    ∃ xs, BeforeFlow T h τ e i xs ∧
      let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
      ∃ (P : IntervalPartition (Set.Ico 0 τ)) (hn : P.size = vs.length),
        ∀ j : Fin vs.length, let J := P.interval ⟨j.val,hn.symm ▸ j.isLt⟩
          J.left = vs[j.val].left ∧ J.right = vs[j.val].right ∧
          J.leftBoundary = T.visitMarker h τ vs[j.val].state ∧
          (j.val+1 = vs.length → J.rightBoundary = ○) := by
  let i : Fin e.count := ⟨e.count - 1, by have := e.nonempty; omega⟩
  have hi : i.succ = (⟨e.count, by omega⟩ : Fin (e.count+1)) := by
    apply Fin.ext
    have := e.nonempty
    dsimp [i]
    omega
  have hend : e.boundary i.succ = τ := hi ▸ T.typed_terminal_cut h τ e hh hj ht
  have hpos : e.boundary i.castSucc < τ :=
    (e.increasing Fin.castSucc_lt_succ).trans_eq hend
  obtain ⟨xs,hp⟩ := T.exists_beforeFlow h τ e i
  let vs := xs ++ [⟨e.start i,e.boundary i.castSucc,τ⟩]
  have times : VisitTimes T h τ vs τ :=
    .snoc (T.beforeFlow_times h τ e hp) _ hpos.le
  have marks : VisitMarks T h τ ● vs ● :=
    .snoc _ (T.beforeFlow_marks h τ e hp) rfl (fun eq => (hpos.ne eq).elim)
  obtain ⟨P,hn,hs⟩ := T.visitPartition h τ times marks
  refine ⟨xs,hp,P,hn,?_⟩
  intro j
  change (P.interval _).left = _ ∧ _
  rw [hs j]
  refine ⟨rfl,rfl,rfl,?_⟩
  intro hlast
  change j.val+1 = vs.length at hlast
  change ((vs[j.val+1]?.map (fun v => T.visitMarker h τ v.state)).getD ●).complement = ○
  rw [show vs[j.val+1]? = none from List.getElem?_eq_none (by omega)]
  rfl

/-- If the successor flow excludes its left endpoint, the incoming jump
checks the source atoms on the value actually observed at that time.
The source may itself be the intermediate singleton. -/
theorem typed_open_entry_source_atoms {σ : FiniteSignal T.TypedVar}
    (e : (𝓗).Execution σ) (i : Fin e.count) {a : (𝓗).State}
    (hj : (𝓗).DiscreteStep a (e.start i)) (ho : T.visitMarker h τ (e.start i) = ○)
    (positive : 0 < (e.startTime i).val) :
    T.atomsAt a.val.1 (σ.value (e.startTime i)) := by
  rw [e.signal_at_start i positive]
  exact T.open_jump_checks_source h τ hj ho

end STLTableau.Section4.Tableau
