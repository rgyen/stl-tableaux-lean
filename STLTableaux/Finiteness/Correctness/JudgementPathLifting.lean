import STLTableaux.Finiteness.Correctness.JudgementTableau

/-! Restore generators without changing the path, for the SAME admission
relation. This neither replaces Derives by literal closure nor contracts jumps. -/
namespace STLTableau.Section4.Finiteness.JudgementTableau
variable {Clock Var : Type*}

theorem exists_generator_lift_valid
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hp : p.valid (tableau X Q root R))
    (N : Section3.StateForm Clock Var) (hN : R N p.firstState) :
    ∃ q : Path Clock (ClosureState Clock Var),
      q.valid (Generated.tableau X Q root R) ∧
      q.firstState.generator = N ∧ forgetGenerator q = p := by
  induction p generalizing N with
  | last incoming F => exact ⟨.last incoming ⟨F, N⟩, hN, rfl, rfl⟩
  | step incoming F p ih =>
    obtain ⟨_, hp, _, _, M, hnext, hM, hlabel⟩ := hp
    obtain ⟨q, hq, hgen, heq⟩ := ih hp M hM
    have hform : q.firstState.form = p.firstState := by
      rw [← first_state, heq]
    have hin : q.firstIncoming = p.firstIncoming := by
      rw [← first_incoming, heq]
    refine ⟨.step incoming ⟨F, N⟩ q, ⟨hN, hq, ?_⟩, rfl, ?_⟩
    · refine ⟨hN, ?_, ?_, ?_⟩
      · simpa only [hgen, hform] using hM
      · simpa only [hgen] using hnext
      · simpa only [hin, ClosureState.incoming, hform, JudgementTableau.incoming] using hlabel
    · exact congrArg (Path.step incoming F) heq

/-- Every accepting run can recover its generator-pair representation.
All incoming labels, states' forms and trace positions remain identical. -/
theorem exists_generator_lift_accepting_run
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (p : Path Clock (Section3.TransitionForm Clock Var))
    (hr : p.run (tableau X Q root R)) (ha : p.accepting (tableau X Q root R)) :
    ∃ q : Path Clock (ClosureState Clock Var),
      q.run (Generated.tableau X Q root R) ∧
      q.accepting (Generated.tableau X Q root R) ∧
      forgetGenerator q = p ∧
      q.trace Generated.labels Generated.labels_finite = p.trace labels labels_finite := by
  obtain ⟨q, hq, hgen, heq⟩ := exists_generator_lift_valid X Q root R p hr.1 root hr.2.1
  have hform : q.firstState.form = p.firstState := by rw [← first_state, heq]
  have hin : q.firstIncoming = p.firstIncoming := by rw [← first_incoming, heq]
  refine ⟨q, ⟨hq, ?_⟩, ⟨hq, ?_⟩, heq, ?_⟩
  · refine ⟨?_, hgen, ?_⟩
    · simpa only [hgen, hform] using hr.2.1
    · simpa only [hin, ClosureState.incoming, hform, incoming] using hr.2.2
  · change q.lastState.form.nextPart = none
    rw [← last_state, heq]
    exact ha.2
  · rw [← ordinary_trace_forward, heq]

/-- Forgetting the generator alone changes neither accepting traces nor
recognition on any fixed partition. The admission relation is unchanged. -/
theorem recognizes_iff_generator_pairs
    (X : Set Var) (Q : Set Clock) (root : Section3.StateForm Clock Var)
    (R : Section3.StateForm Clock Var → Section3.TransitionForm Clock Var → Prop)
    (σ : FiniteSignal Var) (P : IntervalPartition σ.domain) :
    (tableau X Q root R).recognizes labels_finite σ P ↔
      (Generated.tableau X Q root R).recognizes Generated.labels_finite σ P := by
  constructor
  · rintro ⟨p, hr, ha, hs⟩
    obtain ⟨q, hqr, hqa, _, htrace⟩ := exists_generator_lift_accepting_run X Q root R p hr ha
    refine ⟨q, hqr, hqa, ?_⟩
    change ∀ α, (q.trace Generated.labels Generated.labels_finite).holds σ P α ⟨0, by omega⟩
    rw [htrace]
    exact hs
  · exact recognizes_forward X Q root R R (fun _ _ h => h) σ P

end STLTableau.Section4.Finiteness.JudgementTableau
