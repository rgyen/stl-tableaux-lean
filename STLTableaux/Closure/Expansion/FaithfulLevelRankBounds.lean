import STLTableaux.Closure.Expansion.FaithfulPExpansion

/-! Global level maxima do not require finitely many clock representatives:
the natural-valued complexity image is bounded by the source complexity. -/
namespace STLTableau.Section3
variable {Clock Var : Type*}
namespace ConcreteContextual

private theorem finite_branch_source_pos [DecidableEq Clock]
    {p : IntervalPredicate Clock Var} {R : ExpansionRule Clock Var}
    (hr : STLTableau.ConcreteRule p R) : 0 < (Predicate.ofFinite p).complexity := by
  cases hr <;>
    simp [Predicate.ofFinite,Predicate.complexity,Predicate.formulaComplexity,
      Formula.or,Formula.release,Formula.eventually,Formula.always,Formula.untimedUntil] <;> omega

theorem branch_source_pos [DecidableEq Clock]
    {p : Predicate Clock Var} {Λ : ClockResetSet Clock} {B : TransitionForm Clock Var}
    (hb : catalogue.Branch p Λ B) : 0 < p.complexity := by
  obtain ⟨R,A,hR,ha,hB⟩ := hb
  rcases hR with h | h | h
  · obtain ⟨p₀,E,raw,F,rfl,hr,hm,hn,hF⟩ := h
    exact finite_branch_source_pos hr
  · obtain ⟨p₀,Bs,raw,F,rfl,hr,hm,hn,hF⟩ := h
    cases p₀ <;> simp [Predicate.ofUnbounded,Predicate.complexity]
  · obtain ⟨c,m,kind,a,φ,F,rfl,hn,hF⟩ := h
    cases kind <;>
      simp [Predicate.complexity,Predicate.formulaComplexity,UnboundedClocked.formula,
        Formula.eventually,Formula.always]

theorem unclosed_source_pos [DecidableEq Clock]
    (F : TransitionForm Clock Var) (p : Predicate Clock Var)
    (h : ¬ catalogue.RuleClosedFor F p) : 0 < p.complexity := by
  classical
  have hex : ∃ B, catalogue.Branch p F.current.resets B := by
    by_contra hn
    exact h (Or.inl hn)
  exact branch_source_pos hex.choose_spec

theorem zero_complexity_ruleClosed [DecidableEq Clock]
    (F : TransitionForm Clock Var) (p : Predicate Clock Var) (hp : p.complexity = 0) :
    catalogue.RuleClosedFor F p := by
  classical
  by_contra hn
  have h := unclosed_source_pos F p hn
  omega
end ConcreteContextual
namespace ExpansionFamily

def ComplexityBounded (S : Set (TransitionForm Clock Var)) (N : ℕ) : Prop :=
  ∀ F ∈ S, ∀ p, Local.predicate p ∈ F.current.locals → p.complexity ≤ N

def openComplexities (E : ClosureCatalogue Clock Var) (S : Set (TransitionForm Clock Var)) : Set ℕ :=
  {n | ∃ F ∈ S, ∃ p, Local.predicate p ∈ F.current.locals ∧
    ¬ E.RuleClosedFor F p ∧ p.complexity = n}

/-- Maximum open-predicate complexity for the auxiliary complete rounds,
with value zero for an empty set of complexities. -/
noncomputable def familyRank (E : ClosureCatalogue Clock Var)
    (S : Set (TransitionForm Clock Var)) : ℕ := sSup (openComplexities E S)

noncomputable def initialBound (F : TransitionForm Clock Var) : ℕ :=
  (FaithfulClosure.statePredicates F.current).sup Predicate.complexity

theorem initialBound_spec (F : TransitionForm Clock Var) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ F.current.locals) : p.complexity ≤ initialBound F := by
  classical
  exact Finset.le_sup ((FaithfulClosure.mem_statePredicates F.current p).2 hp)

theorem singleton_bounded (F : TransitionForm Clock Var) : ComplexityBounded {F} (initialBound F) := by
  intro G hG p hp
  have he : G = F := hG
  subst G
  exact initialBound_spec F p hp

theorem openComplexities_bddAbove (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N) :
    BddAbove (openComplexities E S) := by
  refine ⟨N,?_⟩
  rintro n ⟨F,hF,p,hp,_,rfl⟩
  exact h F hF p hp

theorem openComplexities_finite (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N) :
    (openComplexities E S).Finite := by
  apply (Set.finite_Iic N).subset
  rintro n ⟨F,hF,p,hp,_,rfl⟩
  exact h F hF p hp

theorem complexity_le_familyRank (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N)
    {F : TransitionForm Clock Var} (hF : F ∈ S) (p : Predicate Clock Var)
    (hp : Local.predicate p ∈ F.current.locals) (ho : ¬ E.RuleClosedFor F p) :
    p.complexity ≤ familyRank E S :=
  le_csSup (openComplexities_bddAbove E h) ⟨F,hF,p,hp,ho,rfl⟩

theorem familyRank_eq_zero_of_all_closed (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} (h : ∀ F ∈ S, E.IsClosed F) : familyRank E S = 0 := by
  have he : openComplexities E S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨F,hF,p,hp,ho,he⟩
    exact ho (h F hF p hp)
  simp [familyRank,he]

theorem familyRank_le (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N) :
    familyRank E S ≤ N := by
  by_cases he : (openComplexities E S).Nonempty
  · exact csSup_le he (by rintro n ⟨F,hF,p,hp,_,rfl⟩; exact h F hF p hp)
  · have he' : openComplexities E S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simp [familyRank,he']

theorem familyRank_attained (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N)
    (hne : (openComplexities E S).Nonempty) :
    ∃ F ∈ S, ∃ p, Local.predicate p ∈ F.current.locals ∧
      ¬ E.RuleClosedFor F p ∧ p.complexity = familyRank E S :=
  Nat.sSup_mem hne (openComplexities_bddAbove E h)

theorem familyRank_lt_of_all_lt (E : ClosureCatalogue Clock Var)
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (hN : 0 < N)
    (h : ∀ F ∈ S, ∀ p, Local.predicate p ∈ F.current.locals →
      ¬ E.RuleClosedFor F p → p.complexity < N) : familyRank E S < N := by
  by_cases he : (openComplexities E S).Nonempty
  · have hb : BddAbove (openComplexities E S) := by
      refine ⟨N,?_⟩
      rintro n ⟨F,hF,p,hp,ho,rfl⟩
      exact (h F hF p hp ho).le
    obtain ⟨F,hF,p,hp,ho,hn⟩ := Nat.sSup_mem he hb
    rw [familyRank,← hn]
    exact h F hF p hp ho
  · have he' : openComplexities E S = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    simpa [familyRank,he'] using hN

theorem familyRank_zero_iff_closed [DecidableEq Clock]
    {S : Set (TransitionForm Clock Var)} {N : ℕ} (h : ComplexityBounded S N) :
    familyRank ConcreteContextual.catalogue S = 0 ↔
      ∀ F ∈ S, ConcreteContextual.catalogue.IsClosed F := by
  constructor
  · intro hz F hF p hp
    by_contra ho
    have hlo := ConcreteContextual.unclosed_source_pos F p ho
    have hle := complexity_le_familyRank ConcreteContextual.catalogue h hF p hp ho
    omega
  · exact familyRank_eq_zero_of_all_closed _
end ExpansionFamily
end STLTableau.Section3
