import STLTableaux.Finiteness.Derivation.Pending.PendingOwnership
import STLTableaux.Finiteness.Derivation.NormalizationSupport

/-! Rebuild safe normalization directly for actual canonical input syntax.
Current locals have no reset bindings; future requirements retain literal next
scope. Outside guards are outside the common reset and may read its names.
No safety transport through arbitrary StructuralEq is assumed. -/
namespace STLTableau.Section4.Finiteness.CanonicalSafety
open Section3
variable {Clock Var : Type*}

private theorem empty_clocks : (ClockResetSet.empty : ClockResetSet Clock).clocks = ∅ := by
  ext c
  constructor
  · rintro ⟨a,ha⟩; cases ha
  · intro h; cases h

/-- A reset-free state-only left component needs no disjoint-all-support test.
Only another CURRENT reset capturing one of its LOCAL clocks is relevant. -/
theorem state_compatible (S : Section3.StateForm Clock Var)
    (G : Section3.TransitionForm Clock Var) (hr : S.resets = ClockResetSet.empty)
    (hd : Disjoint G.current.resets.clocks S.localClocks) :
    (Section3.TransitionForm.ofState S).UnionCompatible G := by
  apply Section3.TransitionForm.unionCompatible_of_captureFree
  · intro c a b ha
    change S.resets.value c = some a at ha
    rw [hr] at ha
    cases ha
  · simpa only [Section3.TransitionForm.ofState,Section3.TransitionForm.bodyFreeClocks,
      hr,empty_clocks,Set.union_empty,Set.sdiff_empty] using hd
  · change Disjoint S.resets.clocks _
    rw [hr,empty_clocks]
    exact Set.disjoint_left.2 (fun _ hc _ => False.elim hc)
  · intro N M hn; cases hn
  · intro N M hn; cases hn
  · intro N M hn; cases hn

private theorem fold_disjoint (U : Set Clock) (Js : List (MixedJ Clock Var))
    (J : MixedJ Clock Var) (hf : foldCurrent Js = some J)
    (hm : ∀ K ∈ Js, Disjoint U (syntaxClocks K)) : Disjoint U (syntaxClocks J) := by
  induction Js generalizing J with
  | nil => cases hf
  | cons K Ks ih =>
    cases ht : foldCurrent Ks with
    | none =>
      have he : K = J := by simpa [foldCurrent,ht,optionalConj] using hf
      exact he ▸ hm K (by simp)
    | some T =>
      have he : .conj K T = J := by simpa [foldCurrent,ht,optionalConj] using hf
      subst J
      exact (hm K (by simp)).union_right (ih T ht (fun L hL => hm L (by simp [hL])))

private theorem fold_safe_disjoint (Js : List (MixedJ Clock Var))
    (hp : Js.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K)))
    (hs : ∀ J ∈ Js, ∃ F, SafeNormalization J F ∧
      F.current.guards = ∅ ∧ F.current.resets = ClockResetSet.empty)
    (J : MixedJ Clock Var) (hf : foldCurrent Js = some J) :
    ∃ F, SafeNormalization J F ∧ F.current.guards = ∅ ∧ F.current.resets = ClockResetSet.empty := by
  induction Js generalizing J with
  | nil => cases hf
  | cons K Ks ih =>
    obtain ⟨F,hF,hFg,hFr⟩ := hs K (by simp)
    cases ht : foldCurrent Ks with
    | none =>
      have he : K = J := by simpa [foldCurrent,ht,optionalConj] using hf
      exact he ▸ ⟨F,hF,hFg,hFr⟩
    | some T =>
      have he : .conj K T = J := by simpa [foldCurrent,ht,optionalConj] using hf
      subst J
      obtain ⟨G,hG,hGg,hGr⟩ := ih (List.pairwise_cons.mp hp).2
        (fun L hL => hs L (by simp [hL])) T ht
      have hd := fold_disjoint (syntaxClocks K) Ks T ht (List.pairwise_cons.mp hp).1
      refine ⟨F.union G,.conj hF hG (NormalizationSupport.unionCompatible_of_disjoint_syntax hF hG hd),?_,?_⟩
      · change F.current.guards ∪ G.current.guards = ∅
        rw [hFg,hGg,Set.union_empty]
      · change F.current.resets.union G.current.resets = ClockResetSet.empty
        rw [hFr,hGr]
        rfl

private theorem next_fold_safe
    (Ks : List (MixedJ Clock Var))
    (hp : Ks.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K)))
    (hs : ∀ K ∈ Ks, ∃ N, SafeNormalization K (Section3.TransitionForm.ofState N))
    (J : MixedJ Clock Var) (hf : foldCurrent (Ks.map Section3.Judgement.next) = some J) :
    ∃ F, SafeNormalization J F ∧ F.current.guards = ∅ ∧ F.current.resets = ClockResetSet.empty := by
  apply fold_safe_disjoint (Ks.map Section3.Judgement.next) _ _ J hf
  · simpa only [List.pairwise_map,syntaxClocks] using hp
  · intro K hK
    obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hK
    obtain ⟨N,hN⟩ := hs L hL
    exact ⟨_,.next hN rfl,rfl,rfl⟩

private theorem local_safe (l : Local Clock Var) :
    SafeNormalization l.toJudgement (Section3.TransitionForm.ofState (Section3.StateForm.ofLocal l)) := by
  cases l with
  | terminal => exact .terminal
  | marker m => exact .marker m
  | predicate p => exact .predicate p

/-- Rebuild the local/next payload; current clocks may overlap next clocks,
because current locals have no binders and next scopes stay literal. -/
private theorem payload_safe (L : List (Local Clock Var)) (Ks : List (MixedJ Clock Var))
    (hp : Ks.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K)))
    (hs : ∀ K ∈ Ks, ∃ N, SafeNormalization K (Section3.TransitionForm.ofState N))
    (J : MixedJ Clock Var)
    (hf : foldCurrent (L.map Local.toJudgement ++ Ks.map Section3.Judgement.next) = some J) :
    ∃ F, SafeNormalization J F ∧ F.current.guards = ∅ ∧ F.current.resets = ClockResetSet.empty := by
  induction L generalizing J with
  | nil => exact next_fold_safe Ks hp hs J hf
  | cons l L ih =>
    cases ht : foldCurrent (L.map Local.toJudgement ++ Ks.map Section3.Judgement.next) with
    | none =>
      have he : l.toJudgement = J := by
        simpa only [List.map_cons,List.cons_append,foldCurrent,ht,optionalConj,Option.some.injEq] using hf
      subst J
      exact ⟨_,local_safe l,rfl,rfl⟩
    | some T =>
      have he : .conj l.toJudgement T = J := by
        simpa only [List.map_cons,List.cons_append,foldCurrent,ht,optionalConj,Option.some.injEq] using hf
      subst J
      obtain ⟨F,hF,hg,hr⟩ := ih T ht
      have hc := state_compatible (Section3.StateForm.ofLocal l) F rfl
        (by rw [hr,empty_clocks]; exact Set.disjoint_left.2 (fun _ hc _ => False.elim hc))
      refine ⟨(Section3.TransitionForm.ofState (Section3.StateForm.ofLocal l)).union F,
        .conj (local_safe l) hF hc,?_,?_⟩
      · change ∅ ∪ F.current.guards = ∅
        rw [hg,Set.union_empty]
      · change ClockResetSet.empty.union F.current.resets = ClockResetSet.empty
        rw [hr]
        rfl

theorem guards_safe (gs : List (Guard Clock)) (J : MixedJ Clock Var)
    (hf : foldCurrent (gs.map (fun g => g.toJudgement)) = some J) :
    ∃ S : Section3.StateForm Clock Var, SafeNormalization J (Section3.TransitionForm.ofState S) ∧
      S.resets = ClockResetSet.empty ∧ S.locals = ∅ := by
  induction gs generalizing J with
  | nil => cases hf
  | cons g gs ih =>
    cases ht : foldCurrent (gs.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
    | none =>
      have he : g.toJudgement = J := by simpa [foldCurrent,ht,optionalConj] using hf
      subst J
      exact ⟨_,.clock g.clock g.relation g.bound,rfl,rfl⟩
    | some T =>
      have he : .conj g.toJudgement T = J := by simpa [foldCurrent,ht,optionalConj] using hf
      subst J
      obtain ⟨S,hS,hr,hl⟩ := ih T ht
      have hc := state_compatible (Section3.StateForm.ofGuard g) (Section3.TransitionForm.ofState S) rfl
        (by
          change Disjoint S.resets.clocks _
          rw [hr,empty_clocks]
          exact Set.disjoint_left.2 (fun _ hc _ => False.elim hc))
      refine ⟨(Section3.StateForm.ofGuard g).union S,.conj (.clock g.clock g.relation g.bound) hS hc,?_,?_⟩
      · change ClockResetSet.empty.union S.resets = ClockResetSet.empty
        rw [hr]
        rfl
      · change ∅ ∪ S.locals = ∅
        rw [hl,Set.union_empty]

/-- Actual outside-guard spine, compatible with every following transition.
Its guards remain before that transition's reset scope. -/
theorem guard_spine (gs : List (Guard Clock)) (J : MixedJ Clock Var)
    (hf : foldCurrent (gs.map (fun g => g.toJudgement)) = some J) :
    ∃ S : Section3.StateForm Clock Var,
      SafeNormalization J (Section3.TransitionForm.ofState S) ∧
      S.resets = ClockResetSet.empty ∧ S.locals = ∅ ∧
      ∀ F : Section3.TransitionForm Clock Var,
        (Section3.TransitionForm.ofState S).UnionCompatible F := by
  obtain ⟨S,hS,hr,hl⟩ := guards_safe gs J hf
  refine ⟨S,hS,hr,hl,?_⟩
  intro F
  apply state_compatible S F hr
  simp only [Section3.StateForm.localClocks,hl,Set.mem_empty_iff_false,
    false_and,exists_false,Set.setOf_false]
  exact Set.disjoint_empty _

/-- Direct canonical safety rebuild. No local/next separation or guard/reset
freshness premise is needed: only distinct future payloads' binding scopes
must be disjoint, and each future payload already normalizes in state form. -/
theorem exists_safe_canonical (R : ClockResetSet Clock) (gs : List (Guard Clock))
    (L : List (Local Clock Var)) (Ks : List (MixedJ Clock Var)) (C : MixedJ Clock Var)
    (hshape : canonicalSyntax R gs L Ks = some C)
    (hs : ∀ K ∈ Ks, ∃ N, SafeNormalization K (Section3.TransitionForm.ofState N))
    (hp : Ks.Pairwise (fun J K => Disjoint (syntaxClocks J) (syntaxClocks K))) :
    ∃ F, SafeNormalization C F := by
  cases hg : foldCurrent (gs.map (fun g => (g.toJudgement : MixedJ Clock Var))) with
  | none =>
    cases hb : foldCurrent (L.map Local.toJudgement ++ Ks.map Section3.Judgement.next) with
    | none => simp [canonicalSyntax,hg,hb,optionalConj] at hshape
    | some B =>
      have he : .reset R B = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
      subst C
      obtain ⟨F,hF,hFg,_⟩ := payload_safe L Ks hp hs B hb
      refine ⟨_,.reset R hF ?_⟩
      simp only [Section3.StateForm.guardClocks,hFg,Set.mem_empty_iff_false,false_and,exists_false,Set.setOf_false]
      exact Set.disjoint_empty _
  | some G =>
    obtain ⟨S,hS,hSr,hSl⟩ := guards_safe gs G hg
    cases hb : foldCurrent (L.map Local.toJudgement ++ Ks.map Section3.Judgement.next) with
    | none =>
      have he : G = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
      exact he ▸ ⟨_,hS⟩
    | some B =>
      have he : .conj G (.reset R B) = C := by simpa [canonicalSyntax,hg,hb,optionalConj] using hshape
      subst C
      obtain ⟨F,hF,hFg,_⟩ := payload_safe L Ks hp hs B hb
      have hReset : SafeNormalization (.reset R B) (F.underReset R) := .reset R hF (by
        simp only [Section3.StateForm.guardClocks,hFg,Set.mem_empty_iff_false,false_and,exists_false,Set.setOf_false]
        exact Set.disjoint_empty _)
      have hc := state_compatible S (F.underReset R) hSr (by
        simp only [Section3.StateForm.localClocks,hSl,Set.mem_empty_iff_false,false_and,exists_false,Set.setOf_false]
        exact Set.disjoint_empty _)
      exact ⟨_,.conj hS hReset hc⟩

end STLTableau.Section4.Finiteness.CanonicalSafety
