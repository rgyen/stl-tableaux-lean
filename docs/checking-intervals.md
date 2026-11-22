# Checking intervals

For a clocked interval predicate over $\square_I\varphi$ with bounded $I$,
the checking interval adds the lower and upper bounds of $I$ to the
corresponding scope endpoints. The merge lemmas use the checking interval
before restriction to the signal horizon.

| Result | Lean source |
|---|---|
| Merging two `↑↓` predicates using the union of their checking intervals | [AlwaysCheckingMerge.lean](../STLTableaux/Finiteness/Derivation/Merging/AlwaysCheckingMerge.lean) |
| Preservation of the predicate invariant | [AlwaysCheckingMergeInvariant.lean](../STLTableaux/Finiteness/Derivation/Merging/AlwaysCheckingMergeInvariant.lean) |
| Preservation of endpoint clock exclusivity | [AlwaysCheckingMergeExclusive.lean](../STLTableaux/Finiteness/Derivation/Merging/AlwaysCheckingMergeExclusive.lean) |
| Grouping predicates by the value of their left endpoint clocks | [AlwaysCheckingCells.lean](../STLTableaux/Finiteness/Bounds/AlwaysCheckingCells.lean) |
| Width and overlap of checking intervals | [AlwaysCheckingGeometry.lean](../STLTableaux/Finiteness/Bounds/AlwaysCheckingGeometry.lean) |
| Packing bounds for ordered intervals | [OrderedIntervalPacking.lean](../STLTableaux/Finiteness/Bounds/OrderedIntervalPacking.lean) |

Merging uses marker-aware comparisons at the two outer endpoints and at
the join. The join condition uses `I.upper - I.lower`, so two checking
intervals can join even when their scopes have a gap. Lemmas about clock
resets use the valuation after the resets.

Preserving `Ready` under a merge requires distinct clocks at the retained
endpoints. The exclusivity lemmas assume `ExclusiveState`. The
geometry lemmas distinguish the predicate invariant from conditions on
the clock values and endpoint markers. When the two left clock values lie in
the same half-open interval in the grouping, the merge uses
$\alpha(d_1) \le \alpha(c_1)$ and
both outer endpoint comparisons. Packing uses ordered intervals with
disjoint interiors and permits endpoint contact. [Clock age conditions](../STLTableaux/Finiteness/Derivation/Merging/AlwaysAgeShape.lean) · [Endpoint clock exclusivity](../STLTableaux/Finiteness/Derivation/Merging/EndpointExclusivityCore.lean)

The results concern individual merges and interval families. Theorem 4.37
uses the finite-tableau construction described in the correspondence guide.
[Theorem 4.37](correspondence.md#main-results)

## Checks

The full check runs the merge regression and checks the axiom dependencies
of the ordered-interval packing lemmas.
[Validation](validation.md)
