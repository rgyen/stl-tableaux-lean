# Source layout

`STLTableaux.lean` imports the production library. Domain imports under
`STLTableaux/` collect syntax, semantics, rules, closure, tableau construction,
finiteness, automata, model checking, and examples. Finiteness contains the
derivations, clock allocation, bounds, and finite correctness proofs.
Signal semantics is defined in `Semantics/Signals.lean`. Interval-predicate
satisfaction is defined in `Semantics/IntervalSemantics.lean`.

`STLTableauxTest/` contains interface and axiom checks, regressions, and
supplemental checks. Lake builds the test library as a separate target.
The import check catches production imports of test modules. [Import check](../scripts/check_library_imports.py)

The correspondence guide connects theorem numbers to Lean declarations and
their checks. [Correspondence](correspondence.md)

The finiteness library includes lemmas on merging interval predicates using
their checking intervals. [Checking intervals](checking-intervals.md)

Add new library modules to the corresponding domain import. Update the
correspondence guide when theorem numbers or Lean declarations change.
