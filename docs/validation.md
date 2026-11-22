# Validation

Run the quick or full check from the repository root.
The toolchain and dependencies are pinned in `lean-toolchain` and
`lake-manifest.json`. [Installation](../README.md#installation-and-quick-check) · [Dependency revisions](../lake-manifest.json)

```sh
python3 scripts/check_formalization.py --smoke --lsp
python3 scripts/check_formalization.py --full --lsp
```

- **Quick check.** Builds `STLTableaux`, checks the main declarations and their
  axioms, and compiles a small example that imports the library.
- **Full check.** Builds `STLTableaux` and `STLTableauxTest`. It checks the
  named results and examples, their axiom dependencies, and the Lean
  regression and diagnostic files.

Both modes check the library's imports and run the Python tests. The direct
axiom, interface, and regression checks treat compiler warnings as errors.
With `--lsp`, the script requires complete diagnostics for the modules it checks.
Lean errors fail the check, and LSP warnings appear in the logs.

The whole-library axiom check allows `propext`, `Classical.choice`, and
`Quot.sound`.
[Declaration checks](../STLTableauxTest/Axioms/Claims.lean) · [Whole-library check](../STLTableauxTest/Axioms/Library.lean)

A passing run reports `smoke: PASS` or `full: PASS`. If a check fails, the
script prints the path to its log. Logs and `summary.json` are in
`.formalization-build/validation/smoke/` or `.formalization-build/validation/full/`.
