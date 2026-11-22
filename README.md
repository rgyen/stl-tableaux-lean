# STL Tableaux in Lean

This Lean 4 library accompanies *Unfolding Continuous Time:
Interval-Based Tableaux for Signal Temporal Logic over Finite Signals*.
It formalizes interval predicates and expansion rules, closure
soundness and completeness, and the construction of sound and complete finite
tableaux. It also formalizes the translation from tableaux to hybrid automata
and the reduction of Boolean and robust STL model checking to goal reachability.

The theorem index links numbered results and examples to Lean declarations.
[Theorem index and scope](docs/correspondence.md) · [Assumptions](docs/assumptions.md)

The prototype translates STL formulas to hybrid automata. The experiment
archive contains the prototype and the benchmark results reported in the manuscript.
[Prototype](https://github.com/rgyen/stl-tableaux) · [Experiment archive](https://doi.org/10.6084/m9.figshare.34420410.v1)

<a name="installation-and-sanity-check"></a>

## Installation and quick check

Use Git, Python 3.11 or later, and elan with `~/.elan/bin` on `PATH`.
Initial setup requires internet access. [Lean installation guide](https://lean-lang.org/install/)

Run the following commands from the repository root.

```sh
elan toolchain install leanprover/lean4:v4.32.2
lake exe cache get
python3 scripts/check_formalization.py --smoke --lsp
```

A successful run reports `smoke: PASS`. Allow roughly 30 minutes for setup
and the first check with the Mathlib cache. Suggested resources are 16 GB of
RAM and 25 GB of free disk space.

## Complete evaluation

```sh
python3 scripts/check_formalization.py --full --lsp
```

A successful run reports `full: PASS`.
[Checks and logs](docs/validation.md)

## Find and use the proofs

The formalization is in `STLTableaux/`. The tests and axiom checks are in
`STLTableauxTest/`. [Repository layout](docs/layout.md)

The following example uses the finite tableau construction in Theorem 4.37
to show that the tableau has finitely many states. Use `STLTableaux` in
imports. The declarations in the example use the `STLTableau` namespace.

```lean
import STLTableaux

open STLTableau STLTableau.Section4.Finiteness

example {Clock Var : Type*} [DecidableEq Clock] [Infinite Clock]
    (X : Set Var) (root : Formula Var) :
    (finiteTableau (Clock := Clock) X root).states.Finite :=
  finiteTableau_states_finite X root
```

The library also includes lemmas that use checking intervals to merge
interval predicates for $\square_I\varphi$ with bounded $I$.
[Checking intervals](docs/checking-intervals.md)

To explore the proofs, open a source file with the Lean 4 extension in VS Code.

## AI assistance and license

OpenAI Codex assisted with drafting and revising parts of the Lean
formalization and with developing the evaluation checks.

The Lean and Python code is distributed under the GNU General Public License,
version 3. [License text](LICENSE)
