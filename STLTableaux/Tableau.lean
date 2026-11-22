/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Tableau.Construction.GeneratorPath
import STLTableaux.Tableau.Construction.Tableau
import STLTableaux.Tableau.Construction.TableauState
import STLTableaux.Tableau.Correctness.GeneratorPathCompleteness
import STLTableaux.Tableau.Correctness.TableauCorrectness
import STLTableaux.Tableau.Correctness.TableauSoundness
import STLTableaux.Tableau.Stability.ClosureStability
import STLTableaux.Tableau.Stability.GeneratorStability
import STLTableaux.Tableau.Support.FreeClockRestriction
import STLTableaux.Tableau.Traces.FullTraceFreeClocks
import STLTableaux.Tableau.Traces.TableauTraceLemmas
import STLTableaux.Tableau.Traces.TracePrefixTransport
import STLTableaux.Tableau.Traces.TraceSubsumption

/-! Tableau construction (Definition 4.28), trace equivalence (Lemma 4.31),
and tableau soundness and completeness (Theorems 4.32 and 4.34). -/
