/-
Copyright (c) 2026 Geunyeol Yu. All rights reserved.
Released under the GNU General Public License, version 3. See LICENSE.
Authors: Geunyeol Yu
-/
import STLTableaux.Rules.Catalogue.ClockedExpansion
import STLTableaux.Rules.Catalogue.Expansion
import STLTableaux.Rules.Finite.Bridge
import STLTableaux.Rules.Finite.ClockedSoundness
import STLTableaux.Rules.Finite.Correctness
import STLTableaux.Rules.Finite.Equivalences
import STLTableaux.Rules.Finite.Preservation
import STLTableaux.Rules.Finite.Rules
import STLTableaux.Rules.Finite.SelectedBranches
import STLTableaux.Rules.Finite.Transitions
import STLTableaux.Rules.Invariants.NumericBranchPreservation
import STLTableaux.Rules.Invariants.NumericGuardTypePreservation
import STLTableaux.Rules.Invariants.Section4RuleInvariants
import STLTableaux.Rules.Merging.ConnectedBoundedMerge
import STLTableaux.Rules.Merging.ConnectedDeferMerge
import STLTableaux.Rules.Merging.ConnectedGeneratorMerge
import STLTableaux.Rules.Merging.ConnectedMergeInvariant
import STLTableaux.Rules.Merging.ConnectedMergeStability
import STLTableaux.Rules.Merging.ConnectedMergeTransport
import STLTableaux.Rules.Unbounded.Unbounded
import STLTableaux.Rules.Unbounded.UnboundedAlwaysCompleteness
import STLTableaux.Rules.Unbounded.UnboundedClockedRules
import STLTableaux.Rules.Unbounded.UnboundedCorrectness
import STLTableaux.Rules.Unbounded.UnboundedEventuallyCompleteness
import STLTableaux.Rules.Unbounded.UnboundedOpeningPreservation
import STLTableaux.Rules.Unbounded.UnboundedPastHelpers
import STLTableaux.Rules.Unbounded.UnboundedPreservation
import STLTableaux.Rules.Unbounded.UnboundedSelectedBranches

/-! Expansion rules and their correctness and invariant preservation
(Theorem 3.13 and Proposition 3.14). -/
