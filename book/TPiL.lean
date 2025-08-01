import VersoManual
import TPiL.Intro
import TPiL.DependentTypeTheory
import TPiL.PropositionsAndProofs
import TPiL.QuantifiersEquality
import TPiL.Tactics
import TPiL.InteractingWithLean
import TPiL.InductiveTypes
import TPiL.InductionAndRecursion
import TPiL.StructuresAndRecords
import TPiL.TypeClasses
import TPiL.Conv
import TPiL.AxiomsComputation

open Verso.Genre Manual
open Verso Code External

open Verso Doc Elab in
open Lean (quote) in
@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do
    let version ← IO.FS.readFile "../examples/lean-toolchain"
    let version := version.stripPrefix "leanprover/lean4:" |>.trim
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Theorem Proving in Lean 4" =>

%%%
authors := ["Jeremy Avigad", "Leonardo de Moura", "Soonho Kong", "Sebastian Ullrich"]
authorshipNote := some "with contributions from the Lean Community"
%%%


This version of the text assumes you’re using Lean 4 (specifically {versionString}[]). See the
[Quickstart section](https://lean-lang.org/documentation/setup/) of
the Lean documentation to install Lean. The first version of this book was
written for Lean 2, and the Lean 3 version is available
[here](https://leanprover.github.io/theorem_proving_in_lean/).

{include 1 TPiL.Intro}

{include 1 TPiL.DependentTypeTheory}

{include 1 TPiL.PropositionsAndProofs}

{include 1 TPiL.QuantifiersEquality}

{include 1 TPiL.Tactics}

{include 1 TPiL.InteractingWithLean}

{include 1 TPiL.InductiveTypes}

{include 1 TPiL.InductionAndRecursion}

{include 1 TPiL.StructuresAndRecords}

{include 1 TPiL.TypeClasses}

{include 1 TPiL.Conv}

{include 1 TPiL.AxiomsComputation}
