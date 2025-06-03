import VersoManual
import TPiL.Intro
import TPiL.DependentTypeTheory
import TPiL.PropositionsAndProofs
import TPiL.QuantifiersEquality
import TPiL.Tactics
import TPiL.AxiomsComputation

open Verso.Genre Manual
open Verso Code External

#doc (Manual) "Theorem Proving in Lean 4" =>

%%%
authors := ["Jeremy Avigad", "Leonardo de Moura", "Soonho Kong", "Sebastian Ullrich"] -- TODO: , with contributions from the Lean Community"
%%%


This version of the text assumes you’re using Lean 4. See the
[Quickstart section](https://lean-lang.org/documentation/setup/) of
the Lean documentation to install Lean. The first version of this book was
written for Lean 2, and the Lean 3 version is available
[here](https://leanprover.github.io/theorem_proving_in_lean/).

{include 1 TPiL.Intro}

{include 1 TPiL.DependentTypeTheory}

{include 1 TPiL.PropositionsAndProofs}

{include 1 TPiL.QuantifiersEquality}

{include 1 TPiL.Tactics}

{include 1 TPiL.AxiomsComputation}
