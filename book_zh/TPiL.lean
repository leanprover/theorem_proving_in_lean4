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
    let version := version.dropPrefix "leanprover/lean4:" |>.dropPrefix "v" |>.trimAscii |>.copy
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Lean 4 定理证明" =>

%%%
authors := ["Jeremy Avigad", "Leonardo de Moura", "Soonho Kong", "Sebastian Ullrich"]
authorshipNote := some "并有 Lean 社区贡献"
tag := "theorem-proving-in-lean-4-zh"
%%%


本书此版本假定你使用 Lean 4（具体为 {versionString}[]）。安装 Lean 请参见
Lean 文档中的
[快速入门](https://lean-lang.org/documentation/setup/)。
本书的第一版是为 Lean 2 编写的，Lean 3 版本见
[此处](https://leanprover.github.io/theorem_proving_in_lean/)。

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
