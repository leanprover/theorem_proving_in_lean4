import VersoManual

import TPiL.Examples

open TPiL

open Verso.Genre Manual
open Verso Code External

#doc (Manual) "引言" =>
%%%
tag := "Intro"
file := "Introduction"
htmlSplit := .never
%%%

# 计算机与定理证明
%%%
tag := "computers-and-theorem-proving"
%%%

_形式化验证_ 使用逻辑和计算方法来确立以精确数学术语表述的断言。这些断言既可以包括通常的数学定理，也可以包括关于硬件或软件、
网络协议，以及机械系统和混合系统是否满足其规约的断言。在实践中，验证一段数学内容与验证一个系统的正确性之间并没有泾渭分明的界限：
形式化验证需要用数学术语描述硬件和软件系统；在这一点上，确立关于其正确性的断言就成为一种定理证明。反过来，一个数学定理的证明可能需要
冗长的计算；在这种情况下，验证该定理为真就需要验证该计算确实完成了它应当完成的任务。

支持一个数学断言的黄金标准是给出证明，而二十世纪逻辑学的发展表明，在多种基础系统中的任意一种之内，绝大多数（即便不是全部）传统证明方法
都可以化约为一小组公理和规则。有了这种化约，计算机可以通过两种方式帮助确立一个断言：它首先可以帮助寻找证明，也可以帮助验证一个声称的证明
是否正确。

_自动定理证明_ 关注“寻找”这一方面。归结定理证明器、语义表定理证明器、快速可满足性求解器等，为确立命题逻辑和一阶逻辑中公式的有效性
提供了手段。其他系统则为特定语言和领域提供搜索过程和判定过程，例如整数或实数上的线性或非线性表达式。诸如 SMT（可满足性模理论，satisfiability
modulo theories）这样的架构，将领域通用的搜索方法与领域专用的过程结合起来。计算机代数系统和专门的数学软件包
提供了执行数学计算、确立数学界限或寻找数学对象的手段。计算也可以被视为一种证明，因此这些系统同样有助于确立数学断言。

自动推理系统追求能力和效率，往往以牺牲有保证的可靠性为代价。此类系统可能存在缺陷，也可能难以确保它们给出的结果是正确的。相比之下，
_交互式定理证明_ 关注定理证明中“验证”的方面，要求每一个断言都由适当公理化基础中的一个证明来支持。这设定了非常高的标准：每一条推理规则、
每一个计算步骤，都必须通过诉诸既有定义和定理而得到辩护，并一直追溯到基本公理和规则。事实上，大多数这样的系统会给出完全细化的
“证明对象”，它们可以被传递给其他系统并独立检查。构造这样的证明通常需要用户提供更多输入并进行更多交互，但它使你能够获得更深入、更复杂的证明。

_Lean Theorem Prover_ 旨在弥合交互式定理证明与自动定理证明之间的鸿沟：它把自动化工具和方法置于一个既支持用户交互、又支持构造完全指定的
公理化证明的框架之中。其目标是同时支持数学推理和关于复杂系统的推理，并验证这两个领域中的断言。

Lean 的底层逻辑具有计算解释，因此 Lean 同样可以被看作一种编程语言。更切要地说，它可以被视为一个用于编写具有精确语义的程序的系统，
也可以用于推理这些程序所计算的函数。Lean 还具有充当自身 _元编程语言_ 的机制，这意味着你可以使用 Lean 本身实现自动化并扩展 Lean 的功能。
Lean 的这些方面在免费在线书籍 [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) 中有所说明，不过本书也会涉及该系统的计算层面。

# 关于 Lean
%%%
tag := "about-lean"
%%%

_Lean_ 项目由 Leonardo de Moura 于 2013 年在 Microsoft Research Redmond 发起。这是一项持续进行的长期工作，其自动化方面的许多潜力
只会随着时间推移逐步实现。Lean 以 [Apache 2.0 许可证](https://github.com/leanprover/lean4/blob/master/LICENSE) 发布；这是一种宽松的开源许可证，允许他人自由使用和扩展其代码与
数学库。

若要在你的计算机上安装 Lean，可考虑使用 [Quickstart](https://lean-lang.org/install/) 说明。Lean 的源代码以及构建 Lean 的说明可在
[https://github.com/leanprover/lean4/](https://github.com/leanprover/lean4/) 获取。

本教程描述的是当前版本的 Lean，即 Lean 4。

# 关于本书
%%%
tag := "about-this-book"
%%%

本书旨在教你在 Lean 中发展并验证证明。为此所需的许多背景知识其实并不专属于 Lean。首先，你将学习 Lean 所基于的逻辑系统：
一种 _依赖类型论_ 的版本；它强大到足以证明几乎任何传统数学定理，也具有足够的表达力，能以自然的方式完成这些证明。更具体地说，
Lean 基于一种被称为带归纳类型的构造演算的系统。Lean 不仅能够在依赖类型论中定义数学对象、表达数学断言，还可以作为书写证明的语言使用。

由于完全详细的公理化证明极其复杂，定理证明的挑战在于让计算机尽可能填补更多细节。你将在 {ref "dependent-type-theory"}[依赖类型论]
中学习支持这一目标的多种方法。例如，项重写，以及 Lean 自动简化项和表达式的自动化方法。同样，你也会学习 _细化_ 与 _类型推断_ 的方法；
它们可用于支持灵活形式的代数推理。

最后，你将学习 Lean 所特有的一些功能，包括你用来与系统通信的语言，以及 Lean 为管理复杂理论和数据所提供的机制。

在全文中，你会看到如下所示的 Lean 代码示例：

```lean
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
```

在本书的每个代码示例旁，你都会看到一个标为 “Copy to clipboard” 的按钮。
按下该按钮会复制示例，并附带足够的上下文，使代码能够正确编译。
你可以将示例代码粘贴到 [VS Code](https://code.visualstudio.com/) 中并修改这些示例；Lean 会在你输入时持续检查结果并提供反馈。
我们建议你在阅读后续章节时亲自运行这些示例，并对代码进行实验。
你可以在 VS Code 中使用命令 “Lean 4: Docs: Show Documentation Resources”，并在打开的标签页中选择 “Theorem Proving in Lean 4” 来打开本书。

# 致谢
%%%
tag := "acknowledgments"
%%%

本教程是一个维护在 Github 上的开放获取项目。许多人为这项工作做出了贡献，提供了修正、建议、示例和文本。我们感谢 Ulrik Buchholz、Kevin Buzzard、
Mario Carneiro、Nathan Carter、Eduardo Cavazos、Amine Chaieb、Joe Corneli、William DeMeo、Marcus Klaas de Vries、Ben Dyer、
Gabriel Ebner、Anthony Hart、Simon Hudon、Sean Leather、Assia Mahboubi、Gihan Marasingha、Patrick Massot、Christopher John Mazey、
Sebastian Ullrich、Floris van Doorn、Daniel Velleman、Théo Zimmerman、Paul Chisholm、Chris Lovett 和 Siddhartha Gadgil 的贡献。关于我们出色贡献者的最新名单，
请参见 [lean prover](https://github.com/leanprover/) 和 [lean community](https://github.com/leanprover-community/)。
