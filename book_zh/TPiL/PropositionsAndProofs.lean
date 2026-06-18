import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL



set_option pp.rawOnError true

#doc (Manual) "命题与证明" =>
%%%
tag := "propositions-and-proofs"
file := "Propositions-and-Proofs"
htmlSplit := .never
%%%

到目前为止，你已经见过一些在 Lean 中定义对象和函数的方法。在本章中，我们还将开始说明如何用依值类型论的语言书写数学断言和证明。

# 命题即类型
%%%
tag := "propositions-as-types"
%%%

要证明关于依值类型论语言中所定义对象的断言，一种策略是在定义语言之上再叠加一套断言语言和一套证明语言。但没有理由以这种方式增殖语言：依值类型论灵活而富有表达力，我们没有理由不能在同一个一般框架中表示断言和证明。

例如，我们可以引入一个新类型 {lean}`Prop` 来表示命题，并引入构造子从已有命题构造新的命题。
```lean
def Implies (p q : Prop) : Prop := p → q
------
#check And     -- And (a b : Prop) : Prop

#check Or      -- Or (a b : Prop) : Prop

#check Not     -- Not (a : Prop) : Prop

#check Implies -- Implies (p q : Prop) : Prop

variable (p q r : Prop)

#check And p q                      -- p ∧ q : Prop

#check Or (And p q) r               -- p ∧ q ∨ r : Prop

#check Implies (And p q) (And q p)  -- Implies (p ∧ q) (q ∧ p) : Prop
```

```setup
variable (p : Prop)
structure Proof (p : Prop) : Type where
  proof : p
variable (t : p) (q r : Prop)
def Implies (p q : Prop) : Prop := p → q
universe u
variable (t1 t2 : p) {α : Type u} {β : Type v}
```
于是，对于每个元素 {lean}`p : Prop`，我们还可以引入另一种类型 {lean}`Proof p`，作为 {lean}`p` 的证明类型。所谓“公理”就是这种类型的一个常量。
```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
#check Proof   -- Proof (p : Prop) : Type

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q     -- and_commut p q : Proof (Implies (p ∧ q) (q ∧ p))
```
不过，除了公理之外，我们还需要从旧证明构造新证明的规则。例如，在许多命题逻辑的证明系统中，我们有 _modus ponens_（肯定前件）规则：

> 从 {lean}`Implies p q` 的一个证明和 {lean}`p` 的一个证明，可以得到 {lean}`q` 的一个证明。

我们可以将它表示如下：
```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q
```
命题逻辑的自然演绎系统通常还依赖下列规则：

> 假设在把 {lean}`p` 作为假设的前提下，我们有 {lean}`q` 的一个证明。那么我们可以“取消”该假设，并得到 {lean}`Implies p q` 的一个证明。

我们可以将它呈现如下：
```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)
```
这种方法会为我们提供一种构造断言和证明的合理方式。要判定表达式 {lean}`t` 是否是断言 {lean}`p` 的正确证明，就只需检查 {lean}`t` 是否具有类型 {lean}`Proof p`。

然而，还可以作一些简化。首先，我们可以把 {lean}`Proof p` 与 {lean}`p` 本身合并起来，从而避免反复书写项 {lean}`Proof`。换言之，只要有 {lean}`p : Prop`，我们就可以把 {lean}`p` 解释为一个类型，即它的证明所成的类型。于是，我们可以把 {lean}`t : p` 读作断言 {lean}`t` 是 {lean}`p` 的一个证明。

此外，一旦作出这种认同，蕴含的规则就表明，我们可以在 {lean}`Implies p q` 与 {lean}`p → q` 之间来回转换。换言之，命题 {lean}`p` 与 {lean}`q` 之间的蕴含，对应于拥有一个函数，它把 {lean}`p` 的任意元素映到 {lean}`q` 的一个元素。因此，引入联结词 {lean}`Implies` 完全是多余的：我们可以使用依值类型论中通常的函数空间构造子 {lean}`p → q` 作为我们的蕴含概念。

这正是构造演算（Calculus of Constructions）所采用的方法，因此 Lean 也采用这种方法。自然演绎证明系统中蕴含规则与函数抽象和应用规则完全对应这一事实，是 {deftech}_Curry-Howard isomorphism_（Curry-Howard 同构）的一个实例；它有时也称为 {deftech}_propositions-as-types_（命题即类型）范式。事实上，类型 {lean}`Prop` 是 {lean}`Sort 0` 的语法糖，也就是上一章所描述的类型层级的最底层。此外，{lean}`Type u` 也只是 {lean}`Sort (u+1)` 的语法糖。{lean}`Prop` 有一些特殊性质，但像其他类型宇宙一样，它在箭头构造子下封闭：如果有 {lean}`p q : Prop`，那么 {lean}`p → q : Prop`。

至少有两种方式可以理解“命题即类型”。对于一些以构造性观点看待逻辑和数学的人来说，这忠实地表达了作为一个命题意味着什么：命题 {lean}`p` 表示某种数据类型，即对构成证明的数据类型的规范。于是，{lean}`p` 的证明就只是一个类型正确的对象 {lean}`t : p`。

不倾向于这种思想的人则可以把它看作一种简单的编码技巧。对于每个命题 {lean}`p`，我们关联一个类型：如果 {lean}`p` 为假，该类型为空；如果 {lit}`p` 为真，该类型有一个元素，比如 {lit}`*`。在后一种情形下，我们说（与）{lean}`p`（相关联的类型）是 _有居项的_。碰巧函数应用和抽象规则可以方便地帮助我们跟踪 {lean}`Prop` 的哪些元素是有居项的。因此，构造一个元素 {lean}`t : p` 告诉我们 {lean}`p` 确实为真。你可以把 {lean}`p` 的居项看成“{lean}`p` 为真这一事实”。{lean}`p → q` 的一个证明使用“{lean}`p` 为真这一事实”来得到“{lean}`q` 为真这一事实”。

事实上，如果 {lean}`p : Prop` 是任意命题，Lean 的内核会把任意两个元素 {lean}`t1 t2 : p` 视为定义相等，这与它把 {lit}`(fun x => t) s` 和 {lit}`t[s/x]` 视为定义相等非常类似。这称为 {deftech}_proof irrelevance_（证明无关性），并且与上一段的解释一致。它意味着，即使我们可以把证明 {lean}`t : p` 当作依值类型论语言中的普通对象来处理，它们除了 {lean}`p` 为真这一事实之外不携带任何信息。

我们提出的关于 {tech}[propositions-as-types]（命题即类型）范式的两种理解方式，在根本上有所不同。从构造性的观点看，证明是抽象的数学对象，由依值类型论中合适的表达式来 _指称_。相反，如果我们按照上面所描述的编码技巧来思考，那么表达式本身并不指称任何有趣的东西。真正起作用的是：我们能够把它们写下来，并检查它们是良类型的；这一事实保证了相关命题为真。换言之，表达式 _本身_ 就是证明。

在下面的阐述中，我们会在这两种说法之间来回切换：有时说一个表达式“构造”“产生”或“返回”某个命题的证明，有时又直接说它“是”这样的证明。这类似于计算机科学家有时会模糊语法与语义之间的区别：有时说一个程序“计算”某个函数，有时又仿佛该程序“就是”所讨论的函数。

无论如何，真正重要的是底线。要在依值类型论语言中形式化地表达一个数学断言，我们需要给出一个项 {lean}`p : Prop`。要 _证明_ 该断言，我们需要给出一个项 {lean}`t : p`。Lean 作为证明助手的任务，是帮助我们构造这样的项 {lean}`t`，并验证它形式良好且具有正确的类型。

# 使用命题即类型
%%%
tag := "working-with-propositions-as-types"
%%%

在 {tech}[propositions-as-types]（命题即类型）范式中，只涉及 {lit}`→` 的定理可以用 lambda 抽象和应用来证明。在 Lean 中，{kw}`theorem` 命令引入一个新的定理：
```lean
set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```
将这个证明与类型为 {lean}`α → β → α` 的表达式 {lit}`fun x : α => fun y : β => x` 相比较，其中 {lean}`α` 和 {lean}`β` 是数据类型。这个表达式描述了一个函数，它分别接受类型为 {leanRef}`α` 和 {leanRef}`β` 的参数 {lit}`x` 与 {lit}`y`，并返回 {lit}`x`。{lean}`t1` 的证明具有相同的形式，唯一的区别是 {lean}`p` 和 {lean}`q` 是 {lean}`Prop` 的元素，而不是 {lean}`Type` 的元素。直观地说，我们对 {lean}`p → q → p` 的证明假设 {lean}`p` 与 {lean}`q` 为真，并（平凡地）使用第一个假设来确立结论 {lean}`p` 为真。

注意，{kw}`theorem` 命令实际上是 {kw}`def` 命令的一个版本：在命题与类型的对应下，证明定理 {lean}`p → q → p` 实际上等同于定义相关类型的一个元素。对于内核类型检查器来说，二者没有区别。

不过，定义与定理之间有一些实际差异。在通常情况下，永远没有必要展开一个定理的“定义”；由 {tech}[proof irrelevance]（证明无关性），该定理的任意两个证明都是定义相等的。一旦一个定理的证明完成，通常我们只需要知道证明存在；证明具体是什么并不重要。鉴于这一事实，Lean 将证明标记为 _不可约_，这可作为给解析器（更准确地说，是 _elaborator_）的提示：处理文件时通常无需展开它们。事实上，Lean 通常能够并行处理和检查证明，因为评估一个证明的正确性并不需要知道另一个证明的细节。此外，在定义体中被引用的 {ref "variables-and-sections"}[节变量] 会自动加入为参数，但对于定理，只有在定理类型中被引用的变量才会加入。这是因为一个命题被证明的方式不应影响所证明的命题本身。

与定义一样，{kw}`#print` 命令会显示一个定理的证明：
```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1 -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```
注意，lambda 抽象 {leanRef}`hp : p` 和 {leanRef}`hq : q` 可以被看作 {lean}`t1` 的证明中的临时假设。Lean 还允许我们用 {kw}`show` 语句显式指定最终项 {leanRef}`hp` 的类型：
```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```
添加这类额外信息可以提高证明的清晰度，并帮助在书写证明时发现错误。{kw}`show` 命令所做的不过是标注类型；在内部，我们已经见过的 {leanRef}`t1` 的所有呈现都会产生同一个项。

与普通定义一样，我们可以把 lambda 抽象出来的变量移到冒号左侧：
```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```
我们可以像进行函数应用一样使用定理 {leanRef}`t1`：
```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```
{kw}`axiom` 声明假定给定类型的一个元素存在，并且可能破坏逻辑一致性。例如，我们可以用它假定空类型 {lean}`False` 有一个元素：
```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound
```
:::setup
```
variable {p q : Prop} (hp : p) {t1 : p → q → p}
```
声明一个“公理” {lean}`hp : p` 等同于声明 {lean}`p` 为真，并由 {lean}`hp` 作为见证。将定理 {lean}`t1 : p → q → p` 应用于事实 {lean}`hp : p`（即 {lean}`p` 为真）会得到定理 {lean}`t1 hp : q → p`。

:::

回忆一下，我们也可以把定理 {leanRef}`t1` 写成如下形式：
```lean
set_option linter.unusedVariables false
------
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```
现在 {leanRef}`t1` 的类型是 {lean}`∀ {p q : Prop}, p → q → p`。我们可以把它读作断言“对于每一对命题 {lean}`p`{lit}` `{lean}`q`，都有 {lean}`p → q → p`。” 例如，我们可以把所有参数都移到冒号右侧：
```lean
set_option linter.unusedVariables false
------
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```
如果 {lean}`p` 和 {lean}`q` 已经被声明为 {ref "variables-and-sections"}[变量]，Lean 会自动为我们将它们泛化：
```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```
当我们以这种方式泛化 {leanRef}`t1` 时，就可以把它应用于不同的命题对，从而得到这个一般定理的不同实例。
```lean
set_option linter.unusedVariables false
------
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- t1 p q : p → q → p
#check t1 r s                -- t1 r s : r → s → r
#check t1 (r → s) (s → r)    -- t1 (r → s) (s → r) : (r → s) → (s → r) → r → s

variable (h : r → s)

#check t1 (r → s) (s → r) h  -- t1 (r → s) (s → r) h : (s → r) → r → s
```
再次利用 {tech}[propositions-as-types]（命题即类型）对应，类型为 {leanRef}`r → s` 的变量 {leanRef}`h` 可以被看作假设或前提，即 {leanRef}`r → s` 成立。

另一个例子是，让我们考虑上一章讨论过的复合函数，不过现在把类型换成命题。
```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```
作为命题逻辑的定理，{leanRef}`t2` 表达了什么？

注意，对于假设，使用数字 Unicode 下标通常很有用；它们可通过输入 {kbd}`\0`、{kbd}`\1`、{kbd}`\2`、……得到，正如本例中所做的那样。

# 命题逻辑
%%%
tag := "propositional-logic"
%%%

Lean 定义了所有标准的逻辑联结词及其记号。命题联结词带有如下记号：

:::table +header
*
 * ASCII
 * Unicode
 * 编辑器快捷输入
 * 定义

*
 * {lean}`True`
 * {empty}[]
 * {empty}[]
 * {lean}`True`

*
 * {lean}`False`
 * {empty}[]
 * {empty}[]
 * {lean}`False`

*
 * {lean}`Not`
 * {lit}`¬`
 * {kbd}`\not`, {kbd}`\neg`
 * {lean}`Not`

*
 * {lit}`/\`
 * {lit}`∧`
 * {kbd}`\and`
 * {lean}`And`

*
 * {lit}`\/`
 * {lit}`∨`
 * {kbd}`\or`
 * {lean}`Or`

*
 * {lit}`->`
 * {lit}`→`
 * {kbd}`\to`, {kbd}`\r`, {kbd}`\imp`
 * {empty}[]

*
 * {lit}`<->`
 * {lit}`↔`
 * {kbd}`\iff`, {kbd}`\lr`
 * {lean}`Iff`

:::

它们的取值都在 {lean}`Prop` 中。
```lean
variable (p q : Prop)

#check p → q → p ∧ q

#check ¬p → p ↔ False

#check p ∨ q → q ∨ p
```
:::setup
```
variable (p q r a b c d e : Prop)
```
运算优先级如下：一元否定 {lit}`¬` 结合最强，其次是 {lit}`∧`，再其次是 {lit}`∨`，然后是 {lit}`→`，最后是 {lit}`↔`。例如，{lean}`a ∧ b → c ∨ d ∧ e` 表示 {lean}`(a ∧ b) → (c ∨ (d ∧ e))`。请记住，{lit}`→` 右结合（现在参数是 {lean}`Prop` 的元素而不是某个其他 {lean}`Type`，这一点并没有改变），其他二元联结词也是如此。因此，如果有 {lean}`p q r : Prop`，表达式 {lean}`p → q → r` 读作“若 {lean}`p`，则若 {lean}`q`，则 {lean}`r`。” 这正是 {lean}`p ∧ q → r` 的“柯里化”形式。

:::

在上一章中，我们观察到 lambda 抽象可以看作 {lit}`→` 的“引入规则”。在当前语境中，它展示了如何“引入”或确立一个蕴含。应用可以看作“消去规则”，展示了如何在证明中“消去”或使用一个蕴含。其他命题联结词在 Lean 的库中定义，并会自动导入。每个联结词都带有其典范的引入规则和消去规则。

## 合取
%%%
tag := "conjunction"
%%%

:::setup
```
variable (p q : Prop) (h1 : p) (h2 : q)
```
表达式 {lean}`And.intro h1 h2` 使用证明 {lean}`h1 : p` 和 {lean}`h2 : q` 构造 {lean}`p ∧ q` 的一个证明。通常把 {lean}`And.intro` 称为 _and-introduction_（合取引入）规则。在下一个例子中，我们使用 {lean}`And.intro` 创建 {lean}`p → q → p ∧ q` 的一个证明。

:::
```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```
{kw}`example` 命令陈述一个定理，但不给它命名，也不把它存入永久上下文。本质上，它只是检查给定项是否具有所标明的类型。它便于示例说明，我们会经常使用它。

:::setup
```
variable (p q : Prop) (h : p ∧ q)
```
表达式 {lean}`And.left h` 从证明 {lean}`h : p ∧ q` 创建 {lean}`p` 的一个证明。类似地，{lean}`And.right h` 是 {lean}`q` 的一个证明。它们通常称为左、右 _and-elimination_（合取消去）规则。

:::
```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```
现在我们可以用下面的证明项来证明 {lean}`p ∧ q → q ∧ p`。
```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```
:::setup
```
variable (p q : Prop) (hp : p) (hq : q) (α β : Type) (a : α) (b : β)

```
注意，合取引入和合取消去类似于笛卡尔积的配对和投影操作。区别在于，给定 {lean}`hp : p` 和 {lean}`hq : q` 时，{lean}`And.intro hp hq` 具有类型 {lean}`p ∧ q : Prop`；而给定 {lean}`a : α` 和 {lean}`b : β` 时，{lean}`Prod.mk a b` 具有类型 {lean}`α × β : Type`。{lean}`Prod` 不能用于 {lean}`Prop`，{lean}`And` 也不能用于 {lean}`Type`。{lit}`∧` 与 {lit}`×` 之间的相似性是 {tech}[Curry-Howard isomorphism]（Curry-Howard 同构）的又一个实例；但与蕴含和函数空间构造子不同，在 Lean 中 {lit}`∧` 与 {lit}`×` 是分开处理的。不过按照这个类比，我们刚刚构造的证明类似于一个交换有序对两个分量的函数。

我们将在 {ref "structures-and-records"}[结构与记录] 中看到，Lean 中某些类型是 _结构_，也就是说，该类型由一个单一的典范 _构造子_ 定义，它从一列合适的参数构造该类型的一个元素。对于每个 {lean}`p q : Prop`，{lean}`p ∧ q` 就是一个例子：构造元素的典范方式是把 {lean}`And.intro` 应用于合适的参数 {lean}`hp : p` 和 {lean}`hq : q`。当相关类型是归纳类型且可以从上下文推断出来时，Lean 允许我们在这类情形中使用 _匿名构造子_ 记号 {lit}`⟨arg1, arg2, ...⟩`。特别地，我们通常可以写 {lean (type := "p ∧ q")}`⟨hp, hq⟩`，而不写 {lean}`And.intro hp hq`：

:::
```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```
这些尖括号分别通过输入 {kbd}`\<` 和 {kbd}`\>` 获得。

:::setup
```
inductive Foo where | mk
inductive Bar where | mk : Foo → Bar
variable (e : Foo)
def Foo.bar (x : Foo) : Bar := .mk x
```
Lean 提供了另一个有用的语法小工具。给定归纳类型 {lean}`Foo`（可能已应用若干参数）的一个表达式 {lean}`e`，记号 {lean}`e.bar` 是 {lean}`Foo.bar e` 的简写。这提供了一种无需打开命名空间即可方便访问函数的方式。例如，下面两个表达式含义相同：

:::
```lean
variable (xs : List Nat)

#check List.length xs

#check xs.length
```
:::setup
```
variable (p q : Prop) (h : p ∧ q)
```
因此，给定 {lean}`h : p ∧ q`，我们可以写 {lean}`h.left` 表示 {lean}`And.left h`，写 {lean}`h.right` 表示 {lean}`And.right h`。于是，我们可以方便地把上面的示例证明改写如下：

:::
```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```
简洁与晦涩之间只有一线之隔；以这种方式省略信息有时会使证明更难阅读。但对于像上面这样直接的构造，当 {leanRef}`h` 的类型以及构造的目标都很显眼时，这种记号清晰而有效。

像 “And” 这样的构造经常会迭代出现。Lean 还允许你把右结合的嵌套构造子展平，因此下面两个证明是等价的：
```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
```
这也常常很有用。

## 析取
%%%
tag := "disjunction"
%%%

:::setup
```
variable (p q : Prop) (hp : p) (hq : q)
```
表达式 {lean}`Or.intro_left q hp` 从证明 {lean}`hp : p` 创建 {lean}`p ∨ q` 的一个证明。类似地，{lean}`Or.intro_right p hq` 使用证明 {lean}`hq : q` 创建 {lean}`p ∨ q` 的一个证明。它们分别是左、右 _or-introduction_（析取引入）规则。
:::
```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```
:::setup
```
variable (p q r : Prop) (hpq : p ∨ q) (hpr : p → r) (hqr : q → r)
```
_or-elimination_（析取消去）规则稍微复杂一些。其思想是，我们可以通过说明 {lean}`r` 可由 {lean}`p` 推出，并且 {lean}`r` 也可由 {lean}`q` 推出，来从 {lean}`p ∨ q` 证明 {lean}`r`。换言之，这就是分情况证明。在表达式 {lean}`Or.elim hpq hpr hqr` 中，{lean}`Or.elim` 接受三个参数：{lean}`hpq : p ∨ q`、{lean}`hpr : p → r` 和 {lean}`hqr : q → r`，并产生 {lean}`r` 的一个证明。在下面的例子中，我们使用 {lean}`Or.elim` 证明 {lean}`p ∨ q → q ∨ p`。
:::
```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```
在大多数情形中，{lean}`Or.intro_right` 和 {lean}`Or.intro_left` 的第一个参数都可以由 Lean 自动推断。因此 Lean 提供了 {lean}`Or.inr` 和 {lean}`Or.inl`，它们可看作 {lean}`Or.intro_right _` 与 {lean}`Or.intro_left _` 的简写。于是，上面的证明项可以更简洁地写为：
```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```
注意，完整表达式中有足够的信息让 Lean 也推断出 {leanRef}`hp` 和 {leanRef}`hq` 的类型。不过，在较长版本中使用类型标注会使证明更易读，也有助于捕捉和调试错误。

:::setup
```
variable (h : p ∨ q)
```
由于 {lean}`Or` 有两个构造子，我们不能使用匿名构造子记号。但我们仍然可以写 {lean}`h.elim`，而不是 {lean}`Or.elim h`：
:::
```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```
再一次，你应当自行判断这类缩写是增强还是削弱了可读性。

## 否定与假命题
%%%
tag := "negation-and-falsity"
%%%

:::setup
```
variable (p q : Prop) (hnp : ¬ p) (hp : p)
```
否定 {lean}`¬p` 实际上被定义为 {lean}`p → False`，因此我们通过从 {lean}`p` 推导出矛盾来获得 {lean}`¬p`。类似地，表达式 {lean}`hnp hp` 从 {lean}`hp : p` 和 {lean}`hnp : ¬p` 产生 {lean}`False` 的一个证明。下一个例子使用这两条规则来产生 {lean}`(p → q) → ¬q → ¬p` 的一个证明。（符号 {lit}`¬` 可通过输入 {kbd}`\not` 或 {kbd}`\neg` 产生。）

:::
```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```
联结词 {lean}`False` 有一条消去规则 {lean}`False.elim`，它表达了从矛盾可以推出任何事物这一事实。该规则有时称为 _ex falso_（_ex falso sequitur quodlibet_ 的简称），或 _爆炸原理_。
```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```
从假命题推出的任意事实 {lean}`q` 是 {lean}`False.elim` 的一个隐式参数，并会被自动推断。这个模式，即从相互矛盾的假设推出任意事实，非常常见，并由 {lean}`absurd` 表示。
```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```
例如，下面是 {lean}`¬p → q → (q → p) → r` 的一个证明：
```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```
顺便说一句，正如 {lean}`False` 只有一条消去规则，{lean}`True` 也只有一条引入规则 {lean}`True.intro : True`。换言之，{lean}`True` 就是真的，并且有一个典范证明 {lean}`True.intro`。

## 逻辑等价
%%%
tag := "logical-equivalence"
%%%

:::setup
```
variable (p q : Prop) (h1 : p → q) (h2 : q → p) (h : p ↔ q)
```
表达式 {lean}`Iff.intro h1 h2` 从 {lean}`h1 : p → q` 和 {lean}`h2 : q → p` 产生 {lean}`p ↔ q` 的一个证明。表达式 {lean}`Iff.mp h` 从 {lean}`h : p ↔ q` 产生 {lean}`p → q` 的一个证明。类似地，{lean}`Iff.mpr h` 从 {lean}`h : p ↔ q` 产生 {lean}`q → p` 的一个证明。下面是 {lean}`p ∧ q ↔ q ∧ p` 的一个证明：

:::
```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- and_swap p q : p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```
我们可以使用匿名构造子记号，由正向和反向两个方向的证明构造 {lean}`p ↔ q` 的一个证明；也可以对 {lit}`mp` 和 {lit}`mpr` 使用 {lit}`.` 记号。因此，前面的例子可以简洁地写成如下形式：
```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```
# 引入辅助子目标
%%%
tag := "introducing-auxiliary-subgoals"
%%%

这里适合介绍 Lean 提供的另一个有助于组织长证明的工具，即 {kw}`have` 构造，它会在证明中引入一个辅助子目标。下面是一个改编自上一节的小例子：
```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```
:::setup
```
variable (p q : Prop) (s : p) (t : q)
```
在内部，表达式 {lean}`have h : p := s; t` 产生项 {lean}`(fun (h : p) => t) s`。换言之，{lean}`s` 是 {lean}`p` 的一个证明，{lean}`t` 是在假设 {leanRef}`h : p` 下所需结论的一个证明，而二者通过 lambda 抽象和应用组合起来。这个简单工具在组织长证明时极其有用，因为我们可以把中间的 {kw}`have` 作为通向最终目标的踏脚石。
:::

Lean 还支持一种从目标反向推理的结构化方式，它模拟了普通数学中的“只需证明”构造。下一个例子只是调换了前一个证明的最后两行。
```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```
书写 {lit}`suffices hq : q` 会留下两个目标。首先，我们必须通过在额外假设 {lit}`hq : q` 下证明原始目标 {leanRef}`q ∧ p`，来证明“只需证明 {leanRef}`q`”确实足够。最后，我们还必须证明 {leanRef}`q`。

# 经典逻辑
%%%
tag := "classical-logic"
%%%

到目前为止我们看到的引入规则和消去规则都是构造性的，也就是说，它们反映了基于 {tech}[propositions-as-types]（命题即类型）对应对逻辑联结词的计算性理解。通常的经典逻辑在此基础上加入排中律 {lean}`p ∨ ¬p`。要使用这一原则，必须打开 classical 命名空间。
```lean
open Classical

variable (p : Prop)

#check em p
```
:::setup
```
variable (p q RH : Prop)
```
直观地说，构造性的 “Or” 非常强：断言 {lean}`p ∨ q` 等同于知道究竟是哪一种情形。如果 {lean}`RH` 表示 Riemann 假设，经典数学家愿意断言 {lean}`RH ∨ ¬RH`，即使我们还不能断言任一析取支。

:::

排中律的一个推论是双重否定消去原则：
```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```
:::setup
```
open Classical
variable (p : Prop)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```
双重否定消去允许人们通过假设 {lean}`¬p` 并推出 {lean}`False` 来证明任意命题 {lean}`p`，因为这等同于证明 {lean}`¬¬p`。换言之，双重否定消去允许人们进行反证法证明，而这在构造性逻辑中通常是不可能的。作为练习，你可以尝试证明其逆命题，也就是说明 {lean}`em` 可以从 {lean}`dne` 证明。



经典公理还让你能够使用一些可通过诉诸 {lean}`em` 来辩护的额外证明模式。例如，可以进行分情况证明：
:::
```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```
或者，你可以进行反证法证明：
```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```
如果你不习惯构造性地思考，可能需要一些时间才能形成对何处使用了经典推理的感觉。下面的例子需要经典推理，因为从构造性的立场看，知道 {lean}`p` 和 {lean}`q` 不可能同时为真，并不一定告诉你哪一个为假：
```lean
open Classical
variable (p q : Prop)
------
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```
稍后我们会看到，在构造性逻辑中 _确实_ 存在一些情形，其中排中律和双重否定消去这样的原则是可允许的；Lean 支持在这类上下文中使用经典推理，而不依赖排中律。

Lean 用来支持经典推理的完整公理列表将在 {ref "axioms-and-computation"}[公理与计算] 中讨论。

# 命题有效式示例
%%%
tag := "examples-of-propositional-validities"
%%%

:::setup
```
variable (p q r s : Prop)
```
Lean 的标准库包含许多命题逻辑有效陈述的证明，你可以在自己的证明中自由使用它们。下面的列表包括若干常见恒等式。

交换律：

1. {lean}`p ∧ q ↔ q ∧ p`
2. {lean}`p ∨ q ↔ q ∨ p`

结合律：

3. {lean}`(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`
4. {lean}`(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)`

分配律：

5. {lean}`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
6. {lean}`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`

其他性质：

7. {lean}`(p → (q → r)) ↔ (p ∧ q → r)`
8. {lean}`((p ∨ q) → r) ↔ (p → r) ∧ (q → r)`
9. {lean}`¬(p ∨ q) ↔ ¬p ∧ ¬q`
10. {lean}`¬p ∨ ¬q → ¬(p ∧ q)`
11. {lean}`¬(p ∧ ¬p)`
12. {lean}`p ∧ ¬q → ¬(p → q)`
13. {lean}`¬p → (p → q)`
14. {lean}`(¬p ∨ q) → (p → q)`
15. {lean}`p ∨ False ↔ p`
16. {lean}`p ∧ False ↔ False`
17. {lean}`¬(p ↔ ¬p)`
18. {lean}`(p → q) → (¬q → ¬p)`

这些需要经典推理：

19. {lean}`(p → r ∨ s) → ((p → r) ∨ (p → s))`
20. {lean}`¬(p ∧ q) → ¬p ∨ ¬q`
21. {lean}`¬(p → q) → p ∧ ¬q`
22. {lean}`(p → q) → (¬p ∨ q)`
23. {lean}`(¬q → ¬p) → (p → q)`
24. {lean}`p ∨ ¬p`
25. {lean}`(((p → q) → p) → p)`

{lean}`sorry` 标识符会神奇地产生任何命题的证明，或者提供任何数据类型的对象。当然，作为证明方法它是不可靠的——例如，你可以用它证明 {lean}`False`——并且当文件使用或导入依赖它的定理时，Lean 会产生严重警告。但它对于逐步构建长证明非常有用。可以从上到下开始书写证明，用 {lean}`sorry` 填充子证明。确保 Lean 接受包含所有 {lean}`sorry` 的项；如果不接受，就有需要修正的错误。然后回头把每个 {lean}`sorry` 替换为实际证明，直到不再剩下为止。

还有一个有用技巧。除了使用 {lean}`sorry`，你也可以使用下划线 {lit}`_` 作为占位符。回忆一下，这会告诉 Lean 该参数是隐式的，应当自动填入。如果 Lean 尝试这样做但失败，它会返回错误消息 “don't know how to synthesize placeholder”，随后给出它期望的项的类型，以及上下文中所有可用对象和假设。换言之，对于每个未解决的占位符，Lean 都会报告该处需要填充的子目标。随后你可以通过逐步填充这些占位符来构造证明。

:::

作为参考，下面是从上面列表中取出的两个有效式的示例证明。
```lean
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```
# 练习
%%%
tag := "propositions-and-proofs-exercises"
%%%

证明下列恒等式，将 {lean}`sorry` 占位符替换为实际证明。
```lean
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```
证明下列恒等式，将 {lean}`sorry` 占位符替换为实际证明。这些需要经典推理。
```lean
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```
不用经典逻辑证明 {lean}`¬(p ↔ ¬p)`。
