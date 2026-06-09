import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "与 Lean 交互" =>
%%%
tag := "interacting-with-lean"
file := "Interacting-with-Lean"
%%%

你现在已经熟悉了依赖类型论的基础：它既是一种定义数学对象的语言，
也是一种构造证明的语言。你目前还缺少的一点，是一种定义新数据类型
的机制。我们将在下一章填补这一空白，届时将引入*归纳数据类型*这一概念。
不过在此之前，本章先暂时离开类型论的机制性内容，转而探讨一些与 Lean
交互时更具实践性的方面。

这里给出的信息并不一定都会立刻对你有用。我们建议你先快速浏览本节，
对 Lean 的特性形成整体印象，然后在需要时再回来查阅。

# 消息
%%%
tag := "messages"
%%%

Lean 会产生三类消息：

: 错误

  当代码中存在不一致、导致其无法被处理时，就会产生错误。例如，
  语法错误（如缺少 {lit}`)`）以及类型错误（例如试图把一个自然数与函数相加）。

: 警告

  警告描述的是代码中潜在的问题，例如出现了 {lean}`sorry`。
  与错误不同，这并不意味着代码毫无意义；不过，警告同样值得认真对待。

: 信息

  信息并不表示代码存在问题，其中包括 {kw}`#check`、{kw}`#eval`
  等命令的输出。

Lean 可以检查某条命令是否产生了预期的消息。如果消息匹配，
那么其中的错误会被忽略；这可用于确保出现的正是我们想要的错误。
如果不匹配，则会再产生一个错误。你可以使用 {kw}`#guard_msgs`
命令来说明哪些消息是预期的。

下面是一个例子：
```lean
/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def x : Nat := "Not a number"
```

:::leanFirst
在 {leanRef}`#guard_msgs` 后面的括号中写入消息类别时，它只会检查
指定的类别，而让其他消息照常显示。在这个例子中，{leanRef}`#eval`
由于存在 {lean}`sorry` 而发出错误，但针对 {lean}`sorry` 总会产生的警告
仍会像往常一样显示出来：
```lean
/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs(error) in
#eval (sorry : Nat)
```
:::

如果不作这样的配置，两条消息都会被捕获：
```lean
/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
#eval (sorry : Nat)
```

本书中的一些例子会使用 {leanRef}`#guard_msgs` 来标明预期出现的错误。

# 导入文件
%%%
tag := "importing-files"
%%%

Lean 前端的目标是解释用户输入、构造形式化表达式，并检查它们是否
良构且类型正确。Lean 还支持多种编辑器，它们能够提供持续的检查与反馈。
更多信息可参见 Lean 的[文档页面](https://lean-lang.org/documentation/)。

Lean 标准库中的定义和定理分散在多个文件中。用户也可能希望使用额外的
库，或者在多个文件中开发自己的项目。Lean 启动时，会自动导入库
{lit}`Init` 文件夹中的内容，其中包含若干基础定义与构造。因此，
我们在这里给出的多数例子都可以“开箱即用”。

不过，如果你想使用额外的文件，就需要在文件开头通过 {kw}`import`
语句手动导入。命令

> {kw}`import`{lit}` Bar.Baz.Blah`


会导入文件 {lit}`Bar/Baz/Blah.olean`，其中这些描述是相对于 Lean 的
*搜索路径* 来解释的。关于搜索路径如何确定，可参见
[文档页面](https://lean-lang.org/documentation/)。默认情况下，
它包括标准库目录，以及（在某些上下文中）用户本地项目的根目录。

导入具有传递性。换言之，如果你导入 {lit}`Foo`，而 {lit}`Foo` 又导入了
{lit}`Bar`，那么你也可以访问 {lit}`Bar` 的内容，无需再显式导入它。

# 关于节的更多说明
%%%
tag := "more-on-sections"
%%%

Lean 提供了多种分节机制来帮助组织理论结构。你已经在
{ref "variables-and-sections"}[变量与节]中看到，{kw}`section` 命令不仅可以将
彼此相关的理论内容组织在一起，还可以声明变量，并在需要时将它们自动插入为
定理和定义的参数。请记住，{kw}`variable` 命令的用途是为定理声明待用变量，
如下例所示：

```lean
section
variable (x y : Nat)

def double := x + x

#check double y

#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y

#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

{leanRef}`double` 的定义不必显式将 {leanRef}`x` 声明为参数；Lean 会检测到
这种依赖关系并自动插入它。同样，Lean 也会检测 {leanRef}`t1` 与 {leanRef}`t2`
中 {leanRef}`x` 的出现，并在那里自动插入该参数。注意，{leanRef}`double`
并*不会*把 {leanRef}`y` 当作参数。变量只会被加入到那些实际使用了它们的声明中。

# 关于命名空间的更多说明
%%%
tag := "more-on-namespaces"
%%%

在 Lean 中，标识符由层级化的*名称*给出，例如 {lit}`Foo.Bar.baz`。我们已经在
{ref "namespaces"}[命名空间]中看到，Lean 提供了处理层级名称的机制。命令
{kw}`namespace`{lit}` Foo` 会在每个定义和定理的名称前加上 {lit}`Foo`，
直到遇到 {kw}`end`{lit}` Foo` 为止。随后，命令 {kw}`open`{lit}` Foo`
会为那些以 {lit}`Foo` 为前缀的定义和定理创建临时的*别名*。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar

#check Foo.bar
```

下面这个定义

```lean
def Foo.bar : Nat := 1
```

会被当作一个宏，并展开为

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

虽然定理和定义的名称必须唯一，但用于引用它们的别名却不必如此。当我们打开
一个命名空间时，某个标识符可能会变得有歧义。Lean 会尝试利用类型信息在上下文中
消解歧义，但你始终可以通过给出全名来明确所指。为此，字符串 {lit}`_root_`
就是空前缀的显式写法。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String

-- This reference is ambiguous:
-- #check add

#check String.add           -- String.add (a b : String) : String

#check Bool.add             -- Bool.add (a b : Bool) : Bool

#check _root_.add           -- _root_.add (α β : Type) : Type

#check add "hello" "world"  -- "hello".add "world" : String

#check add true false       -- true.add false : Bool

#check add Nat Nat          -- _root_.add Nat Nat : Type
```

我们可以使用 {kw}`protected` 关键字来阻止创建这种较短的别名：

```lean
protected def Foo.bar : Nat := 1

open Foo

/-- error: Unknown identifier `bar` -/
#guard_msgs in
#check bar -- error

#check Foo.bar
```

这种做法经常用于 {name}`Nat.rec` 和 {name}`Nat.recOn` 之类的名称，
以避免常见名称发生重载。

{leanRef}`open` 命令还有若干变体。命令

```lean
open Nat (succ zero gcd)

#check zero     -- Nat.zero : Nat

#eval gcd 15 6  -- 3
```

只会为列出的标识符创建别名。命令

```lean
open Nat hiding succ gcd

#check zero     -- Nat.zero : Nat

/-- error: Unknown identifier `gcd` -/
#guard_msgs in
#eval gcd 15 6  -- error

#eval Nat.gcd 15 6  -- 3
```

会为 {lit}`Nat` 命名空间中除所列标识符*之外*的所有内容创建别名。

```lean
open Nat renaming mul → times, add → plus

#eval plus (times 2 2) 3  -- 7
```

会创建别名，并将 {lean}`Nat.mul` 重命名为 {leanRef}`times`，将
{lean}`Nat.add` 重命名为 {leanRef}`plus`。

有时，把别名从一个命名空间 {kw}`export` 到另一个命名空间，或导出到顶层，
会很有用。命令

```lean
export Nat (succ add sub)
```

会在当前命名空间中为 {leanRef}`succ`、{leanRef}`add` 和 {leanRef}`sub`
创建别名，因此只要该命名空间被打开，这些别名就可用。如果在命名空间之外
使用此命令，那么这些别名会被导出到顶层。

# 属性
%%%
tag := "attributes"
%%%

Lean 的主要功能是将用户输入翻译为形式化表达式，由内核检查其正确性，
然后存入环境中以备后用。但有些命令还会对环境产生其他影响，例如为环境中的对象
赋予属性、定义记法，或者像 {ref "type-classes"}[类型类]一章中所述那样，
声明类型类的实例。这些命令大多具有全局效果，也就是说，它们不仅在当前文件中生效，
在任何导入该文件的文件中也继续生效。不过，这类命令通常支持 {kw}`local`
修饰符，表示它们只在当前 {kw}`section` 或 {leanRef}`namespace` 关闭之前，
或直到当前文件结束之前生效。

在 {ref "using-the-simplifier"}[使用化简器]中，我们看到可以用 {attr}`[simp]`
属性来标注定理，从而使化简器能够使用它们。下面的例子在列表上定义了前缀关系，
证明该关系是自反的，并把 {attr}`[simp]` 属性赋给这个定理。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

随后，化简器会通过把 {leanRef}`isPrefix [1, 2, 3] [1, 2, 3]` 重写成
{lean}`True` 来证明它。

也可以在定义完成后的任意时刻再赋予该属性：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

在上述所有情形中，该属性都会在任何导入此声明所在文件的文件中继续生效。
加入 {kw}`local` 修饰符则会限制其作用域：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

/-- error: `simp` made no progress -/
#guard_msgs in
example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

:::leanFirst
再举一个例子，我们可以使用 {kw}`instance` 命令，把记号 {lit}`≤`
赋给关系 {leanRef}`isPrefix`。这个命令将在 {ref "type-classes"}[类型类]
一章中解释；它的工作方式是给相关定义赋予一个 {attr}`[instance]` 属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

:::

这种赋值同样也可以局部化：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
------
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

/--
error: failed to synthesize instance of type class
  LE (List α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

在下面的 {ref "notation"}[记法] 一节中，我们将讨论 Lean 定义记法的机制，
并看到它们也支持 {kw}`local` 修饰符。不过，在 {ref "setting-options"}[设置选项]
一节中，我们将讨论 Lean 设置选项的机制；这一点*并不*遵循上述模式：
选项*只能*局部设置，也就是说，它们的作用域总是限制在当前节或当前文件内。

# 关于隐式参数的更多说明
%%%
tag := "more-on-implicit-arguments"
%%%

:::setup

```
variable (α : Type u) (β : α → Type v) (t : {x : α} → β x)
```


在 {ref "implicit-arguments"}[隐式参数] 中，我们看到，如果 Lean 将某个项
{lean}`t` 的类型显示为 {lean}`{x : α} → β x`，那么花括号表示 {leanRef}`x`
已被标记为 {lean}`t` 的一个*隐式参数*。这意味着，每当你写下 {lean}`t` 时，
都会自动插入一个占位符，也就是“洞”，从而把 {lean}`t` 替换为 {lean}`@t _`。
如果你不希望发生这种情况，就必须改写成 {lean}`@t`。
:::


:::setup
```
def f (x : Nat) {y : Nat} (z : Nat) : Nat := x + y + z
-- Equivalent:
example := f 7
example := @f 7 _
```

请注意，隐式参数会被急切地插入。假设我们定义了一个函数
{lean}`f : (x : Nat) → {y : Nat} → (z : Nat) → Nat`。那么，当我们在没有提供
更多参数的情况下写表达式 {lean}`f 7` 时，它会被解析为 {lean}`@f 7 _`。
:::

:::setup
```
def f (x : Nat) {{y : Nat}} (z : Nat) : Nat := x + y + z
-- Just f 7
example := f 7
-- These are equivalent:
example := @f 7 _ 3
example := f 7 3
-- Alternative syntax:
def f' (x : Nat) ⦃y : Nat⦄ (z : Nat) : Nat := x + y + z
```

Lean 还提供了一种更弱的标注，用来说明：只有在后面紧跟显式参数*之前*，
才应插入占位符。它可以写作双花括号，因此 {lean}`f` 的类型可写为
{lean}`f : (x : Nat) → {{y : Nat}} → (z : Nat) → Nat`。使用这种标注时，
表达式 {lean}`f 7` 会按原样解析，而 {lean}`f 7 3` 则会像使用强标注时一样，
被解析为 {lean}`@f 7 _ 3`。这种标注也可以写成 {lit}`⦃y : Nat⦄`，
其中 Unicode 括号分别通过 {kbd}`\{{` 与 {kbd}`\}}` 输入。
:::


为了说明这种差异，请看下面的例子，它表明：一个自反且欧几里得的关系
同时也是对称的和传递的。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr
```

这个结果被分解成若干小步骤：{leanRef}`th1` 说明一个既自反又欧几里得的关系
是对称的，而 {leanRef}`th2` 说明一个既对称又欧几里得的关系是传递的。
随后，{leanRef}`th3` 将这两个结果组合起来。不过请注意，我们必须手动禁用
{leanRef}`euclr` 中的隐式参数，否则会插入过多的隐式参数。如果改用弱隐式参数，
这个问题就会消失：

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr  -- euclr : Euclidean r
```

还有第三种隐式参数，用方括号 {lit}`[` 与 {lit}`]` 表示。它们用于类型类，
这将在 {ref "type-classes"}[类型类] 一章中说明。

# 记法
%%%
tag := "notation"
%%%

Lean 中的标识符可以包含任意字母数字字符，也包括希腊字母（除了
∀、Σ 和 λ，它们如我们所见，在依赖类型论中具有特殊含义）。
标识符还可以包含下标；输入方法是先键入 {kbd}`\_`，再输入所需的下标字符。

Lean 的解析器是可扩展的，也就是说，我们可以定义新的记法。

Lean 的语法可以由用户在各个层次上进行扩展和定制，范围从基础的
“mixfix” 记法一直到自定义精化器。事实上，所有内建语法也都是通过同样
面向用户开放的机制和 API 来解析和处理的。本节将介绍并解释这些不同的扩展点。

在编程语言中，引入新记法是一项相对少见的特性，有时甚至会因为可能使代码
晦涩而不受欢迎。然而在形式化工作中，它却是一种极其宝贵的工具，能够让相应领域
中已经约定俗成的符号与记法以简洁的方式体现在代码里。更进一步地，除了基础记法外，
Lean 还能把常见样板代码抽象成行为良好的宏，并嵌入完整的自定义领域特定语言
（DSL），以高效且可读的文本形式编码子问题；这对程序员和证明工程师都大有裨益。

## 记法与优先级
%%%
tag := "notations-and-precedence"
%%%

最基础的语法扩展命令允许我们引入新的（或重载已有的）前缀、中缀和后缀运算符。

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => Inv.inv
```

在描述运算符种类（即其“{deftech}[fixity]”）的命令名之后，我们先给出运算符的
*解析优先级*，其前面带一个冒号 {lit}`:`；然后写上用双引号括起来的新 token
或已有 token（其中的空格用于美观输出）；最后在箭头 {lit}`=>` 后写出该运算符
应被翻译成的函数。

优先级是一个自然数，用来描述运算符与其参数结合得有多“紧”，也即编码了
运算顺序。通过观察上述命令展开后的形式，我们可以更精确地理解这一点：

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
 -- `max` is a shorthand for precedence 1024:
notation:1024 arg:1024 "⁻¹" => Inv.inv arg
```

:::setup
```
variable {p : Nat} {a b c : α} [Add α] [Pow α α]
```
事实证明，第一个代码块中的所有命令实际上都是命令*宏*，会被翻译为更通用的
{leanRef}`notation` 命令。我们稍后会学习如何编写这样的宏。{leanRef}`notation`
命令不只接受单个 token，而是接受由 token 与带优先级的具名项占位符交错组成的序列；
这些占位符可以在 {lit}`=>` 右侧被引用，并替换为该位置解析得到的相应项。
优先级为 {lean}`p` 的占位符，在该位置只接受优先级至少为 {lean}`p` 的记法。
因此，字符串 {lean}`a + b + c` 不能被解析为 {lean}`a + (b + c)`，因为
{leanRef}`infixl` 记法右侧操作数的优先级比该记法自身高 1。相对地，
{leanRef}`infixr` 会把该记法自身的优先级复用于右侧操作数，因此
{lean}`a ^ b ^ c` *可以*被解析为 {lean}`a ^ (b ^ c)`。注意，如果我们直接用
{leanRef}`notation` 来引入如下的中缀记法
:::

```lean
def wobble : α → β → γ := sorry
------
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

:::setup
```
variable (a : α) (b : β) (c : γ)
def wobble : α → β → γ := sorry
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs

```

在这种优先级不足以充分决定结合性的情形下，Lean 的解析器默认采用右结合。
更准确地说，当语法存在歧义时，Lean 的解析器遵循局部的*最长解析*规则：
在解析 {lit}`a ~ b ~ c` 中 {lit}`a ~` 的右侧时，只要当前优先级允许，
它就会尽可能继续向后解析，不会在 {leanRef}`b` 处停止，而会把 {lit}`~ c`
也一并解析进去。因此，该项等价于 {lean}`a ~ (b ~ c)`。
:::

如上所述，{leanRef}`notation` 命令允许我们自由地混合 token 与占位符，
从而定义任意的 *mixfix* 语法。

```lean
set_option quotPrecheck false
------
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

未标注优先级的占位符默认使用 {lit}`0`，也就是说，它们在自身位置上接受任意
优先级的记法。如果两个记法发生重叠，我们仍然应用最长解析规则：

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

这里会优先选择新的记法，而不是二元记法，因为后者在形成链式解析之前，
会在 {leanRef}`1 + 2` 之后就停止。如果有多个记法都接受同样的最长解析，
那么最终选择会延迟到精化阶段；除非恰好只有一个重载在类型上是正确的，
否则精化就会失败。

# 强制转换
%%%
tag := "coercions"
%%%

在 Lean 中，自然数类型 {lean}`Nat` 与整数类型 {lean}`Int` 是不同的。
不过，存在一个函数 {lean}`Int.ofNat`，它把自然数嵌入到整数中，这意味着
在需要时我们可以把任意自然数看作一个整数。Lean 具有检测并插入这类
*强制转换* 的机制。我们也可以用重载的 {lit}`↑` 运算符显式请求强制转换。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + ↑m : Int

#check i + m + j  -- i + ↑m + j : Int

#check i + m + n  -- i + ↑m + ↑n : Int
```

# 显示信息
%%%
tag := "displaying-information"
%%%

你可以通过多种方式向 Lean 查询其当前状态，以及当前上下文中可用的对象与定理。
你已经见过其中最常见的两种，即 {kw}`#check` 和 {kw}`#eval`。请记住，
{kw}`#check` 经常与 {lit}`@` 运算符配合使用，后者会把定理或定义的所有参数都
显式写出。此外，你还可以使用 {kw}`#print` 命令获取任意标识符的信息。
如果该标识符表示一个定义或定理，Lean 会打印该符号的类型及其定义；
如果它是常量或公理，Lean 会说明这一点，并显示它的类型。

```lean
-- examples with equality
#check Eq

#check @Eq

#check Eq.symm

#check @Eq.symm

#print Eq.symm

-- examples with And
#check And

#check And.intro

#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo

#check @foo

#print foo
```

# 设置选项
%%%
tag := "setting-options"
%%%

Lean 维护着若干内部变量，用户可以设置它们来控制 Lean 的行为。
其语法如下：


{kw}`set_option`{lit}` <name> <value>`


有一类非常有用的选项用于控制 Lean 的*美观打印器*如何显示项。
下面这些选项都接受 true 或 false 作为输入：

```
pp.explicit  : 显示隐式参数
pp.universes : 显示隐藏的宇宙参数
pp.notation  : 使用已定义的记法显示输出
```

例如，下面的设置会产生长得多的输出：

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4

#reduce (fun x => x + 2) = (fun x => x + 3)

#check (fun x => x + 1) 1
```

命令 {leanCommand}`set_option pp.all true` 会一次性启用这些设置，
而 {leanCommand}`set_option pp.all false` 则会恢复到先前的取值。
在调试证明、或者试图理解晦涩的错误信息时，打印更多附加信息往往非常有用。
不过，信息过多也可能令人不堪重负，而 Lean 的默认设置通常已足以应对日常交互。

:::comment
```
<!--
# 精化提示

当你要求 Lean 处理形如 `λ x y z, f (x + y) z` 的表达式时，你实际上把一些信息留成了隐式的。比如，`x`、`y` 和 `z` 的类型必须从上下文中推断出来，记号 `+` 可能存在重载，而 `f` 也可能带有需要自动补全的隐式参数。此外，我们将在 :numref:`Chapter %s <type_classes>` 中看到，有些隐式参数是通过一种称为*类型类解析*的过程综合出来的。并且我们在上一章已经见过，表达式的某些部分还可以由 tactic 框架构造出来。

推断某些隐式参数是很直接的。例如，设函数 `f` 的类型为 `Π {α : Type*}, α → α → α`，而 Lean 正在解析表达式 `f n`，其中 `n` 可以被推断为类型 `nat`。那么很明显，隐式参数 `α` 必须是 `nat`。然而，有些推断问题是*高阶*的。例如，相等性的替换运算 `eq.subst` 具有如下类型：

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

现在假设给定 `a b : ℕ`、`h₁ : a = b` 以及 `h₂ : a * b > a`。那么，在表达式 `eq.subst h₁ h₂` 中，`P` 可以是下面任意一个：

-  `λ x, x * b > x`
-  `λ x, x * b > a`
-  `λ x, a * b > x`
-  `λ x, a * b > a`

换言之，我们的意图可能是替换 `h₂` 中第一个 `a`、第二个 `a`、两个都替换，或者一个也不替换。在推断归纳谓词或函数参数时，也会出现类似的歧义。甚至二阶统一本身就已知是不可判定的。因此，Lean 只能依赖启发式方法来补全这类参数；当它无法猜到正确结果时，就需要我们显式提供。

更糟的是，有时需要展开定义，有时又需要按照底层逻辑框架的计算规则对表达式进行约化。Lean 仍然只能依靠启发式方法来决定何时展开、何时约化，以及展开或约化哪些内容。

不过，也有一些属性可以为精化器提供提示。其中一类属性决定定义会被多积极地展开：常量可以被标记为 `[reducible]`、`[semireducible]` 或 `[irreducible]`。定义默认带有 `[semireducible]` 标记。若一个定义带有 `[reducible]` 属性，它就会被积极展开；如果你把一个定义看作缩写，那么这通常是合适的属性。精化器会避免展开带有 `[irreducible]` 属性的定义。定理默认带有 `[irreducible]` 属性，因为证明通常与精化过程无关。

值得强调的是，这些属性只是给精化器的提示。当 Lean 的内核检查一个已经精化完毕的项是否正确时，它会展开一切为完成检查所必需展开的定义。与其他属性一样，上述属性也可以配合 `local` 修饰符使用，使其只在当前节或当前文件内生效。

Lean 还有一组属性用于控制精化策略。一个定义或定理可以被标记为 `[elab_with_expected_type]`、`[elab_simple]` 或 `[elab_as_eliminator]`。当它们作用于定义 `f` 时，会影响形如 `f a b c ...` 这一应用表达式的精化方式。在默认属性 `[elab_with_expected_type]` 下，参数 `a`、`b`、`c` 等会利用由 `f` 及先前参数推断出的预期类型信息来精化。相较之下，使用 `[elab_simple]` 时，参数会从左到右精化，而不会传播关于其类型的信息。最后一个属性 `[elab_as_eliminator]` 常用于递归子、归纳原理以及 `eq.subst` 之类的消去子。它会使用另一套启发式方法来推断高阶参数。我们将在下一章更详细地讨论这类操作。

同样地，这些属性都可以在对象定义完成之后再被赋予或重新赋予，你也可以使用 `local` 修饰符来限制它们的作用域。此外，在表达式中把 `@` 符号放在某个标识符前面，会指示精化器采用 `[elab_simple]` 策略；其思想是：既然你已经把那些棘手的参数显式写出来了，就希望精化器更重视这些信息。实际上，Lean 还提供了另一种标注 `@@`，它会让第一个高阶参数之前的参数继续保持隐式。例如，`@@eq.subst` 会让等式的类型保持隐式，但会把替换所处的上下文显式写出。
-->
```
:::

# 使用库
%%%
tag := "using-the-library"
%%%

要高效地使用 Lean，你不可避免地需要借助库中的定义和定理。回想一下，
文件开头的 {kw}`import` 命令会导入其他文件中先前编译好的结果，而且导入具有传递性；
如果你导入 {lit}`Foo`，而 {lit}`Foo` 又导入了 {lit}`Bar`，那么来自 {lit}`Bar`
的定义和定理也会对你可用。不过，打开命名空间这件事——也就是获得较短名称——
并不会随导入自动延续。在每个文件中，你都需要显式打开自己想使用的命名空间。

总的来说，熟悉这个库及其内容非常重要，这样你才能知道有哪些定理、定义、
记法和资源可供使用。下面我们会看到，Lean 的编辑器模式也可以帮助你找到所需内容，
但直接研究库本身的内容往往仍然不可避免。Lean 的标准库可以在 GitHub 上在线查看：

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)


你可以通过 GitHub 的浏览器界面查看这些目录和文件的内容。如果你已经在自己的计算机上
安装了 Lean，那么可以在 {lit}`lean` 文件夹中找到这个库，并用文件管理器浏览它。
每个文件顶部的注释头还提供了更多信息。

Lean 的库开发者遵循一套通用的命名准则，以便你更容易猜出所需定理的名称，
或者在支持此功能的 Lean 编辑器模式中利用 Tab 补全来找到它——下一节会讨论这一点。
标识符通常采用 {lit}`camelCase`，类型采用 {lit}`CamelCase`。至于定理名，
我们倾向于使用描述性的名称，并用 {lit}`_` 将不同部分分隔开来。很多时候，
定理的名字本身就直接描述了其结论：

```lean
#check Nat.succ_ne_zero

#check Nat.zero_add

#check Nat.mul_one

#check Nat.le_of_succ_le_succ
```

:::setup
```
open Nat
```

请记住，Lean 中的标识符可以组织在层级化的命名空间中。例如，命名空间
{lean}`Nat` 中名为 {lit}`le_of_succ_le_succ` 的定理，其全名是
{lean}`Nat.le_of_succ_le_succ`；但通过命令 {kw}`open`{lit}` Nat`
（对未标记为 {kw}`protected` 的名称而言），我们可以使用较短的名字。
我们会在 {ref "inductive-types"}[归纳类型] 和
{ref "structures-and-records"}[结构与记录] 两章中看到，在 Lean 中定义结构和
归纳数据类型时，会自动生成相关操作；这些操作被存放在一个与所定义类型同名的
命名空间中。例如，积类型附带了如下操作：
:::

```lean
#check @Prod.mk

#check @Prod.fst

#check @Prod.snd

#check @Prod.rec
```

第一个用于构造一个序对，接下来的两个 {leanRef}`Prod.fst` 与
{leanRef}`Prod.snd` 则分别投影出这两个分量。最后的 {leanRef}`Prod.rec`
提供了另一种在积类型上定义函数的机制：它把问题归结为在两个分量上的一个函数。
像 {leanRef}`Prod.rec` 这样的名称是 *protected* 的，这意味着即使打开了
{lit}`Prod` 命名空间，也必须使用它们的全名。

按照“命题即类型”的对应，逻辑联结词也都是归纳类型的实例，因此我们也倾向于对它们
使用点记法：

```lean
#check @And.intro

#check @And.casesOn

#check @And.left

#check @And.right

#check @Or.inl

#check @Or.inr

#check @Or.elim

#check @Exists.intro

#check @Exists.elim

#check @Eq.refl

#check @Eq.subst
```

# 自动绑定的隐式参数
%%%
tag := "auto-bound-implicit-arguments"
%%%

:::leanFirst
在上一节中，我们已经展示了隐式参数如何让函数使用起来更方便。
然而，像 {leanRef}`compose` 这样的函数在定义时仍然相当冗长。请注意，
带宇宙多态的 {leanRef}`compose` 比我们先前定义的版本还要更冗长。

```lean
universe u v w

def compose {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

:::leanFirst
在定义 {leanRef}`compose` 时显式给出宇宙参数，就可以避免使用 {kw}`universe`
命令。

```lean
def compose.{u, v, w}
    {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

::::leanFirst
Lean 4 支持一项名为*自动绑定的隐式参数*的新特性。它使得编写
{leanRef}`compose` 这样的函数方便得多。当 Lean 处理一个声明的头部时，
任何未绑定的标识符都会自动被加入为隐式参数。有了这一特性，我们可以把
{leanRef}`compose` 写成

:::TODO

更新并检查细节

:::

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose -- @compose : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

注意，Lean 在这里推断出了一个更一般的类型，使用的是 {lean}`Sort`
而不是 {leanRef}`Type`。
::::

尽管我们非常喜欢这一特性，并且在实现 Lean 时大量使用它，但我们也意识到，
有些用户可能会对此感到不适。因此，你可以使用命令
{leanCommand}`set_option autoImplicit false` 将其关闭。

```lean
set_option autoImplicit false

/--
error: Unknown identifier `β`

Note: It is not possible to treat `β` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
---
error: Unknown identifier `γ`

Note: It is not possible to treat `γ` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
---
error: Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
---
error: Unknown identifier `β`

Note: It is not possible to treat `β` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
---
error: Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
---
error: Unknown identifier `γ`

Note: It is not possible to treat `γ` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

# 隐式 lambda 抽象
%%%
tag := "implicit-lambdas"
%%%

:::TODO
在考据完成后更新这段文字
:::

:::leanFirst
当一个表达式的预期类型是一个尚在等待隐式参数的函数时，精化器会自动引入
相应的 lambda。例如，{leanRef}`pure` 的类型表明其第一个参数是一个隐式类型
{leanRef}`α`，但 {leanRef}`ReaderT.pure` 的第一个参数却是 Reader 单子的上下文类型
{leanRef}`ρ`。系统会自动在它外层加上一层 {kw}`fun`{lit}` {α} => ...`，
从而使精化器能够在函数体中正确填充隐式参数。

```lean
variable (ρ : Type) (m : Type → Type) [Monad m]
------
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```
:::

用户可以通过使用 {lit}`@`，或者书写带有 {lit}`{}` 或 {lit}`[]`
绑定标注的 lambda 表达式，来禁用隐式 lambda 特性。下面是几个例子：

```lean
set_option linter.unusedVariables false
namespace Ex2
------
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before {kw}`fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
------
end Ex2
```

# 简单函数的语法糖
%%%
tag := "sugar-for-simple-functions"
%%%

Lean 提供了一种用于描述简单函数的记法，它使用匿名占位符而不是 {kw}`fun`。
当 {lit}`·` 作为某个项的一部分出现时，离它最近的一对外围括号就会变成一个函数，
并把 {lit}`·` 作为它的参数。如果同一对括号中包含多个占位符，且它们之间没有其他
中间括号，那么这些占位符会按从左到右的顺序依次成为参数。下面是一些例子：

```lean
namespace Ex3
------
#check (· + 1) -- fun x => x + 1 : Nat → Nat

#check (2 - ·) -- fun x => 2 - x : Nat → Nat

#eval [1, 2, 3, 4, 5].foldl (· * ·) 1 -- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·) -- fun x1 x2 => f x1 1 x2 : Nat → Nat → Nat

#eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- [1, 3, 5]
------
end Ex3
```

嵌套括号会引入新的函数。在下面这个例子中，会创建两个不同的 lambda 表达式：

```lean
#check (Prod.mk · (· + 1)) -- fun x => (x, fun x => x + 1) : ?m.2 → ?m.2 × (Nat → Nat)
```

# 命名参数
%%%
tag := "named-arguments"
%%%

命名参数让你可以通过参数名而不是参数列表中的位置，来为某个形参指定实参。
如果你不记得参数的顺序，但知道它们的名字，就可以按任意顺序传入实参。
当 Lean 无法推断某个隐式参数时，你也可以借此显式提供它的值。命名参数还能通过
明确每个参数所代表的含义，提升代码的可读性。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop}
    (h₁ : p a b b) (h₂ : b = a) :
    p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

在下面的例子中，我们将说明命名参数与默认参数之间的相互作用。

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

你可以使用 {lit}`..` 把缺失的显式参数统一补成 {lit}`_`。
这一特性与命名参数结合起来，在编写模式时非常有用。下面是一个例子：

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

当显式参数可以由 Lean 自动推断，而我们又希望避免写出一串 {lit}`_` 时，
省略号同样也很有用。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
