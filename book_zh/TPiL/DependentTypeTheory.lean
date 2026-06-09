import VersoManual

import TPiL.Examples

open TPiL

open Verso.Genre Manual

#doc (Manual) "依赖类型论" =>
%%%
tag := "dependent-type-theory"
file := "Dependent-Type-Theory"
htmlSplit := .never
%%%

依赖类型论是一种强大而富有表现力的语言，使你能够表达复杂的数学断言，
编写复杂的硬件与软件规约，并以自然且统一的方式对二者进行推理。
Lean 基于依赖类型论的一个版本，即_构造演算_，并带有可数的、
非累积宇宙层级以及归纳类型。到本章结束时，你将理解这些说法的大部分含义。

# 简单类型论
%%%
tag := "simple-type-theory"
%%%

“类型论”之所以得名，是因为每个表达式都有一个相关联的_类型_。
例如，在给定上下文中，{lit}`x + 0` 可以表示一个自然数，
而 {lit}`f` 可以表示自然数上的一个函数。对于偏好精确定义的读者，
Lean 中的自然数是任意精度的无符号整数。

下面给出一些示例，说明如何在 Lean 中声明对象并检查它们的类型。

```lean
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- m : Nat
#check n
#check n + 0        -- n + 0 : Nat
#check m * (n + 0)  -- m * (n + 0) : Nat
#check b1           -- b1 : Bool
-- "&&" is the Boolean and
#check b1 && b2     -- b1 && b2 : Bool
-- Boolean or
#check b1 || b2     -- b1 || b2 : Bool
-- Boolean "true"
#check true         -- Bool.true : Bool

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

位于 {lit}`/-` 和 {lit}`-/` 之间的任何文本构成一个注释块，Lean 会忽略它。
类似地，两个短横线 {lean}`--` 表明该行余下部分是注释，也会被忽略。
注释块可以嵌套，因此可以像许多编程语言中那样将一大段代码“注释掉”。

{kw}`def` 关键字在工作环境中声明新的常量符号。在上面的示例中，
{leanRef}`def m : Nat := 1` 定义了一个新的常量 {leanRef}`m`，
其类型为 {lean}`Nat`，值为 {leanRef}`1`。{kw}`#check` 命令要求 Lean
报告它们的类型；在 Lean 中，查询系统信息的辅助命令通常以井号 (#) 开头。
{kw}`#eval` 命令要求 Lean 对给定表达式求值。你应当自己尝试声明一些常量，
并对若干表达式做类型检查。以这种方式声明新对象，是试验该系统的一种好方法。

:::setup
```
variable (a b : Type)
```
简单类型论的强大之处在于，你可以由已有类型构造新类型。例如，
若 {lean}`a` 和 {lean}`b` 是类型，则 {lean}`a -> b` 表示从 {lean}`a`
到 {lean}`b` 的函数类型，而 {lean}`a × b` 表示由一个 {lean}`a` 的元素
与一个 {lean}`b` 的元素配对而成的类型，也称为_笛卡尔积_。注意，
{lit}`×` 是一个 Unicode 符号。审慎使用 Unicode 可以提高可读性，
所有现代编辑器也都很好地支持它。在 Lean 标准库中，你经常会看到用希腊字母表示类型，
并用 Unicode 符号 {lit}`→` 作为 {lit}`->` 的更紧凑写法。
:::

```lean (check := false)
#check Nat → Nat      -- type the arrow as “\to” or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"
```
```lean
#check Nat.succ     -- Nat.succ (n : Nat) : Nat
#check (0, 1)       -- (0, 1) : Nat × Nat
#check Nat.add      -- Nat.add : Nat → Nat → Nat

#check Nat.succ 2   -- Nat.succ 2 : Nat
#check Nat.add 3    -- Nat.add 3 : Nat → Nat
#check Nat.add 5 2  -- Nat.add 5 2 : Nat
#check (5, 9).1     -- (5, 9).fst : Nat
#check (5, 9).2     -- (5, 9).snd : Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

同样，你应当自己尝试一些示例。

我们来看一些基本语法。你可以通过输入 {kbd}`\to`、{kbd}`\r` 或 {kbd}`\->`
来输入 Unicode 箭头 {lit}`→`。也可以使用 ASCII 替代写法 {lit}`->`，
因此表达式 {lean}`Nat -> Nat` 与 {lean}`Nat → Nat` 含义相同。
二者都表示以自然数为输入并以自然数为输出的函数类型。
笛卡尔积的 Unicode 符号 {lit}`×` 可通过 {kbd}`\times` 输入。
通常会用小写希腊字母，如 {lit}`α`、{lit}`β` 和 {lit}`γ`，在类型上取值。
这些特定字母可分别通过 {kbd}`\a`、{kbd}`\b` 和 {kbd}`\g` 输入。

::::setup
```
variable (α β : Type) (f : α → β) (x : α) (m n : Nat) (p : Nat × Nat)
```
这里还有几点需要注意。首先，将函数 {lean}`f` 应用于值 {lean}`x`，
记作 {lean}`f x`（例如 {lean}`Nat.succ 2`）。其次，在书写类型表达式时，
箭头向_右_结合；例如，{lean}`Nat.add` 的类型是 {lean}`Nat → Nat → Nat`，
它等价于 {lean}`Nat → (Nat → Nat)`。因此，可以把 {lean}`Nat.add` 看成一个函数：
它接受一个自然数，并返回另一个接受自然数且返回自然数的函数。在类型论中，
这通常比把 {lean}`Nat.add` 写成接受一对自然数作为输入并返回自然数的函数更方便。
例如，这允许你对函数 {lean}`Nat.add` 进行“部分应用”。上面的例子表明，
{lean}`Nat.add 3` 的类型是 {lean}`Nat → Nat`；也就是说，{lean}`Nat.add 3`
返回一个“等待”第二个参数 {lean}`n` 的函数，这随后等价于写作 {lean}`Nat.add 3 n`。
:::comment
```
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and “redefining” it to look like ``g`` is a process
known as _currying_. -->
```
:::


你已经看到，若有 {lean}`m : Nat` 和 {lean}`n : Nat`，则 {lean}`(m, n)`
表示由 {lean}`m` 和 {lean}`n` 构成的有序对，其类型为 {lean}`Nat × Nat`。
这给出了创建自然数对的一种方式。反过来，若有 {lean}`p : Nat × Nat`，
则可以写 {lean}`p.1 : Nat` 和 {lean}`p.2 : Nat`，这给出了提取其两个分量的方式。
::::

# 作为对象的类型
%%%
tag := "types-as-objects"
%%%

Lean 的依赖类型论扩展简单类型论的一种方式是：类型本身——如 {lean}`Nat`
和 {lean}`Bool` 这样的实体——是一等公民；也就是说，它们自身也是对象。
为使这一点成立，它们每一个也都必须有一个类型。

```lean
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

可以看到，上面每一个表达式都是类型 {lean}`Type` 的对象。也可以为类型声明新的常量：

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- α : Type
#check F α      -- F α : Type
#check F Nat    -- F Nat : Type
#check G α      -- G α : Type → Type
#check G α β    -- G α β : Type
#check G α Nat  -- G α Nat : Type
```

如上例所示，你已经见过类型为 {lean}`Type → Type → Type` 的函数示例，
即笛卡尔积 {lean}`Prod`：

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- α × β : Type
#check α × β          -- α × β : Type

#check Prod Nat Nat   -- Nat × Nat : Type
#check Nat × Nat      -- Nat × Nat : Type
```

:::leanFirst
再看另一个例子：给定任意类型 {leanRef}`α`，类型 {leanRef}`List α`
表示由类型 {leanRef}`α` 的元素构成的列表的类型。

```lean
def α : Type := Nat

#check List α    -- List α : Type
#check List Nat  -- List Nat : Type
```
:::

既然 Lean 中每个表达式都有类型，一个自然的问题是：{lean}`Type` 本身具有何种类型？

```lean
#check Type      -- Type : Type 1
```

你实际上已经触及 Lean 类型系统中最微妙的方面之一。
Lean 的底层基础具有一个无限的类型层级：

```lean
#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
#check Type 2   -- Type 2 : Type 3
#check Type 3   -- Type 3 : Type 4
#check Type 4   -- Type 4 : Type 5
```

:::setup
```
universe n
variable (n : Nat)
```
可以把 {lean}`Type 0` 看作“小”类型或“普通”类型的宇宙。
于是 {lean}`Type 1` 是一个更大的类型宇宙，它把 {lean}`Type 0` 作为元素包含在内；
而 {lean}`Type 2` 又是一个更大的类型宇宙，它把 {lean}`Type 1` 作为元素包含在内。
这个列表是无限的：对每个自然数 {lean}`n`，都有一个 {lean}`Type n`。
{lean}`Type` 是 {lean}`Type 0` 的缩写：
:::

```lean
#check Type
#check Type 0
```


下表有助于具体化正在讨论的关系。沿 x 轴移动表示宇宙的变化，
而沿 y 轴移动表示有时称为“阶数”的变化。

:::table

*
 * 种类
 * {lean}`Prop` ({lean}`Sort 0`)
 * {lean}`Type` ({lean}`Sort 1`)
 * {lean}`Type 1` ({lean}`Sort 2`)
 * {lean}`Type 2` ({lean}`Sort 3`)
 * ...

*
 * 类型
 * {lean}`True`
 * {lean}`Bool`
 * {lean}`Nat -> Type`
 * {lean}`Type -> Type 1`
 * ...

*
 * 项
 * {lean}`True.intro`
 * {lean}`true`
 * {lean}`fun n => Fin n`
 * {lean}`fun (_ : Type) => Type`
 * ...

:::

:::setup

```
universe u
variable (α : Type u)
```

然而，有些操作需要在类型宇宙上是_多态_的。例如，对任意类型 {lean}`α`，
无论 {lean}`α` 位于哪个类型宇宙中，{lean}`List α` 都应当有意义。
这解释了函数 {lean}`List` 的类型签名：


```lean
#check List    -- List.{u} (α : Type u) : Type u
```

这里 {lit}`u` 是一个在类型层级上取值的变量。{kw}`#check` 命令的输出意味着：
只要 {lean}`α` 的类型是 {lean}`Type u`，{lean}`List α` 的类型也就是 {lean}`Type u`。
函数 {lean}`Prod` 也类似地是多态的：
:::

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

为定义多态常量，Lean 允许使用 {kw}`universe` 命令显式声明宇宙变量：

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```

:::leanFirst
也可以在定义 {leanRef}`F` 时给出宇宙参数，从而避免使用 {kw}`universe` 命令：

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```
:::

# 函数抽象与求值
%%%
tag := "function-abstraction-and-evaluation"
%%%

Lean 提供 {kw}`fun`（或 {kw}`λ`）关键字，用于如下从表达式创建函数：

```lean
#check fun (x : Nat) => x + 5   -- fun x => x + 5 : Nat → Nat
-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5     -- fun x => x + 5 : Nat → Nat
```

在这个例子中，类型 {lean}`Nat` 可以被推断出来：
```lean
#check fun x => x + 5   -- fun x => x + 5 : Nat → Nat
#check λ x => x + 5     -- fun x => x + 5 : Nat → Nat
```

可以通过传入所需参数来对 lambda 函数求值：

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

:::setup
```
variable {x : α} {t : β}
```

由另一个表达式创建函数的过程称为 _lambda 抽象_。假设你有变量 {lean}`x : α`，
并且能够构造表达式 {lean}`t : β`，那么表达式 {lean}`fun (x : α) => t`，
或等价地 {lean}`λ (x : α) => t`，就是类型 {lean}`α → β` 的对象。
可以把它看作从 {lean}`α` 到 {lean}`β` 的函数，该函数把任意值 {leanRef}`x`
映射到值 {leanRef}`t`。
:::

下面还有一些示例

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
```

Lean 将最后三个示例解释为同一个表达式；在最后一个表达式中，
Lean 从表达式 {leanRef}`if not y then x + 1 else x + 2` 推断 {leanRef}`x`
和 {leanRef}`y` 的类型。

一些数学上常见的函数操作示例可以用 lambda 抽象来描述：

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- fun x => x : Nat → Nat
#check fun x : Nat => true     -- fun x => true : Nat → Bool
#check fun x : Nat => g (f x)  -- fun x => g (f x) : Nat → Bool
#check fun x => g (f x)        -- fun x => g (f x) : Nat → Bool
```

思考这些表达式的含义。表达式 {lean}`fun x : Nat => x` 表示 {lean}`Nat`
上的恒等函数；表达式 {lean}`fun x : Nat => true` 表示总是返回 {lean}`true` 的常值函数；
而 {leanRef}`fun x : Nat => g (f x)` 表示 {leanRef}`f` 与 {leanRef}`g` 的复合。
一般而言，可以省略类型标注，让 Lean 为你推断。因此，例如可以写
{leanRef}`fun x => g (f x)`，而不写 {leanRef}`fun x : Nat => g (f x)`。

:::leanFirst
可以把函数作为参数传入，并通过给它们命名为 {leanRef}`f` 和 {leanRef}`g`，
在实现中使用这些函数：

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
```
:::

也可以把类型作为参数传入：

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
例如，最后一个表达式表示这样一个函数：它接受三个类型 {leanRef}`α`、
{leanRef}`β` 和 {leanRef}`γ`，以及两个函数 {leanRef}`g : β → γ` 和 {leanRef}`f : α → β`，
并返回 {leanRef}`g` 与 {leanRef}`f` 的复合。（理解这个函数的类型需要理解_依赖积_，
这将在下文解释。）

:::setup
```
variable (α : Type) (t : β)
-- Avoid warnings
axiom whatever : α
def b : γ := whatever
```

lambda 表达式的一般形式是 {lean}`fun (x : α) => t`，其中变量 {leanRef}`x`
是一个“绑定变量”：它实际上是一个占位符，其“作用域”不会延伸到表达式 {leanRef}`t` 之外。
例如，表达式 {lit}`fun (b : β) (x : α) => b` 中的变量 {lean}`b`，
与先前声明的常量 {lean}`b` 没有任何关系。事实上，该表达式表示的函数与
{lean}`fun (u : β) (z : α) => u` 相同。


形式地说，只差绑定变量重命名的表达式称为 _alpha 等价_，并被认为是“相同的”。
Lean 能识别这种等价。
:::

:::setup
```
variable (t : α → β) (s : α)
```
注意，将项 {lean}`t : α → β` 应用于项 {lean}`s : α` 会得到表达式 {lean}`t s : β`。
回到前面的例子，并为清晰起见重命名绑定变量，请注意以下表达式的类型：
:::

```lean
#check (fun x : Nat => x) 1     -- (fun x => x) 1 : Nat
#check (fun x : Nat => true) 1  -- (fun x => true) 1 : Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
```

如预期，表达式 {lean}`(fun x : Nat =>  x) 1` 的类型为 {lean}`Nat`。
事实上，还应当有更强的结论：将表达式 {lean}`(fun x : Nat => x)` 应用于 {lean}`1`
应当“返回”值 {lean}`1`。而它确实如此：

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

稍后你会看到这些项是如何被求值的。现在请注意，这是依赖类型论的一个重要特征：
每个项都有计算行为，并支持_规范化_的概念。原则上，两个能化简到同一值的项称为
_定义等价_。Lean 的类型检查器会把它们视为“相同”，并尽力识别和支持这些同一性。

Lean 是一门完整的编程语言。它有能够生成二进制可执行文件的编译器，
也有交互式解释器。可以使用命令 {kw}`#eval` 执行表达式，
这是测试函数的首选方式。

:::comment
```
<!--
Note that `#eval` and
`#reduce` are _not_ equivalent. The command `#eval` first compiles
Lean expressions into an intermediate representation (IR) and then
uses an interpreter to execute the generated IR. Some builtin types
(e.g., `Nat`, `String`, `Array`) have a more efficient representation
in the IR. The IR has support for using foreign functions that are
opaque to Lean.

In contrast, the ``#reduce`` command relies on a reduction engine
similar to the one used in Lean's trusted kernel, the part of Lean
that is responsible for checking and verifying the correctness of
expressions and proofs. It is less efficient than ``#eval``, and
treats all foreign functions as opaque constants. You will learn later
that there are some other differences between the two commands.
-->
```
:::

# 定义
%%%
tag := "definitions"
%%%

回顾一下，{kw}`def` 关键字提供了一种声明新的具名对象的重要方式。

```lean
def double (x : Nat) : Nat :=
  x + x
```

如果你了解其他编程语言中的函数工作方式，这看起来可能会更熟悉。
名称 {leanRef}`double` 被定义为一个函数，它接受一个类型为 {leanRef}`Nat` 的输入参数
{leanRef}`x`；调用结果是 {leanRef}`x + x`，因此返回类型为 {lean}`Nat`。
随后可以这样调用此函数：

```lean
def double (x : Nat) : Nat :=
 x + x
-----
#eval double 3    -- 6
```

在这种情况下，可以把 {kw}`def` 看作一种具名的 {kw}`fun`。
下面的写法得到相同结果：

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

当 Lean 有足够信息可以推断类型时，可以省略类型声明。类型推断是 Lean 的重要组成部分：

```lean
def double :=
  fun (x : Nat) => x + x
```

定义的一般形式是 {lit}`def foo : α := bar`，其中 {lit}`α` 是表达式 {lit}`bar`
返回的类型。Lean 通常可以推断类型 {lit}`α`，但显式写出它往往是好习惯。
这会澄清你的意图；如果定义右侧不具有匹配的类型，Lean 会报告错误。

右侧的 {lit}`bar` 可以是任意表达式，而不仅仅是 lambda。
因此，{kw}`def` 也可以像这样仅仅为一个值命名：

```lean
def pi := 3.141592654
```

{kw}`def` 可以接受多个输入参数。下面创建一个将两个自然数相加的函数：

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

参数列表也可以像这样分开书写：

```lean
def double (x : Nat) : Nat :=
  x + x
-----
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

注意，这里我们调用 {leanRef}`double` 函数来构造传给 {leanRef}`add` 的第一个参数。

可以在 {kw}`def` 中使用其他更有趣的表达式：

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

你大概可以猜出这个函数会做什么。

也可以定义一个以另一个函数为输入的函数。下面的函数会调用给定函数两次，
并把第一次调用的输出传给第二次调用：

```lean
def double (x : Nat) : Nat :=
 x + x
-----
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

现在再抽象一些，也可以指定类似类型参数的参数：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

这意味着 {leanRef}`compose` 是一个函数，它以任意两个函数作为输入参数，
只要这两个函数各自都只接受一个输入。类型表达式 {leanRef}`β → γ` 与 {leanRef}`α → β`
表明有一个要求：第二个函数的输出类型必须与第一个函数的输入类型相匹配。
这是合理的；否则这两个函数就不能复合。

{leanRef}`compose` 还接受第三个参数，其类型为 {leanRef}`α`；它用该参数调用第二个函数
（局部命名为 {leanRef}`f`），并把该函数的结果（类型为 {leanRef}`β`）作为输入传给第一个函数
（局部命名为 {leanRef}`g`）。第一个函数返回类型 {leanRef}`γ` 的值，
因此这也是 {leanRef}`compose` 函数的返回类型。

{leanRef}`compose` 也非常通用，因为它适用于任意类型 {leanRef}`α β γ`。
这意味着，只要两个函数各自接受一个参数，并且第二个函数的输出类型与第一个函数的输入类型相匹配，
{leanRef}`compose` 几乎可以复合任意两个函数。例如：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def double (x : Nat) : Nat :=
  x + x
-----
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

# 局部定义
%%%
tag := "local-definitions"
%%%

:::setup
```
variable (t1 : α) (t2 : β)
```

Lean 也允许使用 {kw}`let` 关键字引入“局部”定义。表达式 {lean}`let a := t1; t2`
与把 {leanRef}`t2` 中每一次出现的 {leanRef}`a` 都替换为 {leanRef}`t1` 所得结果定义等价。
:::

```lean
#check let y := 2 + 2; y * y   -- let y := 2 + 2; y * y : Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

:::setup
```
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

variable (x : Nat)
```

这里，{lean}`twice_double x` 与项 {lean}`(x + x) * (x + x)` 定义等价。

:::

可以通过串联 {kw}`let` 语句来组合多个赋值：

```lean
#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

使用换行时，可以省略 {lit}`;`。
```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

::::leanFirst
:::setup
```
variable (t1 : α) (t2 : β)
```

注意，表达式 {lean}`let a := t1; t2` 的含义与 {lean}`(fun a => t2) t1` 的含义非常相近，
但二者并不相同。在第一个表达式中，应把 {leanRef (in:="let a := t1; t2")}`t2`
中每一个 {leanRef (in:="let a := t1; t2")}`a` 都看作 {leanRef (in:="let a := t1; t2")}`t1`
的语法缩写。在第二个表达式中，{leanRef (in:="(fun a => t2) t1")}`a` 是一个变量，
而表达式 {leanRef (in:="(fun a => t2) t1")}`fun a => t2` 必须在不依赖
{leanRef (in:="(fun a => t2) t1")}`a` 的具体值的情况下有意义。
{kw}`let` 构造是一种更强的缩写手段；有些形如 {lean}`let a := t1; t2` 的表达式
不能表示为 {lean}`(fun a => t2) t1`。作为练习，请尝试理解为什么下面
{leanRef}`foo` 的定义能通过类型检查，而 {lit}`bar` 的定义不能。
:::

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
::::

# 变量与段落
%%%
tag := "variables-and-sections"
%%%

考虑下面三个函数定义：
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean 提供 {kw}`variable` 命令，使这类声明看起来更紧凑：

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
可以声明任意类型的变量，而不仅限于 {lean}`Type` 本身：
```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
打印它们会显示，这三组定义具有完全相同的效果。

{kw}`variable` 命令指示 Lean：在按名称引用这些变量的定义中，
把所声明的变量插入为绑定变量。Lean 足够智能，能够判断一个定义中哪些变量被显式或隐式使用。
因此，在书写定义时，你可以像 {leanRef}`α`、{leanRef}`β`、{leanRef}`γ`、
{leanRef}`g`、{leanRef}`f`、{leanRef}`h` 和 {leanRef}`x` 都是固定对象那样进行，
并让 Lean 自动为你对定义进行抽象。

以这种方式声明时，变量会一直保持在作用域中，直到当前文件结束。
不过，有时限制变量的作用域是有用的。为此，Lean 提供了 {kw}`section` 的概念：

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

当段落关闭时，这些变量离开作用域，不能再被引用。

段落内部的行不必缩进。也不必给段落命名；也就是说，可以使用匿名的
{kw}`section` / {kw}`end` 对。不过，如果给段落命名，就必须使用相同名称关闭它。
段落也可以嵌套，这允许你逐步声明新的变量。

# 命名空间
%%%
tag := "namespaces"
%%%

Lean 提供了将定义分组到嵌套的、层级化的_命名空间_中的能力：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

当声明正在命名空间 {leanRef}`Foo` 中工作时，你声明的每个标识符都有一个带前缀
“{lit}`Foo.`”的全名。在该命名空间内部，可以用较短名称引用标识符；
但一旦结束该命名空间，就必须使用较长名称。与 {kw}`section` 不同，命名空间必须有名称。
根层级只有一个匿名命名空间。

{leanRef}`open` 命令把较短名称引入当前上下文。通常，当导入一个模块时，
你会想打开其中一个或多个命名空间，以便访问短标识符。但有时你会希望让这些信息
由完全限定名保护起来，例如当它们与你想使用的另一个命名空间中的标识符冲突时。
因此，命名空间为你提供了一种管理工作环境中名称的方式。

例如，Lean 将涉及列表的定义和定理归入命名空间 {lit}`List`。
```lean
#check List.nil
#check List.cons
#check List.map
```
:::leanFirst
命令 {leanRef}`open List` 允许你使用较短名称：
```lean
open List

#check nil
#check cons
#check map
```
:::
与段落一样，命名空间可以嵌套：
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```
已经关闭的命名空间稍后可以重新打开，甚至可以在另一个文件中打开：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

与段落一样，嵌套命名空间必须按打开的相反顺序关闭。命名空间和段落服务于不同目的：
命名空间组织数据，而段落声明要插入定义中的变量。段落还可用于限定诸如
{kw}`set_option` 和 {kw}`open` 等命令的作用域。

然而，在许多方面，{kw}`namespace`{lit}`  ...  `{kw}`end` 块的行为与
{kw}`section`{lit}`  ...  `{kw}`end` 块相同。特别地，如果在命名空间内使用
{kw}`variable` 命令，其作用域会被限制在该命名空间内。类似地，如果在命名空间内使用
{kw}`open` 命令，当命名空间关闭时，其效果也会消失。

# 依赖类型论为何“依赖”？
%%%
tag := "what-makes-dependent-type-theory-dependent"
%%%

:::setup
```
variable (α : Type) (n : Nat)
```

简短的解释是：类型可以依赖于参数。你已经见过一个很好的例子：
类型 {lean}`List α` 依赖于参数 {lean}`α`，正是这种依赖区分了 {lean}`List Nat`
和 {lean}`List Bool`。再举一例，考虑类型 {lean}`Vector α n`，它表示长度为
{lean}`n`、元素类型为 {lean}`α` 的向量类型。这个类型依赖于_两个_参数：
向量中元素的类型（{lean}`α : Type`）以及向量的长度 {lean}`n : Nat`。
:::

::::setup
```
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
variable (α : Type) (a : α) (as : List α)
```
:::leanFirst

假设你想编写函数 {leanRef}`cons`，用于把一个新元素插入列表头部。
{leanRef}`cons` 应当具有何种类型？这样的函数是_多态_的：你期望针对 {leanRef}`Nat`、
{lean}`Bool` 或任意类型 {lean}`α` 的 {leanRef}`cons` 函数以同样方式行为。
因此，把类型作为 {leanRef}`cons` 的第一个参数是合理的；这样，对任意类型 {lean}`α`，
{lean}`cons α` 就是类型为 {lean}`α` 的列表的插入函数。换言之，对每个 {lean}`α`，
{lean}`cons α` 都是这样一个函数：它接受一个元素 {lean}`a : α` 和一个列表
{lean}`as : List α`，并返回一个新列表，因此有 {lean}`cons α a as : List α`。

显然，{lean}`cons α` 应当具有类型 {lean}`α → List α → List α`。但 {leanRef}`cons`
本身应当具有何种类型？第一猜想可能是 {lean}`Type → α → List α → List α`，
但仔细想来，这并不合理：此表达式中的 {leanRef}`α` 没有指向任何东西，
而它本应指向类型为 {lean}`Type` 的那个参数。换句话说，_假设_ {lean}`α : Type`
是函数的第一个参数，那么接下来两个元素的类型分别是 {lean}`α` 和 {lean}`List α`。
这些类型会随着第一个参数 {leanRef}`α` 而变化。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- cons Nat : Nat → List Nat → List Nat
#check cons Bool       -- cons Bool : Bool → List Bool → List Bool
#check cons            -- cons (α : Type) (a : α) (as : List α) : List α
```
:::
::::

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (f : (a : α) → β a)
```

这是_依赖函数类型_，或称*依赖箭头类型*的一个实例。给定 {lean}`α : Type`
和 {lean}`β : α → Type`，可以把 {lean}`β` 看作 {lean}`α` 上的一个类型族，
也就是说，对每个 {lean}`a : α` 都有一个类型 {lean}`β a`。在这种情况下，
类型 {lean}`(a : α) → β a` 表示具有如下性质的函数 {lean}`f` 的类型：
对每个 {lean}`a : α`，{lean}`f a` 都是 {lean}`β a` 的一个元素。
换言之，{lean}`f` 返回值的类型依赖于其输入。
:::

:::setup
```
variable (α : Type) (β : Type) (a : α) (f : (a : α) → β a)
```
注意，对任意表达式 {lean}`β : Type`，{lean}`(a : α) → β` 都有意义。
当 {lean}`β` 的值依赖于 {leanRef}`a` 时（例如上一段中的表达式 {leanRef}`β a`），
{leanRef}`(a : α) → β` 表示一个依赖函数类型。当 {lean}`β` 不依赖于 {leanRef}`a` 时，
{leanRef}`(a : α) → β` 与类型 {lean}`α → β` 没有区别。事实上，在依赖类型论
（以及 Lean）中，当 {lean}`β` 不依赖于 {leanRef (in := "a : α")}`a` 时，
{lean}`α → β` 只是 {lean}`(a : α) → β` 的记号。
:::

回到列表的例子，可以使用命令 {kw}`#check` 查看以下 {lean}`List` 函数的类型。
{lit}`@` 符号以及圆括号与花括号之间的区别稍后会解释。

```lean
#check @List.cons    -- @List.cons : {α : Type u_1} → α → List α → List α
#check @List.nil     -- @List.nil : {α : Type u_1} → List α
#check @List.length  -- @List.length : {α : Type u_1} → List α → Nat
#check @List.append  -- @List.append : {α : Type u_1} → List α → List α → List α
```

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (b : β a)
```
正如依赖函数类型 {lean}`(a : α) → β a` 通过允许 {lit}`β`
依赖于 {leanRef}`a` 来推广函数类型 {lit}`α → β` 一样，依赖笛卡尔积类型
{lean}`(a : α) × β a` 也以同样方式推广笛卡尔积 {lit}`α × β`。
依赖积也称为 _sigma_ 类型，并且也可以写作 {lean}`Σ a : α, β a`。
可以使用 {lean (type := "(a : α) × β a")}`⟨a, b⟩` 或 {lean}`Sigma.mk a b`
创建依赖对。字符 {lit}`⟨` 和 {lit}`⟩` 可分别通过 {kbd}`\langle` 与 {kbd}`\rangle`
或 {kbd}`\<` 与 {kbd}`\>` 输入。
:::

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```
上面的函数 {leanRef}`f` 与 {leanRef}`g` 表示同一个函数。


# 隐式参数
%%%
tag := "implicit-arguments"
%%%

假设我们有如下列表实现：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

那么，可以如下构造 {lean}`Nat` 的列表：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```
:::setup
```
def Lst (α : Type u) : Type u := List α
variable (α : Type)
```
由于构造子在类型上是多态的，我们必须反复把类型 {lean}`Nat` 作为参数插入。
但这些信息是冗余的：在 {leanRef}`Lst.cons Nat 5 (Lst.nil Nat)` 中，
可以根据第二个参数 {leanRef}`5` 具有类型 {leanRef}`Nat` 这一事实推断参数 {lean}`α`。
类似地，{leanRef}`Lst.nil Nat` 中的参数也可以被推断出来；这不是来自该表达式中的其他内容，
而是来自它被作为参数传给函数 {leanRef}`Lst.cons` 这一事实，后者在该位置期望一个
类型为 {lean}`Lst α` 的元素。
:::

这是依赖类型论的一个核心特征：项携带大量信息，而且其中一些信息常常可以从上下文推断出来。
在 Lean 中，可以使用下划线 {lit}`_` 来指定系统应当自动填入这些信息。
这称为“隐式参数”。

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append
-----
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs -- Lst.append Nat as bs : Lst Nat
```

然而，输入所有这些下划线仍然很繁琐。当一个函数接受的某个参数通常可以从上下文推断时，
Lean 允许你指定该参数默认应保持隐式。做法是把这些参数放在花括号中，如下所示：

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

唯一改变的是变量声明中 {leanRef}`α : Type u` 周围的括号。也可以在函数定义中使用这种机制：

```lean
universe u
def ident {α : Type u} (x : α) := x
```

检查 {leanRef}`ident` 的类型时，需要将其置于圆括号中，以避免显示其签名：
```lean
universe u
def ident {α : Type u} (x : α) := x
---------
#check (ident)       -- ident : ?m.22 → ?m.22
#check ident 1       -- ident 1 : Nat
#check ident "hello" -- ident "hello" : String
#check @ident        -- @ident : {α : Type u_1} → α → α
```

这使 {leanRef}`ident` 的第一个参数成为隐式参数。从记号上看，
这隐藏了对类型的指定，使 {leanRef}`ident` 看起来仿佛只是接受任意类型的一个参数。
事实上，标准库中的函数 {lean}`id` 正是以这种方式定义的。这里选择一个非传统名称，
只是为了避免名称冲突。

使用 {kw}`variable` 命令声明变量时，也可以把它们指定为隐式的：

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

这里对 {leanRef}`ident` 的定义与上面的定义具有相同效果。

Lean 具有非常复杂的机制来实例化隐式参数；我们将看到，它们可用于推断函数类型、
谓词，甚至证明。实例化项中的这些“空洞”或“占位符”的过程通常称为_阐释_。
隐式参数的存在意味着，有时可能没有足够信息来精确确定一个表达式的含义。
像 {lean}`id` 或 {lean}`List.nil` 这样的表达式称为_多态_的，
因为它可以在不同上下文中具有不同含义。

:::setup
```
variable (T : Type) (e : T)
```

总可以通过写 {lean}`(e : T)` 来指定表达式 {lean}`e` 的类型 {lean}`T`。
这会指示 Lean 的阐释器在尝试解析隐式参数时，把值 {lean}`T` 用作 {lean}`e` 的类型。
在下面第二组示例中，这一机制用于指定表达式 {lean}`id` 和 {lean}`List.nil` 的期望类型：
:::

```lean
#check (List.nil)             -- [] : List ?m.2
#check (id)                   -- id : ?m.1 → ?m.1

#check (List.nil : List Nat)  -- [] : List Nat
#check (id : Nat → Nat)       -- id : Nat → Nat
```

Lean 中的数码是重载的；但当无法推断一个数码的类型时，Lean 默认假定它是自然数。
因此，下面前两个 {kw}`#check` 命令中的表达式会以相同方式阐释，
而第三个 {kw}`#check` 命令将 {lean (type := "Int")}`2` 解释为整数。

```lean
#check 2            -- 2 : Nat
#check (2 : Nat)    -- 2 : Nat
#check (2 : Int)    -- 2 : Int
```

:::setup
```
variable (foo : {α : Type} → α → β)
```

然而，有时会遇到这样的情况：我们已经把函数的某个参数声明为隐式，
但现在又想显式提供该参数。如果 {lean}`foo` 是这样的函数，记号 {lean}`@foo`
表示同一个函数，只是所有参数都变为显式。
:::

```lean
#check @id        -- @id : {α : Sort u_1} → α → α
#check @id Nat    -- id : Nat → Nat
#check @id Bool   -- id : Bool → Bool

#check @id Nat 1     -- id 1 : Nat
#check @id Bool true -- id true : Bool
```

注意，现在第一个 {kw}`#check` 命令给出了标识符 {leanRef}`id` 的类型，
且没有插入任何占位符。此外，输出表明第一个参数是隐式的。
