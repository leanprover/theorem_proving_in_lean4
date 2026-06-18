import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "归纳与递归" =>
%%%
tag := "induction-and-recursion"
file := "Induction-and-Recursion"
%%%

在上一章中，我们看到归纳定义为在 Lean 中引入新类型提供了
强有力的手段。此外，构造子和递归子是定义这些类型上函数的
唯一方式。由 {tech}[propositions-as-types] 对应可知，这意味着
归纳是证明的基本方法。

Lean 提供了定义递归函数、进行模式匹配以及书写归纳证明的
自然方式。它允许你通过指定函数应满足的等式来定义函数，
也允许你通过指定如何处理可能出现的各种情形来证明定理。
在幕后，这些描述会经由一个我们称为“方程编译器”的过程，
被“编译”到原始递归子。方程编译器并不是受信代码基的一部分；
它的输出由一些项组成，这些项会由内核独立检查。

# 模式匹配
%%%
tag := "pattern-matching"
%%%

对示意性模式的解释是编译过程的第一步。我们已经看到，
{lit}`casesOn` 递归子可以根据归纳定义类型中涉及的构造子，
通过分情形来定义函数并证明定理。但是，复杂的定义可能会使用
多个嵌套的 {lit}`casesOn` 应用，因而难以阅读和理解。模式匹配
提供了一种更方便的方法，也为函数式编程语言的用户所熟悉。

:::setup
```
open Nat
variable (x : Nat)
```

考虑自然数这一归纳定义的类型。每个自然数要么是 {lean}`zero`，
要么是 {lean}`succ x`，因此你可以通过在这两种情形中分别指定一个值，
来定义从自然数到任意类型的函数：
:::

```lean
set_option linter.unusedVariables false
--------
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

用于定义这些函数的等式在定义上成立：

```lean
open Nat
def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x
def isZero : Nat → Bool
  | zero   => true
  | succ x => false
------
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

除了 {leanRef}`zero` 和 {leanRef}`succ`，我们也可以使用更熟悉的记号：

```lean
set_option linter.unusedVariables false
--------
def sub1 : Nat → Nat
  | 0     => 0
  | x + 1 => x

def isZero : Nat → Bool
  | 0     => true
  | x + 1 => false
```

由于加法和零记号已经被赋予 {attr}`[match_pattern]` 属性，
它们可以用于模式匹配。Lean 只是将这些表达式规范化，直到构造子
{leanRef}`zero` 和 {leanRef}`succ` 显现出来。

模式匹配适用于任何归纳类型，例如乘积类型和选项类型：

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

这里我们不仅用它来定义函数，也用它来进行分情形证明：

```lean
namespace Hidden
------
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => show not (not true) = true from rfl
  | false => show not (not false) = false from rfl
------
end Hidden
```

模式匹配也可用于析构归纳定义的命题：

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

这为展开使用逻辑联结词的假设提供了一种紧凑方式。

在所有这些例子中，模式匹配都用于进行一次单一的情形区分。
更有意思的是，模式可以包含嵌套的构造子，如下列例子所示。

```lean
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
```

方程编译器首先根据输入是 {leanRef}`zero` 还是形如 {leanRef}`succ x`
来分情形。然后它再根据 {leanRef}`x` 是形如 {leanRef}`zero` 还是
{leanRef}`succ x` 进行情形区分。它从给出的模式中确定必要的情形区分；
如果这些模式未能穷尽所有情形，则会报错。同样，我们也可以使用算术记号，
如下一个版本所示。无论哪种情形，定义等式都在定义上成立。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
------
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

:::setup
```
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
```
你可以写 {leanCommand}`#print sub2` 来查看该函数是如何被编译为
递归子的。（Lean 会告诉你，{leanRef}`sub2` 是根据一个内部辅助函数
{lean}`sub2.match_1` 定义的，但你也可以把它打印出来。）Lean 使用这些
辅助函数来编译 {kw}`match` 表达式。实际上，上述定义会展开为
:::
```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0     => 0
    | 1     => 0
    | x + 2 => x
```

下面是更多嵌套模式匹配的例子：

```lean
set_option linter.unusedVariables false
--------
example (p q : α → Prop) :
        (∃ x, p x ∨ q x) →
        (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

方程编译器可以按顺序处理多个参数。例如，把前一个例子定义为
二元函数会更自然：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

下面是另一个例子：

```lean
set_option linter.unusedVariables false
--------
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

注意，模式之间用逗号分隔。

在下面每个例子中，尽管其他参数也出现在模式列表中，
但情形区分只发生在第一个参数上。

```lean
set_option linter.unusedVariables false
namespace Hidden
------
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
------
end Hidden
```

还请注意，当定义中不需要某个参数的值时，你可以改用下划线。
这个下划线称为 _通配符模式_，或 _匿名变量_。与方程编译器之外的用法
相反，这里的下划线 _并不_ 表示隐式参数。用下划线表示通配符是
函数式编程语言中的常见做法，因此 Lean 也采用了这一记号。
{ref "wildcards-and-overlapping-patterns"}[通配符与重叠模式] 一节
进一步阐述了通配符的概念，而 {ref "inaccessible-patterns"}[不可访问模式]
的说明则解释了你也可以如何在模式中使用隐式参数。

::::setup
```
set_option linter.unusedVariables false
--------
def tail : List α → List α
  | []      => []
  | a :: as => as
```

:::leanFirst
如 {ref "inductive-types"}[归纳类型] 中所述，
归纳数据类型可以依赖于参数。下面的例子使用模式匹配定义
{name}`tail` 函数。参数 {leanRef}`α : Type u` 出现在冒号之前，
表示它不参与模式匹配。Lean 也允许参数出现在 {leanRef}`:` 之后，
但对它们进行模式匹配需要显式的 {leanRef}`match`。


```lean
set_option linter.unusedVariables false
--------
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```
:::
::::

尽管在这两个例子中参数 {leanRef}`α` 的位置不同，但两种情况下它都以
同样的方式处理：它不参与情形区分。

Lean 还可以处理更复杂的模式匹配形式，其中依值类型的参数会对
各种情形施加额外约束。这类 _依值模式匹配_ 的例子将在
{ref "dependent-pattern-matching"}[依值模式匹配] 一节中讨论。

# 通配符与重叠模式
%%%
tag := "wildcards-and-overlapping-patterns"
%%%

考虑上一节中的一个例子：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

另一种写法是：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

在第二种写法中，模式会发生重叠；例如，参数对 {lit}`0, 0` 匹配全部
三个情形。但是 Lean 通过使用第一个适用的等式来处理这种歧义，
因此在这个例子中最终结果相同。特别地，以下等式在定义上成立：

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
------
example : foo 0       0       = 0 := rfl
example : foo 0       (n + 1) = 0 := rfl
example : foo (m + 1) 0       = 1 := rfl
example : foo (m + 1) (n + 1) = 2 := rfl
```

由于不需要 {leanRef (in:="m, n")}`m` 和 {leanRef (in:="m, n")}`n` 的值，
我们也完全可以改用通配符模式。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

你可以检查，{leanRef}`foo` 的这个定义满足与之前相同的定义等式。

:::setup
```
variable (α : Type u) (a : α)
```

一些函数式编程语言支持 _不完全模式_。在这些语言中，对于未覆盖的情形，
解释器会产生异常，或返回某个任意值。我们可以用 {lean}`Inhabited`
类型类来模拟返回任意值的方法。粗略地说，{lean}`Inhabited α` 的一个元素
见证了 {lean}`α` 中有元素这一事实；在 {ref "type-classes"}[类型类一章] 中，
我们将看到可以指示 Lean 适当的基本类型是有居留元的，并且它可以自动
推断其他构造出的类型也是有居留元的。在此基础上，标准库为任何有居留元的
类型提供了默认元素 {lean}`default`。

我们也可以使用类型 {lean}`Option α` 来模拟不完全模式。思路是对已给出的
模式返回 {lean}`some a`，而对未覆盖的情形使用
{lean (type:="Option α")}`none`。下面的例子展示了这两种方法。
:::

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- “不完全”情形

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- “不完全”情形

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

方程编译器很聪明。如果你在下面的定义中漏掉任何情形，错误信息会告诉你
哪些情形尚未被覆盖。

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

在适当的情况下，它还会使用 {kw}`if`{lit}`  ...  `{kw}`then`{lit}`  ...  `{kw}`else`
而不是 {lit}`casesOn`。

```lean
set_option pp.proofs true
-------
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

# 结构递归与结构归纳
%%%
tag := "structural-recursion-and-induction"
%%%

方程编译器之所以强大，是因为它还支持递归定义。在接下来的三节中，
我们将分别介绍：

- 结构递归定义
- 良基递归定义
- 相互递归定义

一般而言，方程编译器处理如下形式的输入：

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

这里 {lit}`(a : α)` 是一串参数，{lit}`(b : β)` 是进行模式匹配的一串参数，
而 {lit}`γ` 是任意类型，它可以依赖于 {lit}`a` 和 {lit}`b`。每一行都应当
包含相同数量的模式，即 {lit}`β` 的每个元素各有一个模式。正如我们所见，
模式要么是变量，要么是应用于其他模式的构造子，要么是可规范化为这种形式的
表达式（其中非构造子带有 {attr}`[match_pattern]` 属性）。构造子的出现会
引发情形区分，而构造子的参数由给定变量表示。在
{ref "dependent-pattern-matching"}[依值模式匹配] 一节中，我们将看到，
为了使表达式通过类型检查，模式中的某些显式项会被强制为特定形式，
尽管它们并不参与模式匹配。因此它们被称为“{deftech}[inaccessible patterns]”
（不可访问模式）。不过在介绍 {ref "dependent-pattern-matching"}[依值模式匹配]
之前，我们还不需要使用这种不可访问模式。

如上一节所见，项 {lit}`t₁, ..., tₙ` 可以使用任意参数 {lit}`a`，也可以使用
相应模式中引入的任意变量。使递归与归纳成为可能的是，它们还可以包含对
{lit}`foo` 的递归调用。本节将讨论 _结构递归_，其中出现在 {lit}`=>`
右侧、传给 {lit}`foo` 的参数，是左侧模式的子项。其思想是：它们在结构上更小，
因此在归纳类型中出现在更早的阶段。下面是上一章中的一些结构递归例子，
现在用方程编译器来定义：

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n
```

{leanRef}`zero_add` 的证明清楚表明，在 Lean 中归纳证明实际上是一种递归。

上面的例子表明，{leanRef}`add` 的定义等式在定义上成立，{leanRef}`mul`
也是如此。方程编译器会尽可能确保这一点；直接的结构归纳正是这种情形。
然而在其他情形中，归约只在 _命题上_ 成立，也就是说，它们是必须显式应用的
等式定理。方程编译器会在内部生成这样的定理。它们并不意在由用户直接使用；
相反，{tactic}`simp` 策略会被配置为在必要时使用它们。下面的
{leanRef}`zero_add` 证明就是这样工作的：

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)
-----
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

与通过模式匹配进行定义一样，结构递归或结构归纳的参数也可以出现在冒号之前。
这样的参数只是在处理定义之前被加入局部上下文。例如，加法的定义也可以写成：

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

你也可以用 {kw}`match` 来书写上面的例子。

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

:::leanFirst
Fibonacci 函数 {leanRef}`fib` 给出了一个更有趣的结构递归例子。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl

example : fib 1 = 1 := rfl

example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```
:::
:::setup
```
variable (n : Nat)
open Nat
```

这里，{leanRef}`fib` 函数在 {leanRef}`n + 2`（它在定义上等于
{lean}`succ (succ n)`）处的值，是用它在 {leanRef}`n + 1`（它在定义上等价于
{lean}`succ n`）处的值以及在 {leanRef}`n` 处的值来定义的。不过，
这是计算 Fibonacci 函数的一种众所周知的低效方式，其运行时间关于 {lean}`n`
呈指数增长。下面是一种更好的方法：
:::

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100 -- 573147844013817084101
```

下面是使用 {kw}`let rec` 而不是 {kw}`where` 的同一定义。

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

在这两种情形中，Lean 都会生成辅助函数 {lit}`fibFast.loop`。

:::leanFirst
为了处理结构递归，方程编译器使用 _值历程_ 递归；它使用随每个归纳定义类型
自动生成的常量 {lit}`below` 和 {lit}`brecOn`。通过查看 {leanRef}`Nat.below`
和 {leanRef}`Nat.brecOn` 的类型，你可以大致了解其工作方式：

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```
:::
:::setup
```
variable (C : Nat → Type u) (n : Nat)
```
类型 {lean}`@Nat.below C (3 : Nat)` 是一个数据结构，存储 {lean}`C 0`、
{lean}`C 1` 和 {lean}`C 2` 的元素。值历程递归由 {name}`Nat.brecOn` 实现。
它使我们能够依据函数此前的所有值，来定义类型为 {lean}`(n : Nat) → C n`
的依值函数在特定输入 {lean}`n` 处的值；这些此前的值以
{lean}`@Nat.below C n` 的一个元素给出。
:::

:::leanFirst
使用值历程递归，是方程编译器向 Lean 内核证明函数终止的技术之一。
它并不影响代码生成器；后者会像其他函数式编程语言编译器那样编译递归函数。
回忆一下，{kw}`#eval`{lit}` ` {leanRef}`fib`{lit}` <n>` 关于 {lit}`<n>`
是指数时间的。另一方面，{kw}`#reduce`{lit}` `{leanRef}`fib`{lit}` <n>`
却很高效，因为它使用发送给内核、基于 {lit}`brecOn` 构造的定义。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- 慢：
-- #eval fib 50
-- 快：
#reduce fib 50

#print fib
```
:::

:::leanFirst
递归定义的另一个好例子是列表的 {leanRef}`append` 函数。

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```
:::

再看另一个例子：它把第一个列表的元素与第二个列表的元素相加，
直到两个列表中有一个耗尽为止。

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10] -- [5, 7, 9]
```

建议你在下面的练习中尝试类似的例子。

# 局部递归声明
%%%
tag := "local-recursive-declarations"
%%%

你可以使用 {kw}`let rec` 关键字定义局部递归声明。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop -- @replicate.loop : {α : Type u_1} → α → Nat → List α → List α
```

Lean 会为每个 {leanRef}`let rec` 创建一个辅助声明。在上面的例子中，
它为 {leanRef}`replicate` 中出现的 {leanRef}`let rec loop` 创建了声明
{leanRef}`replicate.loop`。请注意，Lean 会把 {leanRef}`let rec` 声明中出现的
任何局部变量作为额外参数加入，从而“闭合”该声明。例如，局部变量
{leanRef}`a` 出现在 {leanRef}`let rec loop` 中。


你也可以在策略模式中使用 {leanRef}`let rec`，并用它创建归纳证明。

```lean
def replicate (n : Nat) (a : α) : List α :=
 let rec loop : Nat → List α → List α
   | 0,   as => as
   | n+1, as => loop n (a::as)
 loop n []
------
theorem length_replicate (n : Nat) (a : α) :
    (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α) :
      (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]
  exact aux n []
```

你还可以在定义之后使用 {kw}`where` 子句引入辅助递归声明。
Lean 会把它们转换为 {kw}`let rec`。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) :
    (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α) :
      (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]
```

# 良基递归与归纳
%%%
tag := "well-founded-recursion-and-induction"
%%%

当无法使用结构递归时，我们可以用良基递归来证明终止性。我们需要一个良基关系，
以及一个证明，说明每个递归应用相对于这个关系都是递减的。依值类型论强大到
足以编码并论证良基递归的正当性。让我们从理解其工作方式所需的逻辑背景开始。

:::setup
```
variable (α : Type u) (a : α) (r : α → α → Prop)
```

Lean 的标准库定义了两个谓词：{lean}`Acc r a` 和 {lean}`WellFounded r`。
其中 {lean}`r` 是类型 {lean}`α` 上的二元关系，而 {lean}`a` 是类型
{lean}`α` 的一个元素。
:::

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

```lean (show := false)
variable {α : Sort u} (x y : α)
variable {r : α → α → Prop}

example : Acc r x = ∀ y, r y x → Acc r y := by
  simp only [eq_iff_iff]
  constructor
  . intro ⟨_, hAcc⟩
    assumption
  . intro h
    constructor
    assumption

def r' : α → α → Prop := fun x y => True
infix:50 " ≺ " => r'
example : y ≺ x := True.intro
example := WellFounded r
```


第一个谓词 {leanRef}`Acc` 是一个归纳定义的谓词。按照它的定义，
{leanRef}`Acc r x` 等价于 {leanRef}`∀ y, r y x → Acc r y`。如果把
{leanRef}`r y x` 理解为某种序关系 {leanRef}`y ≺ x`，那么
{leanRef}`Acc r x` 表示 {leanRef}`x` 可从下方到达，也就是说它的所有前驱
都是可到达的。特别地，如果 {leanRef}`x` 没有前驱，那么它就是可到达的。
给定任意类型 {leanRef}`α`，我们应当能够以递归方式为 {leanRef}`α` 的
每个可到达元素赋值：先为其所有前驱赋值，再为它本身赋值。



断言 {leanRef}`r` 是良基的，记为 {leanRef}`WellFounded r`，正是断言该类型的
每个元素都是可到达的。根据上述考虑，如果 {leanRef}`r` 是类型
{leanRef}`α` 上的良基关系，那么相对于关系 {leanRef}`r`，我们就应当有一个
{leanRef}`α` 上的良基递归原理。事实上也确实如此：标准库定义了
{name}`WellFounded.fix`，它正是为此目的服务的。

```lean
noncomputable
def f {α : Sort u}
    (r : α → α → Prop)
    (h : WellFounded r)
    (C : α → Sort v)
    (F : (x : α) → ((y : α) → r y x → C y) → C x) :
    (x : α) → C x :=
WellFounded.fix h F
```

这里出现了一长串角色，但第一组我们已经见过：类型 {leanRef}`α`、关系
{leanRef}`r`，以及假设 {leanRef}`h`，即 {leanRef}`r` 是良基的。变量
{leanRef}`C` 表示递归定义的动机：对于每个元素 {leanRef}`x : α`，
我们希望构造一个 {leanRef}`C x` 的元素。函数 {leanRef}`F` 提供了完成此事的
归纳配方：给定 {leanRef}`x` 的每个前驱 {leanRef}`y` 的 {leanRef}`C y`
元素，它告诉我们如何构造一个 {leanRef}`C x` 的元素。

:::setup
```
variable {x y : α} (C : α → Sort v) (r : α → α → Prop)

```

注意，{name}`WellFounded.fix` 同样可以作为归纳原理使用。它说明，
如果 {leanRef}`≺` 是良基的，而你想证明 {lean}`∀ x, C x`，那么只需证明：
对任意 {lean}`x`，若有 {lean}`∀ y, r y x → C y`，则有 {lean}`C x`。
:::

在上面的例子中，我们使用修饰符 {leanRef}`noncomputable`，因为代码生成器
目前不支持 {name}`WellFounded.fix`。函数 {name}`WellFounded.fix` 是 Lean 用来
论证函数终止的另一种工具。

Lean 知道自然数上的通常次序 {lit}`<` 是良基的。它还知道多种从已有良基序
构造新良基序的方法，例如使用字典序。

下面基本上就是标准库中自然数除法的定义。

```lean
------
open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

:::TODO
示例缺少高亮
:::
这个定义有些难以看懂。这里递归发生在 {leanRef (in:="def div.F (x")}`x` 上，
而 {lit}`div.F x f : Nat → Nat` 会为这个固定的
{leanRef (in:="def div.F (x")}`x` 返回“除以 {leanRef}`y`”的函数。你必须记住，
{leanRef}`div.F` 的第二个参数，即递归的配方，是一个函数；它应当为所有小于
{leanRef}`x` 的值 {leanRef}`x₁` 返回相应的除以 {leanRef}`y` 的函数。

精化器的设计目标之一就是让这类定义更方便。它接受如下写法：

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0
```

当 Lean 遇到递归定义时，它会首先尝试结构递归；只有在失败时，
才退回到良基递归。Lean 使用策略 {tactic}`decreasing_tactic` 来证明
递归应用更小。上例中的辅助命题 {leanRef}`x - y < x` 应当被视为给该策略的提示。

{leanRef}`div` 的定义等式 _并不_ 在定义上成立，但我们可以使用
{tactic}`unfold` 策略展开 {leanRef}`div`。我们使用 {ref "conv"}[{tactic}`conv`]
来选择要展开哪一个 {leanRef}`div` 应用。

```lean
def div (x y : Nat) : Nat :=
 if h : 0 < y ∧ y ≤ x then
   have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
   div (x - y) y + 1
 else
   0
------
example (x y : Nat) :
    div x y =
    if 0 < y ∧ y ≤ x then
      div (x - y) y + 1
    else 0 := by
  -- 展开等式左侧出现的项：
  conv => lhs; unfold div
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) :
    div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

:::leanFirst
下面的例子类似：它把任意自然数转换为二进制表达式，表示为由 0 和 1 组成的列表。
我们必须提供证据说明递归调用是递减的；这里我们用 {leanRef}`sorry` 完成这一点。
{leanRef}`sorry` 不会阻止解释器成功求值该函数，但当项中含有 {leanRef}`sorry`
时，必须使用 {leanRef}`#eval!` 而不是 {kw}`#eval`。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval! natToBin 1234567
```
:::

:::leanFirst
作为最后一个例子，我们注意到 Ackermann 函数可以直接定义，因为它由自然数上的
字典序的良基性来保证。{leanRef}`termination_by` 子句指示 Lean 使用字典序。
这个子句实际上把函数参数映射到类型 {lean}`Nat × Nat` 的元素。然后，Lean
使用类型类解析合成一个类型为 {lean}`WellFoundedRelation (Nat × Nat)` 的元素。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
```
:::

在许多情况下，Lean 可以自动确定一个适当的字典序。Ackermann 函数就是这样的
情形之一，因此 {leanRef}`termination_by` 子句是可选的：

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
```

:::setup
```
variable {α : Type u} {β : Type v}
```

注意，上面的例子之所以使用字典序，是因为实例
{lean}`WellFoundedRelation (α × β)` 使用字典序。Lean 还定义了实例

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```
:::

:::leanFirst
在下面的例子中，我们通过说明递归应用中 {leanRef}`as.size - i` 是递减的，
来证明终止性。

```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i
```
:::
注意，在这个例子中辅助函数 {leanRef}`go` 是递归的，而 {leanRef}`takeWhile`
并不是。再一次，Lean 可以自动识别这种模式，因此 {leanRef}`termination_by`
子句并非必要：
```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
```

:::leanFirst
默认情况下，Lean 使用策略 {tactic}`decreasing_tactic` 来证明递归应用是递减的。
修饰符 {leanRef}`decreasing_by` 允许我们提供自己的策略。下面是一个例子。

```lean
theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption
```
:::

注意，{leanRef}`decreasing_by` 不是 {leanRef}`termination_by` 的替代品；
二者是相辅相成的。{leanRef}`termination_by` 用于指定良基关系，
而 {leanRef}`decreasing_by` 用于提供我们自己的策略，以证明递归应用是递减的。
在下面的例子中，我们同时使用二者。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
  -- 展开良基递归的辅助定义：
  all_goals simp_wf
  · apply Prod.Lex.left; simp +arith
  · apply Prod.Lex.right; simp +arith
  · apply Prod.Lex.left; simp +arith
```

:::leanFirst
我们可以使用 {leanRef}`decreasing_by sorry` 来指示 Lean “相信”该函数会终止。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval! natToBin 1234567
```
:::

:::leanFirst
回忆一下，使用 {leanRef}`sorry` 等同于使用一个新的公理，应当避免。下面的例子中，
我们用 {leanRef}`sorry` 证明了 {leanRef}`False`。命令
{leanRef}`#print axioms unsound` 表明，{leanRef}`unsound` 依赖于用于实现
{lean}`sorry` 的不可靠公理 {lit}`sorryAx`。

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` 是 `False` 的证明

#print axioms unsound -- 'unsound' 依赖于公理：[sorryAx]
```
:::

:::setup
```
variable {α : Type w} {β  : Type u} {γ : Type v} {G : Prop}
```

总结：

- 如果没有 {leanRef}`termination_by`，Lean 会（在可能时）通过选择一个参数，
  然后使用类型类解析为该参数的类型合成一个良基关系，从而导出良基关系。

- 如果指定了 {leanRef}`termination_by`，它会把函数参数映射到某个类型 {lean}`α`，
  然后再次使用类型类解析。回忆一下，{lean}`β × γ` 的默认实例是基于
  {lean}`β` 和 {lean}`γ` 的良基关系构造的字典序。

- {lean}`Nat` 的默认良基关系实例是 {lean (type := "Nat → Nat → Prop")}`(· < ·)`。

- 默认情况下，策略 {tactic}`decreasing_tactic` 用于说明递归应用相对于所选的
  良基关系更小。如果 {tactic}`decreasing_tactic` 失败，错误信息会包含剩余目标
  {lit}`... |- G`。注意，{tactic}`decreasing_tactic` 会使用 {tactic}`assumption`。
  因此，你可以包含一个 {kw}`have` 表达式来证明目标 {lean}`G`。你也可以使用
  {kw}`decreasing_by` 提供自己的策略。
:::

# 函数式归纳
%%%
tag := "functional-induction"
%%%

Lean 会为递归函数生成专门的归纳原理。这些归纳原理遵循函数定义的递归结构，
而不是数据类型的结构。关于函数的证明通常遵循函数自身的递归结构，
因此这些归纳原理使得关于函数的陈述可以更方便地得到证明。

:::leanFirst
例如，使用 {leanRef}`ack` 的函数式归纳原理来证明结果总是大于 {leanRef}`0`，
需要为 {leanRef}`ack` 中模式匹配的每个分支处理一个情形：

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack with
  | case1 y =>
--          ^ PROOF_STATE: case1
    simp
  | case2 x ih =>
--             ^ PROOF_STATE: case2
    exact ih
  | case3 x y ih1 ih2 =>
--                    ^ PROOF_STATE: case3
    simp [ack, *]
```
:::

在 {goal case1}`case1` 中，目标是：
```proofState case1
case case1
y : Nat
⊢ y + 1 > 0
```
目标中的 {leanRef}`y + 1` 对应于 {leanRef}`ack` 第一种情形返回的值。

在 {goal case2}`case2` 中，目标是：
```proofState case2
case case2
x : Nat
ih : ack x 1 > 0
⊢ ack x 1 > 0
```
目标中的 {leanRef}`ack x 1` 对应于把 {leanRef}`ack` 应用于模式变量
{leanRef}`x + 1` 和 {leanRef}`0` 后，在 {leanRef}`ack` 第二种情形中返回的值。
这个项会自动简化为右侧。令人满意的是，归纳假设
{leanRef}`ih : ack x 1 > 0` 对应于递归调用，而它正是该情形返回的答案。

在 {goal case3}`case3` 中，目标是：
```proofState case3
case case3
x : Nat
y : Nat
ih1 : ack (x + 1) y > 0
ih2 : ack x (ack (x + 1) y) > 0
⊢ ack x (ack (x + 1) y) > 0
```
目标中的 {leanRef}`ack x (ack (x + 1) y)` 对应于 {leanRef}`ack` 的第三种情形
返回的值，此时应用于 {leanRef}`x + 1` 和 {leanRef}`y + 1` 的 {leanRef}`ack`
已经被归约。归纳假设 {leanRef}`ih1 : ack (x + 1) y > 0` 和
{leanRef}`ih2 : ack x (ack (x + 1) y) > 0` 对应于递归调用，其中
{leanRef}`ih1` 匹配嵌套的递归调用。归纳假设再次正好适用。

使用 {leanRef}`fun_induction ack` 会得到与 {leanRef}`ack` 的递归结构相匹配的
目标和归纳假设。因此，证明可以写成一行：
```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
-------------
theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack <;> simp [*, ack]
```

:::leanFirst
还有一个 {leanRef}`fun_cases` 策略，它类似于 {tactic}`cases` 策略。
它会为函数控制流中的每个分支生成一个情形。它和 {leanRef}`fun_induction`
还会额外提供假设，以排除未被采用的路径。

函数 {leanRef}`f` 表示一个五路布尔析取：
```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x

```

为了证明它确实是析取，最后一个情形需要知道所有参数都不是 {leanRef}`true`。
这一信息由该策略提供：
```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x
------
theorem f_or : f b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases f
-- ^ PROOF_STATE: fOrAll
  all_goals sorry
```
:::

每个情形都包含一个排除先前情形的假设：

```proofState fOrAll
case case1
b2 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
⊢ true = (true || b2 || b3 || b4 || b5)

case case2
b1 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
x✝ : b1 = true → False
⊢ true = (b1 || true || b3 || b4 || b5)

case case3
b1 : Bool
b2 : Bool
b4 : Bool
b5 : Bool
x✝¹ : b1 = true → False
x✝ : b2 = true → False
⊢ true = (b1 || b2 || true || b4 || b5)

case case4
b1 : Bool
b2 : Bool
b3 : Bool
b5 : Bool
x✝² : b1 = true → False
x✝¹ : b2 = true → False
x✝ : b3 = true → False
⊢ true = (b1 || b2 || b3 || true || b5)

case case5
b1 : Bool
b2 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
x✝³ : b1 = true → False
x✝² : b2 = true → False
x✝¹ : b3 = true → False
x✝ : b4 = true → False
⊢ b5 = (b1 || b2 || b3 || b4 || b5)
```

:::leanFirst
{leanRef}`simp_all` 策略会同时简化所有假设和目标，它可以处理全部情形：
```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x
------
theorem f_or : f b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases f <;> simp_all
```
:::


# 相互递归
%%%
tag := "mutual-recursion"
%%%

Lean 也支持相互递归定义。其语法类似于相互归纳类型的语法。下面是一个例子：

```lean
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]
```

之所以这是一个相互定义，是因为 {leanRef}`even` 递归地用 {leanRef}`odd` 定义，
而 {leanRef}`odd` 又递归地用 {leanRef}`even` 定义。在幕后，这会被编译为
一个单一的递归定义。内部定义的函数以一个和类型的元素为参数：它要么是
{leanRef}`even` 的输入，要么是 {leanRef}`odd` 的输入。然后它返回适合该输入的输出。
为了定义这个函数，Lean 使用一个适当的良基度量。内部细节意在对用户隐藏；
使用这类定义的规范方式是像上面那样使用 {leanRef}`simp`（或 {tactic}`unfold`）。

:::leanFirst
相互递归定义也为处理相互归纳类型和嵌套归纳类型提供了自然方式。回忆一下，
前面曾把 {leanRef}`Even` 和 {leanRef}`Odd` 定义为相互归纳谓词。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end
```
:::

:::leanFirst
构造子 {leanRef}`even_zero`、{leanRef}`even_succ` 和 {leanRef}`odd_succ`
提供了证明一个数为偶数或奇数的正向手段。我们需要利用归纳类型由这些构造子生成
这一事实，来知道零不是奇数，并且后两个蕴含可以反向使用。照例，构造子保存在
以所定义类型命名的命名空间中，而命令 {leanRef}`open Even Odd` 使我们能够更方便地访问它们。

```lean
mutual
 inductive Even : Nat → Prop where
   | even_zero : Even 0
   | even_succ : ∀ n, Odd n → Even (n + 1)
 inductive Odd : Nat → Prop where
   | odd_succ : ∀ n, Even n → Odd (n + 1)
end
------
open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h
```
:::

再看一个例子。假设我们使用嵌套归纳类型来归纳地定义一组项，使得一个项要么是
常量（其名称由字符串给出），要么是把一个常量应用于一列常量所得的结果。

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

于是我们可以使用相互递归定义来计算一个项中出现的常量个数，以及一列项中出现的常量个数。

```lean
inductive Term where
 | const : String → Term
 | app   : String → List Term → Term
------
namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]

#eval numConsts sample

end Term
```

:::leanFirst
作为最后一个例子，我们定义函数 {leanRef}`replaceConst a b e`，它在项
{leanRef (in := "replaceConst a b e")}`e` 中把常量
{leanRef (in := "replaceConst a b e")}`a` 替换为
{leanRef (in := "replaceConst a b e")}`b`，然后证明常量个数保持不变。
注意，我们的证明使用相互递归（也即归纳）。

```lean
inductive Term where
 | const : String → Term
 | app   : String → List Term → Term
namespace Term
mutual
 def numConsts : Term → Nat
   | const _ => 1
   | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
   | [] => 0
   | c :: cs => numConsts c + numConstsLst cs
end
------
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term) :
      numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c =>
      simp [replaceConst]; split <;> simp [numConsts]
    | app f cs =>
      simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term) :
      numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
```
:::

# 依值模式匹配
%%%
tag := "dependent-pattern-matching"
%%%


::::setup
```
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

def map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

def zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def unzip : Vect (α × β) n → (Vect α n × Vect β n)
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

def tail : Vect α (n + 1) → Vect α n
  | .cons x xs => xs

variable {v : Vect α (n + 1)}
open Vect
```

:::leanFirst
我们在 {ref "pattern-matching"}[模式匹配] 一节中讨论过的所有模式匹配例子，
都可以很容易地用 {lit}`casesOn` 和 {lit}`recOn` 写出。然而，对于
{leanRef}`Vect α n` 这样的带索引归纳族，情况通常并非如此，因为情形区分会
对索引值施加约束。若没有方程编译器，我们就需要大量样板代码，才能用递归子
定义 {lean}`map`、{lean}`zip` 和 {lean}`unzip` 这样非常简单的函数。
为理解其中困难，考虑定义一个函数 {lean}`tail` 需要做什么；它接受一个向量
{lean}`v : Vect α (n + 1)` 并删除第一个元素。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::



第一个想法可能是使用 {name}`Vect.casesOn` 函数：

```signature
Vect.casesOn.{u, v}
  {α : Type v} {motive : (a : Nat) → Vect α a → Sort u}
  {a : Nat}
  (t : Vect α a)
  (nil : motive 0 nil)
  (cons : (a : α) → {n : Nat} → (a_1 : Vect α n) →
    motive (n + 1) (cons a a_1)) :
  motive a t
```


但是在 {name}`nil` 情形中我们应当返回什么值？这里出现了一个微妙之处：
如果 {lean}`v` 的类型是 {lean}`Vect α (n + 1)`，它 _不可能_ 是 {name}`nil`，
但并不清楚如何把这一点告诉 {name}`Vect.casesOn`。

::::

一种解决方案是定义一个辅助函数：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def tailAux (v : Vect α m) : m = n + 1 → Vect α n :=
  Vect.casesOn (motive := fun x _ => x = n + 1 → Vect α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vect α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vect α (n+1)) : Vect α n :=
  tailAux v rfl
-----
end Vect
```

在 {leanRef}`nil` 情形中，{leanRef (in := "m = n + 1")}`m` 被实例化为
{leanRef}`0`，而 {leanRef}`Nat.noConfusion` 利用 {leanRef}`0 = n + 1`
不可能发生这一事实。否则，{leanRef}`v` 形如
{lit}`cons `{leanRef}`a`{lit}` `{leanRef}`as`，我们只需把 {leanRef}`as`
从长度为 {leanRef (in := "m + 1 = n + 1")}`m` 的向量强制转换为长度为
{leanRef (in := "m + 1= n + 1")}`n` 的向量，然后返回它。

定义 {leanRef}`tail` 的困难在于维持索引之间的关系。{leanRef}`tailAux` 中的
假设 {leanRef}`m = n + 1` 用来传达 {leanRef (in:="m = n + 1")}`n`
与小前提相关索引之间的关系。此外，{leanRef}`0 = n + 1` 情形不可达，
丢弃这类情形的规范方式是使用 {leanRef}`Nat.noConfusion`。

:::leanFirst
不过，使用递归方程定义 {leanRef}`tail` 函数很容易，方程编译器会为我们自动生成
所有样板代码。下面还有若干类似的例子：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def head : {n : Nat} → Vect α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vect α (n+1) → Vect α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vect α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vect α n → Vect β n → Vect (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
------
end Vect
```
:::

注意，我们可以省略诸如 {leanRef}`head`{lit}` `{leanRef}`nil` 这类
“不可达”情形的递归方程。为带索引族自动生成的定义远非直截了当。例如：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
-------
def zipWith (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (zipWith f as bs)

#print zipWith
#print zipWith.match_1
------
end Vect
```

:::setup
```
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
```

{leanRef}`zipWith` 函数手工定义起来甚至比 {leanRef}`tail` 函数更繁琐。
我们鼓励你使用 {name}`Vect.recOn`、{name}`Vect.casesOn` 和
{name}`Vect.noConfusion` 试一试。
:::

# 不可访问模式
%%%
tag := "inaccessible-patterns"
%%%

有时，依值匹配模式中的某个参数对于定义本身并非必要，但仍必须包含它，
以便适当地特化表达式的类型。Lean 允许用户把这样的子项标记为对模式匹配
_不可访问_。例如，当左侧出现的某个项既不是变量也不是构造子应用时，
这些标注就是必要的，因为这类项并不是模式匹配的合适目标。我们可以把这种
不可访问模式视为模式中“无关紧要”的组成部分。你可以通过写 {lit}`.(t)`
来声明某个子项不可访问。如果不可访问模式可以被推断，也可以写 {lit}`_`。

:::leanFirst
在下面的例子中，我们声明一个归纳类型，用来定义“属于
{leanRef (in := "(f :")}`f` 的像”这一性质。你可以把类型
{leanRef}`ImageOf f b` 的元素看作证据，说明
{leanRef (in := "ImageOf f b")}`b` 属于
{leanRef (in := "ImageOf f b")}`f` 的像；构造子 {leanRef}`imf` 用于构造这样的证据。
然后，我们可以为任意函数 {leanRef (in := "inverse {f")}`f` 定义一个“逆”，
它把 {leanRef (in := "inverse {f")}`f` 的像中的任何东西送到一个映到它的元素。
类型规则迫使我们为第一个参数写出 {leanRef (in := ".(f a)")}`f a`，但这个项既不是变量
也不是构造子应用，并且在模式匹配定义中不起作用。为了定义下面的函数
{leanRef}`inverse`，我们 _必须_ 把 {leanRef (in := ".(f a)")}`f a` 标记为不可访问。

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```
:::

在上面的例子中，不可访问标注清楚表明 {leanRef (in := ".(f a)")}`f`
_不是_ 模式匹配变量。

:::leanFirst
不可访问模式可用于澄清并控制使用依值模式匹配的定义。考虑函数
{leanRef}`Vect.add` 的如下定义；在假设某类型带有相应加法函数的前提下，
它将该类型元素构成的两个向量相加：

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

def Vect.add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)
```
:::

参数 {leanRef}`{n : Nat}` 出现在冒号之后，因为在整个定义中它不能保持固定。
实现这个定义时，方程编译器首先根据第一个参数是 {leanRef}`0` 还是形如
{leanRef}`n+1` 进行情形区分。随后它对接下来的两个参数进行嵌套情形区分；
在每个情形中，方程编译器都会排除与第一个模式不兼容的情形。

但事实上，并不需要对第一个参数作情形区分；当我们对第二个参数作情形区分时，
{lit}`Vect` 的 {lit}`casesOn` 消去子会自动抽象这个参数，并把它替换为
{leanRef}`0` 和 {leanRef}`n + 1`。使用不可访问模式，我们可以提示方程编译器
避免对 {leanRef}`n` 作情形区分。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

把该位置标记为不可访问模式，会告诉方程编译器两件事：第一，
该参数的形式应当由其他参数施加的约束推断出来；第二，第一个参数 _不应_
参与模式匹配。

为方便起见，不可访问模式 {leanRef}`.(_)` 可以写作 {lit}`_`。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

如上所述，参数 {leanRef}`{n : Nat}` 是模式匹配的一部分，因为它不能在整个定义中
保持固定。Lean 并不要求显式提供这些判别项，而是会为我们自动隐式包含这些额外判别项。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] {n : Nat} : Vect α n → Vect α n → Vect α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

结合 _自动绑定隐式参数_ 功能后，你可以进一步简化声明，写成：

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : Vect α n → Vect α n → Vect α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

利用这些新功能，你可以把前几节定义的其他向量函数更紧凑地写成如下形式：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def head : Vect α (n+1) → α
  | cons a as => a

def tail : Vect α (n+1) → Vect α n
  | cons a as => as

theorem eta : (v : Vect α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vect α n → Vect β n → Vect (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
-------
end Vect
```

# 匹配表达式
%%%
tag := "match-expressions"
%%%

Lean 还为许多函数式语言中出现的 {kw}`match`-{kw}`with` 表达式提供了编译器：

```lean
set_option linter.unusedVariables false
------
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0     => false
  | n + 1 => true
```

这看起来与普通的模式匹配定义差别不大，但关键在于，{kw}`match` 可以在表达式中的
任意位置使用，并且可以带任意参数。

```lean
set_option linter.unusedVariables false
-------
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0     => false
  | n + 1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

下面是另一个例子：

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,     true  => 0
      | m + 1, true  => m + 7
      | 0,     false => 5
      | m + 1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

Lean 在内部使用 {kw}`match` 构造来实现系统各处的模式匹配。因此，下面四个定义
具有相同的最终效果：

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

这些变体对于析构命题同样有用：

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```


# 练习
%%%
tag := "induction-and-recursion-exercises"
%%%

```setup

open List

variable {xs : List α} {n : Nat}

```

1. 打开一个命名空间 {lit}`Hidden` 以避免命名冲突，并使用方程编译器定义
   自然数上的加法、乘法和幂运算。然后使用方程编译器导出它们的一些基本性质。

2. 类似地，使用方程编译器定义列表上的一些基本操作（如 {lean}`reverse` 函数），
   并通过归纳证明关于列表的定理（例如对任意列表 {lean}`xs`，
   都有 {lean}`reverse (reverse xs) = xs`）。

3. 定义你自己的函数，在自然数上执行值历程递归。类似地，看看你是否能自己想出
   如何定义 {name}`WellFounded.fix`。

4. 仿照 {ref "dependent-pattern-matching"}[依值模式匹配] 一节中的例子，
   定义一个能连接两个向量的函数。这有些棘手；你需要定义一个辅助函数。

5.  :::leanFirst

    考虑下面的算术表达式类型。其思想是，{leanRef}`var`{lit}` `{lean}`n`
    是一个变量 {lit}`vₙ`，而 {leanRef}`const`{lit}` `{lean}`n`
    是值为 {lean}`n` 的常量。

    ```lean
    inductive Expr where
      | const : Nat → Expr
      | var : Nat → Expr
      | plus : Expr → Expr → Expr
      | times : Expr → Expr → Expr
    deriving Repr

    open Expr

    def sampleExpr : Expr :=
      plus (times (var 0) (const 7)) (times (const 2) (var 1))
    ```
    :::

    这里 {leanRef}`sampleExpr` 表示 {lit}`(v₀ * 7) + (2 * v₁)`。

    :::leanFirst
    写一个函数对此类表达式求值，将每个 {leanRef}`var n` 求值为 {leanRef}`v n`。

    ```lean
    inductive Expr where
      | const : Nat → Expr
      | var : Nat → Expr
      | plus : Expr → Expr → Expr
      | times : Expr → Expr → Expr
      deriving Repr
    open Expr
    def sampleExpr : Expr :=
      plus (times (var 0) (const 7)) (times (const 2) (var 1))
    ------
    def eval (v : Nat → Nat) : Expr → Nat
      | const n     => sorry
      | var n       => v n
      | plus e₁ e₂  => sorry
      | times e₁ e₂ => sorry

    def sampleVal : Nat → Nat
      | 0 => 5
      | 1 => 6
      | _ => 0

    -- 试一试。这里应当得到 47。
    -- #eval eval sampleVal sampleExpr
    ```
    :::

    :::leanFirst
    实现“常量融合”：这是一个把 {lean}`5 + 7` 这样的子项简化为 {lean}`12`
    的过程。使用辅助函数 {leanRef}`simpConst`，定义一个函数 “fuse”：
    为了简化加法或乘法，先递归地简化参数，然后应用 {leanRef}`simpConst`
    尝试简化结果。

    ```lean
    inductive Expr where
      | const : Nat → Expr
      | var : Nat → Expr
      | plus : Expr → Expr → Expr
      | times : Expr → Expr → Expr
      deriving Repr
    open Expr
    def eval (v : Nat → Nat) : Expr → Nat
      | const n     => sorry
      | var n       => v n
      | plus e₁ e₂  => sorry
      | times e₁ e₂ => sorry
    ------
    def simpConst : Expr → Expr
      | plus (const n₁) (const n₂)  => const (n₁ + n₂)
      | times (const n₁) (const n₂) => const (n₁ * n₂)
      | e                           => e

    def fuse : Expr → Expr := sorry

    theorem simpConst_eq (v : Nat → Nat)
            : ∀ e : Expr, eval v (simpConst e) = eval v e :=
      sorry

    theorem fuse_eq (v : Nat → Nat)
            : ∀ e : Expr, eval v (fuse e) = eval v e :=
      sorry
    ```
    :::

    最后两个定理表明这些定义保持取值不变。
