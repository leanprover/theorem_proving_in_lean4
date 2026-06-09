import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "归纳类型" =>
%%%
tag := "inductive-types"
file := "Inductive-Types"
%%%

:::setup
```
variable {α : Sort u} {β : Sort v}
```


我们已经看到，Lean 的形式化基础包括基本类型
{lean}`Prop`、{lean}`Type 0`、{lean}`Type 1`、{lean}`Type 2`、……，并允许形成
依赖函数类型 {lean}`(x : α) → β`。在例子中，我们还使用了诸如 {lean}`Bool`、
{lean}`Nat` 和 {lean}`Int` 这样的其他类型，以及诸如 {lean}`List` 和乘积
{lit}`×` 这样的类型构造子。事实上，在 Lean 的库中，除宇宙之外的每个具体类型，
以及除依赖箭头之外的每个类型构造子，都是称为_归纳类型_的一般类型构造族的实例。
值得注意的是，仅凭类型宇宙、依赖箭头类型和归纳类型，就可以构筑起相当宏大的数学大厦；
其余一切都由此而来。
:::

直观地说，归纳类型由一组指定的构造子构成。在 Lean 中，指定这种类型的语法如下：

:::setup
```
variable {α β ω : Type}

inductive Foo where
  | constructor₁ : α → Foo
  | constructor₂ : β → Foo
  | constructorₙ : ω → Foo

```

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

直观含义是，每个构造子都指定了一种构造 {lean}`Foo` 的新对象的方法，
这些对象可能依赖于先前构造出的值。类型 {lean}`Foo` 只包含以这种方式构造出的对象。



我们将在下文看到，构造子的参数可以包含类型 {lean}`Foo` 的对象，但须满足某种
“正性”约束；该约束保证 {lean}`Foo` 的元素是自底向上构造的。粗略地说，每个
{lit}`...` 都可以是由 {lean}`Foo` 和先前定义的类型构成的任意箭头类型，其中
{lean}`Foo` 即便出现，也只能作为依赖箭头类型的“目标”。
:::

我们将给出若干归纳类型的例子。我们还会考察上述模式的轻微推广，包括相互定义的归纳类型，
以及所谓的_归纳族_。

与逻辑联结词一样，每个归纳类型都配有引入规则和消去规则：前者说明如何构造该类型的元素，
后者说明如何在另一个构造中“使用”该类型的元素。它们与逻辑联结词的类比并不令人意外；
正如下文将看到的，逻辑联结词本身也是归纳类型构造的例子。你已经见过归纳类型的引入规则：
它们正是类型定义中指定的构造子。消去规则给出了该类型上的递归原则，而归纳原则也是它的一个特例。

在下一章中，我们将介绍 Lean 的函数定义机制，它提供了更便捷的方法来在归纳类型上定义函数并进行归纳证明。
不过，由于归纳类型这一概念如此基础，我们认为从底层的、动手式的理解开始非常重要。
我们将从一些基本的归纳类型例子出发，逐步推进到更精细、更复杂的例子。

# 枚举类型
%%%
tag := "enumerated-types"
%%%

最简单的归纳类型，是具有有限个、逐一枚举的元素的类型。

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

{kw}`inductive` 命令创建一个新类型 {leanRef}`Weekday`。所有构造子都位于
{lit}`Weekday` 命名空间中。

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
#check Weekday.sunday

#check Weekday.monday

open Weekday

#check sunday

#check monday
```

在声明 {leanRef}`Weekday` 归纳类型时，可以省略 {leanRef}`: Weekday`。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

:::setup
```
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

可以把 {leanRef}`sunday`、{leanRef}`monday`、……、{leanRef}`saturday` 看成
{leanRef}`Weekday` 的彼此不同的元素，除此之外没有其他区分性质。消去原则
{name}`Weekday.rec` 会与类型 {leanRef}`Weekday` 及其构造子一同定义。它也称为_递归子_，
并且正是它使这个类型成为“归纳”的：它允许我们通过为每个构造子指定相应的值，
来定义 {leanRef}`Weekday` 上的函数。直观地说，归纳类型由其构造子穷尽生成，
除了这些构造子构造出的元素之外没有其他元素。

```signature
Weekday.rec.{u} {motive : Weekday → Sort u}
  (sunday : motive Weekday.sunday)
  (monday : motive Weekday.monday)
  (tuesday : motive Weekday.tuesday)
  (wednesday : motive Weekday.wednesday)
  (thursday : motive Weekday.thursday)
  (friday : motive Weekday.friday)
  (saturday : motive Weekday.saturday)
  (t : Weekday) :
  motive t
```

:::

:::leanFirst
我们将使用 {kw}`match` 表达式来定义一个从 {leanRef}`Weekday` 到自然数的函数：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1

#eval numberOfDay Weekday.monday  -- 2

#eval numberOfDay Weekday.tuesday -- 3
```

在使用 Lean 的逻辑时，{kw}`match` 表达式会通过声明归纳类型时生成的_递归子_
{leanRef}`Weekday.rec` 编译。这保证所得项在类型论中是良定义的。对于编译后的代码，
{kw}`match` 则像其他函数式编程语言中那样编译。
:::

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay

#print numberOfDay.match_1

#print Weekday.casesOn

#check @Weekday.rec
```

:::leanFirst
声明归纳数据类型时，可以使用 {leanRef}`deriving Repr` 指示 Lean 生成一个函数，
把 {leanRef}`Weekday` 对象转换为文本。{kw}`#eval` 命令使用这个函数来显示
{leanRef}`Weekday` 对象。如果不存在 {lean}`Repr`，{kw}`#eval` 会尝试当场派生一个。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```
:::

把与某个结构相关的定义和定理放入同名命名空间中通常很有用。例如，我们可以把
{leanRef}`numberOfDay` 函数放在 {lit}`Weekday` 命名空间中。这样，当打开该命名空间后，
就可以使用较短的名称。

:::leanFirst
我们可以定义从 {leanRef}`Weekday` 到 {leanRef}`Weekday` 的函数：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
------
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday

#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```
:::

:::leanFirst
如何证明对任意 Weekday {leanRef}`d` 都有 {leanRef}`next (previous d) = d`
这一一般定理？可以使用 {kw}`match` 为每个构造子分别给出该断言的证明：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```
:::

使用策略证明时，我们可以更加简洁：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

下文的 {ref "tactics-for-inductive-types"}[归纳类型的策略] 将介绍更多专门用于利用归纳类型的策略。

注意，在 {tech}[propositions-as-types] 对应之下，我们既可以用 {kw}`match` 来定义函数，
也可以用它来证明定理。换言之，在 {tech}[propositions-as-types] 对应之下，分情况证明就是一种分情况定义，
只不过被“定义”的是一个证明，而不是一段数据。

Lean 库中的 {lean}`Bool` 类型就是枚举类型的一个实例。

```lean
namespace Hidden
------
inductive Bool where
  | false : Bool
  | true  : Bool
------
end Hidden
```

（为了运行这些例子，我们把它们放在名为 {lit}`Hidden` 的命名空间中，
使得像 {leanRef}`Bool` 这样的名称不会与标准库中的 {lean}`Bool` 冲突。
这是必要的，因为这些类型是 Lean “prelude”的一部分，会在系统启动时自动导入。）


作为练习，你应该思考这些类型的引入规则和消去规则分别做什么。进一步地，我们建议在
{lean}`Bool` 类型上定义布尔运算 {lean}`and`、{lean}`or`、{lean}`not`，
并验证常见恒等式。注意，可以用 {kw}`match` 定义像 {leanRef}`and` 这样的二元运算：

```lean
namespace Hidden
------
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
-------
end Hidden
```

类似地，大多数恒等式都可以通过引入合适的 {kw}`match`，然后使用 {lean}`rfl` 来证明。

# 带参数的构造子
%%%
tag := "constructors-with-arguments"
%%%

:::setup
```
variable (α : Type u) (β : Type v) (a : α) (b : β)
```


枚举类型是归纳类型的一个非常特殊的情形，其中构造子完全不接受参数。一般而言，
一个“构造”可以依赖于数据，而这些数据随后体现在被构造出的参数中。考虑库中乘积类型和和类型的定义：

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
-------
end Hidden
```

考察这些例子中发生了什么。乘积类型有一个构造子 {lean}`Prod.mk`，它接受两个参数。
要在 {leanRef}`Prod α β` 上定义函数，可以假设输入形如 {lean}`Prod.mk a b`，
并且必须用 {leanRef}`a` 和 {leanRef}`b` 来指定输出。我们可以利用这一点为
{leanRef}`Prod` 定义两个投影。请记住，标准库把 {lean}`Prod α β` 记作
{lean}`α × β`，把 {lean}`Prod.mk a b` 记作 {lean}`(a, b)`。

```lean
namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
------
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
--------
end Hidden
```

函数 {leanRef}`fst` 接受一个对 {leanRef}`p`。{kw}`match` 将 {leanRef}`p` 解释为一个对
{leanRef}`Prod.mk a b`。还请回忆 {ref "dependent-type-theory"}[依赖类型论] 中的内容：
为了使这些定义尽可能一般，我们允许类型 {leanRef}`α` 和 {leanRef}`β` 属于任意宇宙。

:::
:::setup
```
universe u_2 u_3 u_1
variable (b : Bool) {α : Type u} {t1 t2 : α}
```

下面是另一个例子，其中我们使用递归子
{lean (type := "{α : Type u_2} → {β : Type u_3} → {motive : α × β → Sort u_1} → (t : α × β) → ((fst : α) → (snd : β) → motive (fst, snd)) → motive t")}`Prod.casesOn`，
而不是 {kw}`match`。

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)

#eval prod_example (false, 3)
```

参数 {leanRef}`motive` 用来指定你想构造的对象的类型；它是一个函数，因为该类型可能依赖于这个对。
函数 {leanRef}`cond` 是布尔条件表达式：如果 {lean}`b` 为真，{lean}`cond b t1 t2`
返回 {lean}`t1`，否则返回 {lean}`t2`。函数 {leanRef}`prod_example` 接受一个由布尔值
{leanRef}`b` 和数 {leanRef}`n` 组成的对，并根据 {leanRef}`b` 为真还是为假，
返回 {leanRef}`2 * n` 或 {leanRef}`2 * n + 1`。
:::

:::setup
```
open Sum
variable {α : Type u} {β : Type v} (a : α) (b : β)
```

相比之下，和类型有_两个_构造子 {lean}`inl` 和 {lean}`inr`（分别表示“插入左边”和“插入右边”），
每个构造子接受_一个_（显式）参数。要在 {lean}`Sum α β` 上定义函数，我们必须处理两种情况：
输入要么形如 {lean}`inl a`，此时必须用 {leanRef}`a` 指定输出值；要么形如
{lean}`inr b`，此时必须用 {leanRef}`b` 指定输出值。

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)

#eval sum_example (Sum.inr 3)
```

:::

:::setup
```
open Sum
variable (n : Nat)
```

这个例子与前一个类似，但现在 {leanRef}`sum_example` 的输入隐含地要么形如
{lean}`inl n`，要么形如 {lean}`inr n`。在第一种情况下，函数返回 {lean}`2 * n`；
在第二种情况下，它返回 {lean}`2 * n + 1`。

:::

:::setup
```
variable {α β : Type} {a : α} {b : β}
open Sum
```


注意，乘积类型依赖于参数 {lean}`α β : Type`；这些参数既是构造子的参数，
也是 {lean}`Prod` 的参数。当 Lean 检测到这些参数可以从构造子的后续参数或返回类型中推断出来时，
就会把它们设为隐式参数。

在 {ref "defining-the-natural-numbers"}[定义自然数] 中，我们将看到当归纳类型的构造子接受来自该归纳类型自身的参数时会发生什么。
本节所考察例子的特征在于：每个构造子只依赖于先前指定的类型。

注意，具有多个构造子的类型具有析取性：{lean}`Sum α β` 的元素要么形如
{lean}`inl a`，_要么_形如 {lean}`inl b`。具有多个参数的构造子引入合取性信息：
从 {lean}`Prod α β` 的元素 {lean}`Prod.mk a b` 中，我们可以同时提取 {leanRef}`a`
_和_ {leanRef}`b`。任意归纳类型都可以同时包含这两种特征：它可以有任意多个构造子，
而每个构造子又可以接受任意多个参数。

:::

与函数定义一样，Lean 的归纳定义语法允许你把构造子的具名参数放在冒号之前：

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
-------
end Hidden
```

这些定义得到的结果与本节前面给出的定义本质上相同。

像 {leanRef}`Prod` 这样只有一个构造子的类型是纯粹合取性的：构造子只是把参数列表打包成一份数据，
本质上是一个元组，其中后续参数的类型可以依赖于初始参数的类型。我们也可以把这种类型看作一个“记录”或“结构”。
在 Lean 中，关键字 {kw}`structure` 可以用来同时定义这样的归纳类型及其投影。

```lean
namespace Hidden
------
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
-------
end Hidden
```

这个例子同时引入了归纳类型 {leanRef}`Prod`、它的构造子 {leanRef}`mk`、通常的消去器
（{lit}`rec` 和 {lit}`recOn`），以及上面定义的投影 {leanRef}`fst` 和 {leanRef}`snd`。

如果没有给构造子命名，Lean 默认使用 {lit}`mk`。例如，下面的定义把颜色存储为 RGB 值的三元组记录：

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

{leanRef}`yellow` 的定义用所示的三个值构造了这个记录，而投影 {leanRef}`Color.red` 返回红色分量。

{kw}`structure` 命令对于定义代数结构尤其有用，Lean 也提供了大量基础设施来支持对它们的处理。
例如，下面是半群的定义：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

我们将在 {ref "structures-and-records"}[结构与记录] 一章中看到更多例子。

:::leanFirst
我们已经讨论过依赖乘积类型 {leanRef}`Sigma`：

```lean
namespace Hidden
------
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
-------
end Hidden
```
:::

库中另外两个归纳类型的例子如下：

```lean
namespace Hidden
------
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
-------
end Hidden
```

:::setup
```
variable {α : Type u} {β : Type v} {γ : Type u'} (b : β) (f : α → Option β) (a : α)
```

在依赖类型论的语义中，没有内建的偏函数概念。函数类型 {lean}`α → β` 或依赖函数类型
{lean}`(a : α) → β` 的每个元素，都被假定在每个输入上有值。{lean}`Option` 类型提供了一种表示偏函数的方法。
{lean}`Option β` 的元素要么是 {lean}`none`，要么形如 {lean}`some b`，其中
{lean}`b : β`。因此，我们可以把类型 {lean}`α → Option β` 的元素 {lean}`f`
看作从 {lean}`α` 到 {lean}`β` 的偏函数：对每个 {lean}`a : α`，{lean}`f a`
要么返回 {lean (type := "Option β")}`none`，表示 {lean}`f a` “未定义”，要么返回 {lean}`some b`。

{lean}`Inhabited α` 的元素只是一个见证，表明 {lean}`α` 中存在元素。稍后我们会看到，
{lean}`Inhabited` 是 Lean 中_类型类_的一个例子：可以告知 Lean 某些合适的基本类型是有元素的，
Lean 随后可以据此自动推断其他构造出的类型也是有元素的。

作为练习，我们鼓励你为从 {lean}`α` 到 {lean}`β` 以及从 {lean}`β` 到 {lean}`γ` 的偏函数发展出复合的概念，
并证明它具有预期的行为。我们还鼓励你证明 {lean}`Bool` 和 {lean}`Nat` 是有元素的，
两个有元素类型的乘积也是有元素的，而以有元素类型为值域的函数类型也是有元素的。

:::

# 归纳定义的命题
%%%
tag := "inductively-defined-propositions"
%%%

归纳定义的类型可以位于任意类型宇宙中，包括最底层的 {lean}`Prop`。事实上，逻辑联结词正是这样定义的。

```lean
namespace Hidden
------
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
-------
end Hidden
```

:::setup
```
variable (p : Prop) (hp : p) (α : Type u) (β : Type v)
```

你应该思考这些定义如何产生你已经见过的引入规则和消去规则。有一些规则支配着归纳类型的消去器可以消去到_什么_，
也就是说，哪些类型可以作为递归子的目标。粗略地说，{lean}`Prop` 中归纳类型的特征在于：
它通常只能消去到 {lean}`Prop` 中的其他类型。这与如下理解是一致的：如果
{lean}`p : Prop`，那么元素 {lean}`hp : p` 不携带数据。不过，这条规则有一个小例外，
我们将在下文 {ref "inductive-families"}[归纳族] 中讨论。


甚至存在量词也是归纳定义的：

```lean
namespace Hidden
------
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
-------
end Hidden
```

请记住，记号 {lean}`∃ x : α, p` 是 {lean}`Exists (fun x : α => p)` 的语法糖。


{lean}`False`、{lean}`True`、{lean}`And` 和 {lean}`Or` 的定义与
{lean}`Empty`、{lean}`Unit`、{lean}`Prod` 和 {lean}`Sum` 的定义完全类似。
区别在于，前一组给出 {lean}`Prop` 的元素，而后一组给出 {lean}`Type u` 的元素
（对某个 {leanRef}`u`）。类似地，{leanRef}`∃ x : α, p` 是 {lean}`Σ x : α, β` 的
{lean}`Prop` 值变体。

:::

::::setup
```
variable (α : Type u) (β : Type v) (p : Prop)
```

这里适合提及另一种归纳类型，记作 {lean}`{x : α // p}`，它有些像
{lean}`∃ x : α, p` 与 {lean}`Σ x : α, β` 的混合体。

```lean
namespace Hidden
------
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
-------
end Hidden
```
::::
::::setup
```
variable {α : Type u} {p : α → Prop}
```

:::leanFirst
事实上，在 Lean 中，{leanRef}`Subtype` 是用结构命令定义的：

```lean
namespace Hidden
------
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
-------
end Hidden
```


记号 {lean}`{x : α // p x}` 是 {lean}`Subtype (fun x : α => p x)` 的语法糖。
它模仿集合论中的子集记号：其含义是，{leanRef}`{x : α // p x}` 表示
{leanRef}`α` 中具有性质 {leanRef}`p` 的元素所组成的集合。
:::

::::

# 定义自然数
%%%
tag := "defining-the-natural-numbers"
%%%

到目前为止，我们见到的归纳定义类型都是“扁平的”：构造子包装数据并将其插入某个类型中，
相应的递归子则解包这些数据并作用于它们。当构造子作用于正在定义的类型自身的元素时，
情形会有趣得多。一个典型例子是自然数类型 {lean}`Nat`：

```lean
namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
-------
end Hidden
```

:::setup
```
open Nat
variable {motive : Nat → Sort u} {f : (n : Nat) → motive n} {n : Nat}
```

这里有两个构造子。我们从 {lean}`zero : Nat` 开始；它不接受参数，所以一开始就拥有它。
相比之下，构造子 {lean}`succ` 只能应用于先前构造出的 {lean}`Nat`。把它应用于
{lean}`zero` 得到 {lean}`succ zero : Nat`。再次应用则得到
{lean}`succ (succ zero) : Nat`，依此类推。直观地说，{lean}`Nat` 是具有这些构造子的“最小”类型，
也就是说，它从 {lean}`zero` 出发、反复应用 {lean}`succ` 而被穷尽地（且自由地）生成。


和前面一样，{lean}`Nat` 的递归子旨在定义从 {lean}`Nat` 到任意论域的依赖函数
{lean}`f`，也就是对某个 {lean}`motive : Nat → Sort u` 而言，类型
{lean}`(n : Nat) → motive n` 的元素 {lean}`f`。它必须处理两种情况：输入为
{lean}`zero` 的情况，以及输入形如 {lean}`succ n`、其中 {lean}`n : Nat` 的情况。
在第一种情况下，我们像以前一样，只需指定一个具有适当类型的目标值。然而在第二种情况下，
递归子可以假设 {lean}`f` 在 {lean}`n` 处的值已经计算出来。因此，递归子的下一个参数会根据
{lean}`n` 和 {lean}`f n` 来指定 {lean}`f (succ n)` 的值。如果检查递归子的类型，
会看到如下内容：
:::

```signature
Nat.rec.{u} :
  {motive : Nat → Sort u} →
  (zero : motive Nat.zero) →
  (succ : (n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) → motive t
```

隐式参数 {leanRef}`motive` 是正在定义的函数的余定义域。在类型论中，通常说
{leanRef}`motive` 是消去/递归的_动机_，因为它描述了我们希望构造的对象种类。
接下来的两个参数指定如何计算零和后继两种情况，如上所述。它们也称为_小前提_。
最后，{leanRef}`t : Nat` 是该函数的输入。它也称为_大前提_。

{name}`Nat.recOn` 类似于 {name}`Nat.rec`，但大前提出现在小前提之前。

```signature
Nat.recOn.{u} :
  {motive : Nat → Sort u} →
  (t : Nat) →
  (zero : motive Nat.zero) →
  (succ : ((n : Nat) → motive n → motive (Nat.succ n))) →
  motive t
```

:::setup
```
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
variable {n m : Nat}
open Nat
```

例如，考虑自然数上的加法函数 {lean}`add m n`。固定 {lean}`m` 后，我们可以对
{lean}`n` 递归地定义加法。在基本情形中，把 {lean}`add m zero` 设为 {lean}`m`。
在后继步骤中，假设 {lean}`add m n` 的值已经确定，我们把 {lean}`add m (succ n)`
定义为 {lean}`succ (add m n)`。
:::

```lean
namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
-------
end Hidden
```


把这样的定义放入命名空间 {lean}`Nat` 中很有用。随后可以在该命名空间中定义熟悉的记号。
此时，加法的两个定义方程按定义成立：

```lean
namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr
------
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
-------
end Hidden
```

我们将在 {ref "type-classes"}[类型类] 一章中解释 {kw}`instance` 命令如何工作。
在下面的例子中，我们将使用 Lean 自带的自然数版本。

::::leanFirst

:::setup
```
variable {n : Nat} {motive : Nat → Sort u} {ih : motive n}
```

然而，证明像 {lean}`0 + n = n` 这样的事实需要归纳证明。正如上面所观察到的，
当余定义域 {lean}`motive n` 是 {lean}`Prop` 的元素时，归纳原则只是递归原则的一个特例。
它体现了熟悉的归纳证明模式：要证明 {lean}`∀ n, motive n`，先证明
{lean}`motive 0`；然后对任意 {lean}`n`，假设 {lean}`ih : motive n`，
并证明 {lean}`motive (n + 1)`。
:::

```lean
namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + (n + 1) = n + 1 from
    calc 0 + (n + 1)
      _ = (0 + n) + 1 := rfl
      _ = n + 1       := by rw [ih])
-------
end Hidden
```

::::

再次注意，当 {name}`Nat.recOn` 用在证明语境中时，它实际上就是伪装起来的归纳原则。
{tactic}`rw` 和 {tactic}`simp` 策略在这类证明中通常非常有效。在这个例子中，
二者都可以用来把证明化简为：


```lean
namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [ih])
-------
end Hidden
```

:::setup
```
variable (m n k : Nat)
```

再举一例，让我们证明加法的结合律：
{lean}`∀ m n k, m + n + k = m + (n + k)`。
（按照我们的定义，记号 {leanRef}`+` 左结合，所以 {leanRef}`m + n + k` 实际上是
{lean}`(m + n) + k`。）最困难的部分是弄清楚应该对哪个变量做归纳。由于加法是按第二个参数递归定义的，
{leanRef (in := "n k,")}`k` 是一个不错的猜测；一旦作出这个选择，证明几乎会自行写出：
:::

```lean
namespace Hidden
------
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + (k + 1) = m + (n + (k + 1)) from
      calc m + n + (k + 1)
        _ = (m + n + k) + 1   := rfl
        _ = (m + (n + k)) + 1 := by rw [ih]
        _ = m + ((n + k) + 1) := rfl
        _ = m + (n + (k + 1)) := rfl)
-------
end Hidden
```

同样地，可以把证明化简为：

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [add_succ (m + n) k, ih]; rfl)
```

假设我们尝试证明加法的交换律。若选择对第二个参数做归纳，可以从如下证明开始：

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)
```

此时我们看到，还需要另一个辅助事实，即 {leanRef}`succ (n + m)`{lit}`  =  `{leanRef}`succ n + m`。
可以对 {leanRef}`m` 做归纳来证明它：

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)
```

然后可以用 {leanRef}`succ_add` 替换前一个证明中的 {leanRef}`sorry`。证明仍然可以进一步压缩：

```lean
namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

namespace Nat
theorem add_zero (m : Nat) : m + zero = m := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun n ih => by simpa [add_zero, add_succ])

end Nat
------
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simpa [add_succ (succ n)])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp [add_zero, zero_add])
    (fun m ih => by simp_all [succ_add, add_succ])
-------
end Hidden
```

# 其他递归数据类型
%%%
tag := "other-recursive-data-types"
%%%

:::leanFirst
让我们再考察一些归纳定义类型的例子。对于任意类型 {leanRef}`α`，库中定义了由
{leanRef}`α` 的元素组成的列表类型 {leanRef}`List α`。

```lean
namespace Hidden
------
inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
-------
end Hidden
```

类型 {leanRef}`α` 的元素列表要么是空列表 {leanRef}`nil`，要么是一个元素
{leanRef}`h : α` 后接一个列表 {leanRef}`t : List α`。第一个元素
{leanRef}`h` 通常称为列表的“头”，其余部分 {leanRef}`t` 称为“尾”。
:::

作为练习，请证明以下命题：

```lean
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
------
theorem append_nil (as : List α) :
    append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  sorry
-------
end List
end Hidden
```

:::setup
```
universe u
def length : {α : Type u} → List α → Nat := List.length
def append : {α : Type u} → List α → List α → List α := List.append
variable (as bs : List α)
```

也请尝试定义函数 {lean}`length : {α : Type u} → List α → Nat` 来返回列表长度，
并证明它具有预期的行为（例如，{lean}`length (append as bs) = length as + length bs`）。
:::

作为另一个例子，我们可以定义二叉树类型：

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

事实上，我们甚至可以定义可数分支树的类型：

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

# 归纳类型的策略
%%%
tag := "tactics-for-inductive-types"
%%%

鉴于归纳类型在 Lean 中的基础重要性，存在若干专门为有效处理它们而设计的策略并不令人惊讶。
这里我们介绍其中一些。

:::setup
```
variable {x : InductiveType}
```

{tactic}`cases` 策略作用于归纳定义类型的元素，并且顾名思义：它按照所有可能的构造子分解该元素。
在最基本的形式中，它应用于局部上下文中的元素 {lean}`x`。随后，它把目标化为若干情形，
其中 {lean}`x` 分别被每一种构造替换。
:::

```lean
example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
--^ PROOF_STATE: A
  . apply hs
--^ PROOF_STATE: B
```

在第一个分支中，证明状态为：
```proofState A
case zero
p : Nat → Prop
hz : p 0
hs : ∀ (n : Nat), p n.succ
⊢ p 0
```
在第二个分支中，则为：
```proofState B
case succ
p : Nat → Prop
hz : p 0
hs : ∀ (n : Nat), p n.succ
n✝ : Nat
⊢ p (n✝ + 1)
```

:::leanFirst
它还有一些额外功能。首先，{leanRef}`cases` 允许你用 {leanRef}`with` 子句为每个分支选择名称。
例如，在下一个例子中，我们为 {leanRef}`succ` 的参数选择名称 {leanRef}`m`，
使得第二种情形指的是 {leanRef}`succ m`。更重要的是，cases 策略会检测局部上下文中依赖目标变量的项。
它会还原这些元素，进行分情况讨论，然后再重新引入它们。在下面的例子中，请注意假设
{leanRef}`h : n ≠ 0` 在第一个分支中变为 {leanRef}`h : 0 ≠ 0`，
在第二个分支中变为 {leanRef}`h : m + 1 ≠ 0`。

```lean (showProofStates := "C D")
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
  --     ^ PROOF_STATE: C
    apply absurd rfl h
  | succ m =>
  --       ^ PROOF_STATE: D
    rfl
```
:::

注意，{leanRef}`cases` 既可以用来产生数据，也可以用来证明命题。

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

同样，cases 会还原、拆分，然后重新引入上下文中的依赖项。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

下面是一个含有多个带参数构造子的例子。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

各个构造子对应的分支不需要按照构造子声明的顺序来解决。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

:::leanFirst
{leanRef}`with` 的语法便于书写结构化证明。Lean 还提供了互补的
{leanRef}`case` 策略，使你能够聚焦于目标并指定变量名。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```
:::

{leanRef}`case` 策略很聪明，因为它会把构造子与相应目标匹配起来。例如，我们可以按相反顺序填充上面的目标：

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

也可以对任意表达式使用 {leanRef}`cases`。假设该表达式出现在目标中，cases 策略会对该表达式进行泛化，
引入得到的全称量化变量，并对它做分情况讨论。

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)
```

可以把这理解为“按 {leanRef}`m + 3 * k` 是零还是某个数的后继来分情况讨论”。
其结果在功能上等价于以下证明：

```lean (showProofStates := "Z S")
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  -- ^ PROOF_STATE: Z
  exact hz
  -- ^ PROOF_STATE: S
  apply hs
```

注意，表达式 {leanRef}`m + 3 * k` 会被 {leanRef}`generalize` 抹去；重要的只是它是形如
{leanRef}`0`，还是形如 {leanRef}`n✝ + 1`。这种形式的 {leanRef}`cases` _不会_还原那些同样提及该等式中表达式
（本例中为 {leanRef}`m + 3 * k`）的假设。如果这样的项出现在某个假设中，而你也想对它进行泛化，
就需要显式地 {tactic}`revert` 它。

如果要分情况讨论的表达式没有出现在目标中，{tactic}`cases` 策略会使用 {tactic}`have`
把该表达式的类型放入上下文。下面是一个例子：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  --           ^ PROOF_STATE: one
  case inr hge => exact h₂ hge
  --           ^ PROOF_STATE: two
```

定理 {leanRef}`Nat.lt_or_ge m n` 说明 {leanRef}`m < n`{lit}`  ∨  `{leanRef}`m ≥ n`，
因此很自然地把上面的证明看作在这两种情形上拆分。在第一个分支中，我们有假设
{leanRef}`hlt : m < n`；在第二个分支中，我们有假设 {leanRef}`hge : m ≥ n`。
上面的证明在功能上等价于如下证明：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

前两行之后，我们得到假设 {leanRef}`h : m < n ∨ m ≥ n`，然后只需对它做分情况讨论。

:::leanFirst
下面是另一个例子，其中我们使用自然数相等性的可判定性，把证明拆分为
{leanRef}`m = n` 和 {leanRef}`m ≠ n` 两种情况。

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```
:::

请记住，如果你 {kw}`open `{lit}`Classical`，就可以对任意命题使用排中律。
但是借助类型类推断（见 {ref "type-classes"}[类型类]），Lean 实际上可以找到相关的判定过程，
这意味着你可以在可计算函数中使用这种分情况拆分。

:::leanFirst
正如 {leanRef}`cases` 策略可以用于进行分情况证明，{leanRef}`induction` 策略也可以用于进行归纳证明。
其语法类似于 {leanRef}`cases`，区别在于参数只能是局部上下文中的项。下面是一个例子：

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

:::leanFirst
与 {leanRef}`cases` 一样，我们可以使用 {leanRef}`case` 策略来替代 {leanRef}`with`。

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

下面是一些额外的例子：
:::TODO
待修复
:::
```lean
namespace Hidden
inductive Nat where
  | zero
  | succ : Nat → Nat

def Nat.toNat : Nat → _root_.Nat
  | .zero => .zero
  | .succ n => .succ n.toNat

def Nat.ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (.ofNat n)

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

instance : OfNat Nat n where
  ofNat := .ofNat n

@[simp]
theorem zero_zero : (.zero : Nat) = 0 := rfl
theorem add_zero (n : Nat) : n + 0 = n := rfl
theorem add_succ (n k : Nat) : n + k.succ = (n + k).succ := rfl
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
-------
end Hidden
```

{leanRef}`induction` 策略还支持具有多个目标（也称为大前提）的用户自定义归纳原则。
此例使用 {name}`Nat.mod.inductionOn`，它具有如下签名：
```signature
Nat.mod.inductionOn
  {motive : Nat → Nat → Sort u}
  (x y  : Nat)
  (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
  (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y) :
  motive x y
```


```lean
example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
```

在策略中也可以使用 {kw}`match` 记号：

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

:::leanFirst
为方便起见，模式匹配已经集成到 {leanRef}`intro` 和 {leanRef}`funext` 等策略中。

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```
:::

:::leanFirst
本节最后介绍一个旨在方便处理归纳类型的策略，即 {leanRef}`injection` 策略。
按照设计，归纳类型的元素是自由生成的；也就是说，构造子是单射的，并且其值域两两不交。
{leanRef}`injection` 策略正是为了利用这一事实：

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```
:::

第一次使用该策略会把 {lit}`h' : m.succ = n.succ` 加入上下文，
第二次则加入 {lit}`h'' : m = n`。

{leanRef}`injection` 策略还会检测由不同构造子被设为相等所产生的矛盾，并利用这些矛盾关闭目标。

```lean
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

如第二个例子所示，{leanRef}`contradiction` 策略也会检测这种形式的矛盾。

# 归纳族
%%%
tag := "inductive-families"
%%%

我们已经快要完整描述 Lean 接受的各种归纳定义了。到目前为止，你已经看到 Lean 允许引入带有任意数量递归构造子的归纳类型。
事实上，单个归纳定义还可以按下面要介绍的方式，引入一个带索引的归纳类型_族_。

归纳族是一个带索引的类型族，由如下形式的同步归纳定义给出：

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```
::::setup
```
universe u
```

:::leanFirst
普通归纳定义构造某个 {leanRef}`Sort u` 的元素；与之不同，更一般的版本构造一个函数
{lit}`... → `{lean}`Sort u`，其中“{lit}`...`”表示一列参数类型，也称为_索引_。
随后，每个构造子都构造该族中某个成员的元素。一个例子是 {leanRef}`Vect α n` 的定义，
它是长度为 {leanRef}`n`、元素来自 {leanRef}`α` 的向量类型：

```lean
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::
::::

注意，构造子 {leanRef}`cons` 接受 {leanRef}`Vect α n` 的一个元素，并返回
{leanRef}`Vect α (n + 1)` 的一个元素，从而用该族某个成员的元素来构造另一个成员的元素。

一个更特殊的例子是 Lean 中相等类型的定义：

```lean
namespace Hidden
------
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
-------
end Hidden
```

:::setup
```
variable (α : Sort u) (a : α) (x : α)
```

对每个固定的 {leanRef}`α : Sort u` 和 {leanRef}`a : α`，这个定义构造了一个由
{lean}`x : α` 索引的类型族 {lean}`Eq a x`。然而值得注意的是，它只有一个构造子
{leanRef}`refl`，后者是 {leanRef}`Eq a a` 的元素。直观地说，构造
{lean}`Eq a x` 的证明的唯一方法，是在 {lean}`x` 为 {lean}`a` 的情况下使用自反性。
注意，在类型族 {lean}`Eq a x` 中，{lean}`Eq a a` 是唯一有元素的类型。Lean 生成的消去原则如下：
:::

```lean
set_option pp.proofs true
--------
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} →
                  {motive : (x : α) → a = x → Sort v} →
                  motive a rfl →
                  {b : α} → (h : a = b) → motive b h)
```

一个值得注意的事实是，关于相等性的所有基本公理都可由构造子 {leanRef}`refl` 和消去器
{leanRef}`Eq.rec` 推出。不过，相等性的定义并不典型；参见
{ref "axiomatic-details"}[公理细节] 中的讨论。

递归子 {leanRef}`Eq.rec` 还用于定义替换：

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
-------
end Hidden
```

也可以使用 {kw}`match` 定义 {leanRef}`subst`。

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
-------
end Hidden
```

实际上，Lean 会用基于所生成辅助定义的方式编译 {kw}`match` 表达式，例如
{name}`Eq.casesOn` 和 {name}`Eq.ndrec`；而这些辅助定义本身又是用 {leanRef}`Eq.rec` 定义的。

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : a = b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst

#print subst.match_1_1

#print Eq.casesOn

#print Eq.ndrec
-------
end Hidden
```

对 {leanRef}`h₁ : a = b` 使用递归子或 {kw}`match` 时，我们可以假定 {leanRef}`a`
和 {leanRef}`b` 相同；在这种情况下，{leanRef}`p b` 与 {leanRef}`p a` 也相同。

:::leanFirst
证明 {leanRef}`Eq` 具有对称性和传递性并不困难。在下面的例子中，我们证明
{leanRef}`symm`，并把定理 {leanRef}`trans` 和 {leanRef}`congr`（同余）留作练习。

```lean
namespace Hidden
------
variable {α β : Type u} {a b c : α}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
-------
end Hidden
```
:::

在类型论文献中，还有对归纳定义的进一步推广，例如_归纳-递归_和_归纳-归纳_原则。
Lean 不支持这些原则。

# 公理细节
%%%
tag := "axiomatic-details"
%%%

我们已经通过例子描述了归纳类型及其语法。本节为对公理基础感兴趣的读者提供更多信息。

我们已经看到，归纳类型的构造子接受_参数_——直观地说，就是在整个归纳构造过程中保持固定的参数——
以及_索引_，即为同时正在构造的类型族作参数化的参数。每个构造子都应具有一个类型，
其中参数类型由先前定义的类型、参数类型与索引类型，以及当前正在定义的归纳族构成。
要求是：如果后者出现，它只能_严格正向_地出现。简单来说，这意味着凡是包含它的构造子参数，
都必须是一个依赖箭头类型，并且正在定义的归纳类型只出现在该依赖箭头类型的结果类型位置；
其中索引由常量和先前的参数给出。

由于归纳类型位于某个 {leanRef}`u` 下的 {leanRef}`Sort u` 中，自然要问：
{leanRef}`u` 可以实例化为_哪些_宇宙层级。归纳类型族 {lit}`C` 的定义中，每个构造子
{lit}`c` 都具有如下形式：

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

其中 {lit}`a` 是一列数据类型参数，{lit}`b` 是构造子的参数序列，而
{lit}`p[a, b]` 是索引，它们决定该构造所栖居的是归纳族中的哪一个元素。
（注意，这种描述有些误导，因为只要依赖关系有意义，构造子的参数可以按任意顺序出现。）
对 {lit}`C` 的宇宙层级的约束分为两种情况，取决于该归纳类型是否被指定落在
{lean}`Prop`（即 {lean}`Sort 0`）中。

先考虑归纳类型_没有_被指定落在 {lean}`Prop` 中的情况。此时宇宙层级
{leanRef}`u` 受到如下约束：

> 对于如上的每个构造子 {lit}`c`，以及序列 {lit}`β[a]` 中的每个 {lit}`βk[a]`，若 {lit}`βk[a] : Sort v`，则有 {leanRef}`u` ≥ {leanRef}`v`。

换言之，要求宇宙层级 {leanRef}`u` 至少与表示构造子参数的每个类型所在的宇宙层级一样大。

当归纳类型被指定落在 {lean}`Prop` 中时，构造子参数的宇宙层级没有约束。
但这些宇宙层级确实会影响消去规则。一般而言，对于 {lean}`Prop` 中的归纳类型，
消去规则的动机要求位于 {lean}`Prop` 中。

最后这条规则有一个例外：当只有一个构造子，并且每个构造子参数要么位于
{lean}`Prop` 中、要么是索引时，我们允许从一个归纳定义的 {leanRef}`Prop`
消去到任意 {lean}`Sort`。直观理由是，在这种情况下，消去并没有使用任何超出
“参数类型有元素”这一事实之外的信息。这个特例称为_单例消去_。

我们已经在归纳定义的相等类型的消去器 {name}`Eq.rec` 的应用中看到单例消去发挥作用。
我们可以用元素 {leanRef}`h : Eq a b` 将元素 {leanRef}`h₂ : p a` 强制转换为
{leanRef}`p b`，即使 {leanRef}`p a` 和 {leanRef}`p b` 是任意类型也可以；
因为这种转换不会产生新数据，它只是重新解释我们已有的数据。单例消去也用于异质相等和良基递归；
这些内容将在 {ref "well-founded-recursion-and-induction"}[归纳与递归] 一章中讨论。

# 相互和嵌套归纳类型
%%%
tag := "mutual-and-nested-inductive-types"
%%%

现在我们考虑归纳类型的两种常用推广。Lean 通过把它们“编译”为上面描述的更原始的归纳类型来支持它们。
换言之，Lean 解析更一般的定义，基于它们定义辅助归纳类型，然后再用这些辅助类型定义我们真正想要的类型。
要有效使用这些类型，需要下一章将介绍的 Lean 方程编译器。尽管如此，在这里描述这些声明仍然有意义，
因为它们是普通归纳定义的直接变体。

首先，Lean 支持_相互定义的_归纳类型。其思想是，可以同时定义两个（或更多）归纳类型，
其中每一个都引用其他类型。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

在这个例子中，两个类型被同时定义：自然数 {leanRef}`n` 若为 {leanRef}`0`
或比某个 {leanRef}`Odd` 数大一，则为 {leanRef}`Even`；若比某个 {leanRef}`Even`
数大一，则为 {leanRef}`Odd`。在下面的练习中，你需要把细节写出来。

:::leanFirst
相互归纳定义也可用于定义一种有限树的表示，其节点由 {leanRef (in:="Tree (α")}`α` 的元素标记：

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```
:::

有了这个定义，可以通过给出一个 {leanRef}`α` 的元素以及一个可能为空的子树列表，
来构造 {leanRef}`Tree α` 的元素。子树列表由类型 {leanRef}`TreeList α` 表示；
它被定义为要么是空列表 {leanRef}`nil`，要么是由一棵树和一个 {leanRef}`TreeList α`
元素构成的 {leanRef}`cons`。

:::leanFirst
然而，使用这个定义并不方便。如果子树列表由类型 {leanRef}`List (Tree α)` 给出会好得多，
尤其是因为 Lean 的库包含许多处理列表的函数和定理。可以证明类型 {leanRef}`TreeList α`
与 {leanRef}`List (Tree α)` _同构_，但沿着这个同构来回转换结果很繁琐。

事实上，Lean 允许我们定义真正想要的归纳类型：

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```
:::

这称为_嵌套_归纳类型。它超出了上一节给出的归纳类型严格规范，因为 {leanRef}`Tree`
并不是严格正向地出现在 {leanRef}`mk` 的参数中，而是嵌套在 {leanRef}`List` 类型构造子内部。
于是 Lean 会在其内核中自动构造 {leanRef}`TreeList α` 与 {leanRef}`List (Tree α)` 之间的同构，
并依据该同构定义 {leanRef}`Tree` 的构造子。

# 练习
%%%
tag := "inductive-types-exercises"
%%%

```setup
open Nat
variable {n m : Nat}
def length : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1
def reverse : List α → List α := go []
where
  go (acc : List α) : List α → List α
    | [] => acc
    | x :: xs => go (x :: acc) xs
variable {xs ys : List α}

inductive Term where
  | const (n : Nat)
  | var (n : Nat)
  | plus (s t : Term)
  | times (s t : Term)
open Term
variable {s t : Term}

```

1. 尝试定义自然数上的其他运算，例如乘法、前驱函数（满足 {lean}`pred 0 = 0`）、
   截断减法（当 {lean}`m` 大于或等于 {lean}`n` 时满足 {lean}`n - m = 0`）以及乘方。
   然后基于我们已经证明的定理，尝试证明它们的一些基本性质。

   由于其中许多已经在 Lean 的核心库中定义，为避免名称冲突，你应该在名为
   {lit}`Hidden` 或类似名称的命名空间中工作。

2. 定义一些列表上的运算，例如 {lean}`length` 函数或 {lean}`reverse` 函数。
   证明一些性质，例如：

   a. {lean}`length (xs ++ ys) = length xs + length ys`

   b. {lean}`length (reverse xs) = length xs`

   c. {lean}`reverse (reverse xs) = xs`

3. 定义一个归纳数据类型，其项由以下构造子构成：

   - {lean}`const n`，表示自然数 {lean}`n` 的常量
   - {lean}`var n`，编号为 {lean}`n` 的变量
   - {lean}`plus s t`，表示 {leanRef}`s` 与 {leanRef}`t` 的和
   - {lean}`times s t`，表示 {leanRef}`s` 与 {leanRef}`t` 的积

   递归地定义一个函数，使其能够相对于变量赋值来求值任意这样的项。

4. 类似地，定义命题公式的类型，以及该类型上的函数：求值函数、度量公式复杂度的函数，
   以及把另一个公式替换给定变量的函数。
