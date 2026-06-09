import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "结构与记录" =>
%%%
tag := "structures-and-records"
file := "Structures-and-Records"
%%%

我们已经看到，Lean 的基础系统包含归纳类型。此外，我们还注意到一个引人注目的事实：仅凭类型宇宙、依赖箭头类型和归纳类型，就可以构造起相当宏大的数学体系；其余一切都由此而来。Lean 标准库包含许多归纳类型的实例（例如 {lean}`Nat`、{lean}`Prod`、{lean}`List`），甚至逻辑联结词也是用归纳类型定义的。

回忆一下，只包含一个构造子的非递归归纳类型称为 _结构_ 或 _记录_。积类型是一种结构，依赖积（Sigma）类型也是如此。一般而言，每当我们定义一个结构 {lit}`S` 时，通常也会定义 _投影_ 函数，使我们能够“析构” {lit}`S` 的每个实例，并取回存储在其字段中的值。函数 {lean}`Prod.fst` 和 {lean}`Prod.snd` 分别返回一个有序对的第一、第二个元素，它们就是这类投影的例子。

在编写程序或形式化数学时，定义包含许多字段的结构并不少见。Lean 中可用的 {kw}`structure` 命令提供了支持这一过程的基础设施。当我们用该命令定义结构时，Lean 会自动生成所有投影函数。{kw}`structure` 命令还允许我们在既有结构的基础上定义新结构。此外，Lean 还提供了便捷记法，用于定义给定结构的实例。

# 声明结构
%%%
tag := "declaring-structures"
%%%

结构命令本质上是用于定义归纳数据类型的“前端”。每个 {kw}`structure` 声明都会引入一个同名命名空间。其一般形式如下：

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

其中大多数部分都是可选的。下面是一个例子：

```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
```

:::setup
```
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
variable (p : Point α) (a b : α)
```
{leanRef}`Point` 类型的值用 {lean}`Point.mk a b` 创建，而点 {lean}`p` 的字段可用 {lean}`Point.x p` 和 {lean}`Point.y p` 访问（不过 {lean}`p.x` 和 {lean}`p.y` 也可以，见下文）。结构命令还会生成有用的递归子和定理。下面是上述声明所生成的一些构造。
:::

```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
------
-- 一个类型
#check Point

-- 消去子
#check @Point.rec

-- 构造子
#check @Point.mk -- @Point.mk : {α : Type u_1} → α → α → Point α

-- 一个投影
#check @Point.x -- @Point.x : {α : Type u_1} → Point α → α

-- 一个投影
#check @Point.y -- @Point.y : {α : Type u_1} → Point α → α
```

如果没有给出构造子的名称，则构造子默认命名为 {lit}`mk`。

:::leanFirst
下面是一些使用生成构造的简单定理和表达式。和往常一样，可以使用命令 {leanRef}`open Point` 来省略前缀 {leanRef}`Point`。

```lean
structure Point (α : Type u) where
  x : α
  y : α
------
#eval Point.x (Point.mk 10 20) -- 10

#eval Point.y (Point.mk 10 20) -- 20

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```
:::


:::setup
```
structure Point (α : Type u) where
  x : α
  y : α
variable (p : Point Nat)
```


给定 {lean}`p : Point Nat`，点记法 {lean}`p.x` 是 {lean}`Point.x p` 的简写。这提供了一种访问结构字段的便捷方式。
:::

```lean
structure Point (α : Type u) where
 x : α
 y : α
------
def p := Point.mk 10 20

#check p.x  -- p.x : Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

:::leanFirst
点记法不仅便于访问记录的投影，也便于应用在同名命名空间中定义的函数。回忆 {ref "conjunction"}[合取一节] 中的内容：如果 {leanRef}`p` 的类型是 {leanRef}`Point`，那么在 {lit}`foo` 的第一个非隐式参数类型为 {lit}`Point` 的前提下，表达式 {lit}`p.foo` 会被解释为 {lit}`Point.foo p`。因此，在下面的例子中，表达式 {lit}`p.add q` 是 {lit}`Point.add p q` 的简写。

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- { x := 4, y := 6 }
```
:::

:::setup
```
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

variable {α : Type u}
```

在下一章中，你将学习如何定义像 {leanRef}`add` 这样的函数，使它不仅适用于 {lean}`Point Nat`，而是在假设 {lean}`α` 带有相应加法运算时，能一般地适用于 {lean}`Point α` 的元素。
:::

:::leanFirst
更一般地说，给定表达式 {lit}`p.foo x y z`，其中 {lit}`p : Point`，Lean 会把 {lit}`p` 插入到 {lit}`Point.foo` 中类型为 {lit}`Point` 的第一个参数位置。例如，对于下面定义的标量乘法，{leanRef}`p.smul 3` 会被解释为 {leanRef}`Point.smul 3 p`。

```lean
structure Point (α : Type u) where
 x : α
 y : α
 deriving Repr
------
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- { x := 3, y := 6 }

example {p : Point Nat} : p.smul 3 = Point.smul 3 p := rfl
```
:::

类似的技巧常用于 {name}`List.map` 函数；该函数把列表作为其第二个非隐式参数：

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]

example {xs : List α} {f : α → β} :
    xs.map f = List.map f xs :=
  rfl
```

这里，{leanRef}`xs.map f` 会被解释为 {leanRef}`List.map f xs`。

# 对象
%%%
tag := "objects"
%%%

我们一直在使用构造子来创建结构类型的元素。对于包含许多字段的结构而言，这通常不方便，因为我们必须记住字段定义的顺序。因此，Lean 提供了以下替代记法，用于定义结构类型的元素。

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

只要结构的名称可以由期望类型推断出来，后缀 {lit}`: structure-type` 就可以省略。例如，我们使用这种记法来定义“点”。字段给出的顺序并不重要，因此下面所有表达式都定义了同一个点。

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- { x := 10, y := 20 } : Point Nat

#check { y := 20, x := 10 : Point _ } -- { x := 10, y := 20 } : Point Nat

#check ({ x := 10, y := 20 } : Point Nat) -- { x := 10, y := 20 } : Point Nat

example : Point Nat :=
  { y := 20, x := 10 }
```

字段可以用花括号标记为隐式。隐式字段会成为构造子的隐式参数。

如果某个字段的值没有指定，Lean 会尝试推断它。如果未指定的字段无法被推断，Lean 会报告错误，指出相应的占位符无法被合成。

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

_记录更新_ 是另一种常见操作，它相当于通过修改旧记录中一个或多个字段的值来创建新的记录对象。Lean 允许你指定：记录说明中未赋值的字段应从先前定义的结构对象 {lit}`s` 中取得；做法是在字段赋值之前添加注记 {lit}`s `{kw}`with`。如果提供了多个记录对象，那么 Lean 会按顺序访问它们，直到找到包含该未指定字段的对象。如果在访问所有对象后仍有字段名未被指定，Lean 就会报错。

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }

#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

# 继承
%%%
tag := "inheritance"
%%%

我们可以通过添加新字段来 _扩展_ 既有结构。这个特性使我们能够模拟一种 _继承_ 形式。

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

在下一个例子中，我们使用多重继承定义一个结构，然后利用父结构的对象来定义一个对象。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```
