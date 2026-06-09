import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "类型类" =>
%%%
tag := "type-classes"
file := "Type-Classes"
%%%

类型类最初作为一种原则化的方法被引入，用以在函数式编程语言中实现特设多态。首先注意，如果一个特设多态函数（如加法）只是把某个类型专属的加法实现作为参数，并随后把该实现应用于其余参数，那么实现它将很容易。例如，假设我们在 Lean 中声明一个结构来保存加法的实现。

```lean
namespace Ex
------
structure Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → Add α → α → α → α
------
end Ex
```


::::setup
```
namespace Ex
structure Add (α : Type) where
  add : α → α → α
def double (s : Add α) (x : α) : α :=
  s.add x x
variable {n : Nat}
```
:::leanFirst
在上面的 Lean 代码中，字段 {leanRef}`add` 的类型为 {lean}`Add.add : {α : Type} → Add α → α → α → α`，其中类型 {leanRef}`α` 外的花括号表示它是一个隐式参数。我们可以如下实现 {leanRef}`double`：


```lean
namespace Ex
structure Add (α : Type) where
  add : α → α → α
------
def double (s : Add α) (x : α) : α :=
  s.add x x

#eval double { add := Nat.add } 10 -- 20

#eval double { add := Nat.mul } 10 -- 100

#eval double { add := Int.add } 10 -- 20
------
end Ex
```
:::

注意，可以用 {lean}`double { add := Nat.add } n` 将自然数 {lean}`n` 加倍。当然，让用户以这种方式手动传递实现会非常繁琐。事实上，这会抵消特设多态的大部分潜在益处。
::::

:::leanFirst
类型类背后的主要思想，是使诸如 {leanRef}`Add α` 这样的参数成为隐式参数，并使用用户定义实例的数据库，通过称为类型类解析的过程自动合成所需实例。在 Lean 中，把上例中的 {kw}`structure` 改为 {kw}`class` 后，{leanRef}`Add.add` 的类型变为：

```lean
namespace Ex
------
class Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → [self : Add α] → α → α → α
------
end Ex
```
:::

其中方括号表示类型为 {leanRef}`Add α` 的参数是 _实例隐式_ 参数，也就是说它应当通过类型类解析来合成。这个版本的 {leanRef}`add` 是 Lean 中对应于 Haskell 项 {lit}`add :: Add a => a -> a -> a` 的类似物。类似地，我们可以如下注册实例：

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
------
end Ex
```

::::leanFirst
:::setup
```
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

variable (n m : Nat)
```
于是对于 {lean}`n : Nat` 和 {lean}`m : Nat`，项 {lean}`Add.add n m` 会触发以 {lean}`Add Nat` 为目标的类型类解析，而类型类解析会合成上面关于 {lean}`Nat` 的实例。现在我们可以使用实例隐式参数来重新实现 {leanRef}`double`：
:::

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
instance : Add Nat where
 add := Nat.add
instance : Add Int where
 add := Int.add
instance : Add Float where
 add := Float.add
------
def double [Add α] (x : α) : α :=
  Add.add x x

#check @double -- @double : {α : Type} → [Add α] → α → α

#eval double 10 -- 20

#eval double (10 : Int) -- 20

#eval double (7 : Float) -- 14.000000

#eval double (239.0 + 2) -- 482.000000

------
end Ex
```
::::

:::leanFirst
一般而言，实例可以以复杂方式依赖于其他实例。例如，可以声明一个实例，说明如果 {leanRef}`α` 具有加法，那么 {leanRef}`Array α` 也具有加法：

```lean
instance [Add α] : Add (Array α) where
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4] -- #[4, 6]

#eval #[1, 2] + #[3, 4] -- #[4, 6]
```
:::

注意，{leanRef}`(· + ·)` 是 Lean 中 {lean}`fun x y => x + y` 的记法。


:::setup
```
def head [Inhabited α] (xs : List α) : α := default
variable {α : Type u} {x : α} {xs : List α} [Inhabited α]
```

上面的例子展示了类型类如何用于重载记法。现在，我们探讨另一种应用。我们经常需要某个给定类型的任意元素。回忆一下，在 Lean 中类型可能没有任何元素。我们常常希望某个定义在“边界情形”下返回一个任意元素。例如，当 {lean}`xs` 的类型为 {lean}`List α` 时，我们可能希望表达式 {lean}`head xs` 的类型为 {lean}`α`。类似地，许多定理在附加假设某个类型非空时才成立。例如，如果 {lean}`α` 是一个类型，那么 {lean}`∃ x : α, x = x` 只有在 {lean}`α` 非空时才为真。标准库定义了类型类 {lean}`Inhabited`，使类型类推断能够推断有默认元素类型的“默认”元素。让我们从上述方案的第一步开始，即声明一个适当的类：



```lean
namespace Ex
------
class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default -- @Inhabited.default : {α : Type u_1} → [self : Inhabited α] → α
------
end Ex
```

注意，{leanRef}`Inhabited.default` 没有任何显式参数。

类 {lean}`Inhabited α` 的一个元素只是形如 {lean}`Inhabited.mk x` 的表达式，其中 {lean}`x : α`。投影 {lean}`Inhabited.default` 允许我们从 {lean}`Inhabited α` 的元素中“提取”这样一个 {lean}`α` 的元素。现在我们用一些实例填充该类：
:::

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
------
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat) -- 0

#eval (Inhabited.default : Bool) -- true
--------
end Ex
```

可以使用命令 {kw}`export` 为 {lean}`Inhabited.default` 创建别名 {lean}`default`。

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
instance : Inhabited Unit where
 default := ()
instance : Inhabited Prop where
 default := True
------
export Inhabited (default)

#eval (default : Nat) -- 0

#eval (default : Bool) -- true
------
end Ex
```

# 实例的链接
%%%
tag := "chaining-instances"
%%%

如果类型类推断仅止于此，那么它并不算十分令人印象深刻；它不过是把一列实例存储起来，供精化器在查找表中查找的机制。类型类推断的强大之处在于可以 _链接_ 实例。也就是说，一个实例声明本身可以依赖某个类型类的隐式实例。这会使类推断通过实例进行递归链接，并在必要时回溯，形成一种类似 Prolog 的搜索。

:::leanFirst
例如，下面的定义表明，如果两个类型 {leanRef}`α` 和 {leanRef}`β` 都有默认元素，那么它们的乘积类型也有默认元素：

```lean
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)
```
:::

把它加入前面的实例声明后，类型类实例推断便可以推断出例如 {lean}`Nat × Bool` 的默认元素：

```lean
namespace Ex
class Inhabited (α : Type u) where
 default : α
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
opaque default [Inhabited α] : α :=
 Inhabited.default
------
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool) -- (0, true)
------
end Ex
```

类似地，我们可以用合适的常值函数使函数类型具有默认元素：

```lean
instance [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default
```

作为练习，请尝试为其他类型定义默认实例，例如 {lean}`List` 和 {lean}`Sum` 类型。

:::setup
```
universe u
set_option checkBinderAnnotations false
```
Lean 标准库包含定义 {name}`inferInstance`。它的类型是 {lean}`{α : Sort u} → [i : α] → α`，当期望类型是一个实例时，它可用于触发类型类解析过程。
:::

```lean
#check (inferInstance : Inhabited Nat) -- inferInstance : Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```

:::leanFirst
可以使用命令 {leanRef}`#print` 来查看 {leanRef}`inferInstance` 有多么简单。

```lean
#print inferInstance
```
:::

# ToString（转为字符串）
%%%
tag := "ToString"
%%%
```setup
universe u
```

:::leanFirst
多态方法 {leanRef}`toString` 的类型是 {lean}`{α : Type u} → [ToString α] → α → String`。你可以为自己的类型实现其实例，并通过链接把复杂值转换为字符串。Lean 为大多数内建类型提供了 {lean}`ToString` 实例。

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person } -- "Leo@542"

#eval toString ({ name := "Daniel", age := 18 : Person }, "hello") -- "(Daniel@18, hello)"
```
:::

# 数值字面量
%%%
tag := "numerals"
%%%

数值字面量在 Lean 中是多态的。你可以使用一个数值字面量（例如 {lit}`2`）来表示任何实现了类型类 {name}`OfNat` 的类型的元素。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- 2 : Rational

#check (2 : Nat)      -- 2 : Nat
```

:::setup
```
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"
```
Lean 分别将项 {lean}`(2 : Nat)` 和 {lean}`(2 : Rational)` 精化为 {lean (type := "Nat")}`@OfNat.ofNat Nat 2 (@instOfNatNat 2)` 与 {lean}`@OfNat.ofNat Rational 2 (@instOfNatRational 2)`。我们称精化后项中出现的数值字面量 {lit}`2` 为 _原始_ 自然数。可以使用宏 {lit}`nat_lit 2` 输入原始自然数 {lean}`2`。
:::

```lean
#check nat_lit 2  -- 2 : Nat
```

原始自然数 _不是_ 多态的。

{lean}`OfNat` 实例以数值字面量为参数。因此，可以为特定数值字面量定义实例。第二个参数通常像上例那样是变量，或者是一个 _原始_ 自然数。

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

# 输出参数
%%%
tag := "output-parameters"
%%%

:::setup
```
universe u
variable (T : Type u)
```

默认情况下，Lean 只有在项 {lean}`T` 已知且不包含缺失部分时，才会尝试合成实例 {lean}`Inhabited T`。下面的命令会产生错误 {lit}`typeclass instance problem is stuck, it is often due to metavariables`，因为该类型有一个缺失部分（即 {lit}`_`）。
:::

```lean
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2)
-/
#guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))
```

可以把类型类 {lean}`Inhabited` 的参数看作类型类合成器的一个 _输入_ 值。当类型类有多个参数时，可以把其中一些标记为 {deftech}_输出参数_。即便这些参数含有缺失部分，Lean 也会启动类型类合成器。在下面的例子中，我们使用输出参数来定义 _异质_ 多态乘法。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12

#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
------
end Ex
```

参数 {leanRef}`α` 和 {leanRef}`β` 被视为输入参数，而 {leanRef}`γ` 被视为输出参数。给定应用 {leanRef}`hMul a b`，在 {leanRef}`a` 和 {leanRef}`b` 的类型已知后，类型类合成器会被调用，并从输出参数 {leanRef}`γ` 得到结果类型。在上面的例子中，我们定义了两个实例。第一个是自然数的同质乘法；第二个是数组的标量乘法。注意，你可以链接实例并推广第二个实例。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12

#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]

#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]

#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
------
end Ex
```

只要有实例 {leanRef}`HMul α β γ`，就可以把我们新的标量数组乘法实例用于类型为 {leanRef}`Array β` 的数组和类型为 {leanRef}`α` 的标量。在最后一个 {kw}`#eval` 中，注意该实例在数组的数组上被使用了两次。

输出参数在实例合成过程中会被忽略。即使实例合成发生在输出参数的值已经确定的上下文中，这些值也会被忽略。一旦 Lean 使用输入参数找到了一个实例，它会确保输出参数的既有已知值与所找到的值相匹配。

Lean 还具有 {deftech}_半输出参数_，它们兼有输入参数和输出参数的一些特征。像输入参数一样，半输出参数在选择实例时会被考虑；像输出参数一样，它们可用于实例化未知值。然而，它们并不会唯一地完成这一点。带有半输出参数的实例合成可能更难预测，因为实例被考虑的顺序可能决定所选实例，但它也更加灵活。

# 默认实例
%%%
tag := "default-instances"
%%%

在类 {leanRef}`HMul` 中，参数 {leanRef}`α` 和 {leanRef}`β` 被当作输入值。因此，类型类合成只有在这两个类型已知后才会开始。这常常可能过于受限。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

/--
error: typeclass instance problem is stuck
  HMul Int ?m.2 (?m.11 y)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `HMul` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
#eval fun y => xs.map (fun x => hMul x y)
------
end Ex
```

Lean 没有合成实例 {leanRef}`HMul`，因为尚未给出 {leanRef}`y` 的类型。然而，在这种情形下，自然会假定 {leanRef}`y` 和 {leanRef}`x` 的类型应当相同。我们可以用 _默认实例_ 精确地实现这一点。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- fun y => List.map (fun x => hMul x y) xs : Int → List Int
------
end Ex
```

:::setup
```
variable {α : Type u} {β : Type v} {γ : Type w} {a : α} {b : β} {n : Nat}
variable [HAdd α β γ] [HSub α β γ] [HMul α β γ] [HDiv α β γ] [HMod α β γ]
```
通过给上面的实例加上属性 {attr}`[default_instance]`，我们指示 Lean 在待处理的类型类合成问题上使用此实例。Lean 的实际实现为算术运算符定义了同质和异质的类。此外，{lean}`a + b`、{lean}`a * b`、{lean}`a - b`、{lean}`a / b` 和 {lean}`a % b` 都是异质版本的记法。实例 {lean}`OfNat Nat n` 是 {lean}`OfNat` 类的默认实例（优先级为 100）。这就是为什么在期望类型未知时，数值字面量 {lean}`2` 的类型为 {lean}`Nat`。可以定义更高优先级的默认实例来覆盖内建实例。
:::
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- 2 : Rational
```

:::setup
```
variable {α : Type u} {xs : List α} [Mul α] [OfNat α 2]
```

优先级也有助于控制不同默认实例之间的交互。例如，假设 {lean}`xs` 的类型为 {lean}`List α`。在精化 {lean}`xs.map (fun x => 2 * x)` 时，我们希望乘法的同质实例具有比 {lean}`OfNat α 2` 的默认实例更高的优先级。当我们只实现了实例 {lean}`HMul α α α` 而没有实现 {lean}`HMul Nat α α` 时，这一点尤其重要。现在，我们展示 Lean 中记法 {lit}`a * b` 是如何定义的。
:::
```lean
namespace Ex
------
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
------
end Ex
```

{leanRef}`Mul` 类对于只实现同质乘法的类型很方便。

# 局部实例
%%%
tag := "local-instances"
%%%

在 Lean 中，类型类是使用属性实现的。因此，可以使用 {kw}`local` 修饰符表示它们只在当前 {kw}`section` 或 {kw}`namespace` 关闭之前有效，或一直有效到当前文件末尾。

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p
```

也可以使用 {kw}`attribute` 命令临时禁用一个实例，直到当前 {kw}`section` 或 {kw}`namespace` 关闭，或直到当前文件末尾。

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p  -- Error: failed to synthesize instance
```

我们建议你只在诊断问题时使用此命令。

# 作用域实例
%%%
tag := "scoped-instances"
%%%

也可以在命名空间中声明作用域实例。这类实例只有在你位于该命名空间内部或打开该命名空间时才处于活动状态。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

/--
error: failed to synthesize instance of type class
  HAdd Point Point ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (error) in
#check fun (p : Point) => p + p + p

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

可以使用命令 {kw}`open scoped`{lit}` <namespace>` 来激活作用域属性，但不会“打开”该命名空间中的名称。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

/--
error: Unknown identifier `double`
-/
#guard_msgs (error) in
#check fun (p : Point) => double p
```

# 可判定命题
%%%
tag := "decidable-propositions"
%%%

让我们考虑标准库中定义的另一个类型类示例，即 {lean}`Decidable` 命题的类型类。粗略地说，如果我们能够判定一个 {lean}`Prop` 的元素是真还是假，就说它是可判定的。这一区分只在构造性数学中有用；在经典意义下，每个命题都是可判定的。但是，如果我们使用经典原则，例如按情况定义函数，那么该函数将不是可计算的。从算法角度看，{lean}`Decidable` 类型类可用于推断一个能有效判断该命题是否为真的过程。因此，该类型类在可能时支持这类计算性定义，同时又允许平滑过渡到经典定义和经典推理。

在标准库中，{lean}`Decidable` 形式上定义如下：

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

:::setup
```
variable {p : Prop} (t : Decidable p) (t' : p ∨ ¬p) (a b : α)
```

从逻辑上说，拥有一个元素 {lean}`t : Decidable p` 强于拥有一个元素 {lean}`t' : p ∨ ¬p`；它使我们能够根据 {lean}`p` 的真值定义任意类型的值。例如，要使表达式 {lean}`if p then a else b` 有意义，我们需要知道 {lean}`p` 是可判定的。该表达式是 {lean}`ite p a b` 的语法糖，而 {lean}`ite` 定义如下：
:::
```lean
namespace Hidden
------
def ite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t e : α) : α :=
  h.casesOn (motive := fun _ => α) (fun _ => e) (fun _ => t)
------
end Hidden
```

:::leanFirst
标准库还包含 {leanRef}`ite` 的一个变体，称为 {leanRef}`dite`，即依赖的 if-then-else 表达式。它定义如下：

```lean
namespace Hidden
------
def dite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
------
end Hidden
```
:::

:::setup
```
variable {c : Prop} [Decidable c] (t : c → α) (e : ¬c → α) (hc : c) (hnc : ¬c)
```
```lean (show := false)
example [Decidable c] (t e : α) : α := if h : c then t else e
```

也就是说，在 {lean}`dite c t e` 中，我们可以在 “then” 分支中假设 {lean}`hc : c`，并在 “else” 分支中假设 {lean}`hnc : ¬c`。为了使 {lean}`dite` 更便于使用，Lean 允许我们写 {leanRef}`if h : c then t else e`，而不是 {lean}`dite c (fun h : c => t h) (fun h : ¬c => e h)`。
:::

没有经典逻辑，我们无法证明每个命题都是可判定的。但我们可以证明 _某些_ 命题是可判定的。例如，可以证明自然数和整数上的相等、比较等基本运算的可判定性。此外，可判定性在命题联结词下保持：

```lean
#check @instDecidableAnd -- @instDecidableAnd : {p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∧ q)

#check @instDecidableOr
#check @instDecidableNot
```

因此，我们可以在自然数上的可判定谓词上按情况进行定义：

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

打开隐式参数会显示，精化器仅通过应用适当的实例，便已推断出命题 {leanRef}`x < a ∨ x > b` 的可判定性。

借助经典公理，我们可以证明每个命题都是可判定的。可以导入经典公理，并通过打开 {lit}`Classical` 命名空间使通用的可判定性实例可用。

```lean
open Classical
```

:::setup
```
open Classical
variable {p : Prop}
```
此后，对于每个 {lean}`p`，{lean}`Decidable p` 都有一个实例。因此，当你想进行经典推理时，库中所有依赖可判定性假设的定理都可以自由使用。在 {ref "axioms-and-computation"}[公理与计算] 中，我们将看到，使用排中律来定义函数可能会阻止它们以计算方式使用。因此，标准库为 {lean}`propDecidable` 实例赋予较低优先级。
:::

```lean
namespace Hidden
------
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
------
end Hidden
```

这保证了 Lean 会优先采用其他实例，只有在推断可判定性的其他尝试都失败后，才退回到 {leanRef}`propDecidable`。

{lean}`Decidable` 类型类还为证明定理提供了一点小规模自动化。标准库引入了策略 {tactic}`decide`，它使用 {lean}`Decidable` 实例来解决简单目标；还引入了函数 {name}`decide`，它使用 {lean}`Decidable` 实例来计算相应的 {lean}`Bool`。

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬(True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1 + 1 := by
  decide

#print ex

#check @of_decide_eq_true -- @of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p

#check @decide -- decide : (p : Prop) → [h : Decidable p] → Bool
```

:::setup
```
variable {p : Prop} [Decidable p]
```

它们的工作方式如下。表达式 {lean}`decide p` 尝试推断 {leanRef}`p` 的判定过程；若成功，则求值为 {lean}`true` 或 {lean}`false`。特别地，如果 {leanRef}`p` 是一个为真的闭表达式，那么 {leanRef}`decide p` 会按定义归约为布尔值 {lean}`true`。在假设 {lean}`decide p = true` 成立时，{lean}`of_decide_eq_true` 产生 {lean}`p` 的证明。策略 {tactic}`decide` 将这些合在一起以证明目标 {lean}`p`。根据前面的观察，只要为 {lean}`p` 推断出的判定过程有足够信息按定义求值到 {lean}`isTrue` 情形，{tactic}`decide` 就会成功。
:::

# 管理类型类推断
%%%
tag := "managing-type-class-inference"
%%%

如果你遇到需要提供一个 Lean 能够通过类型类推断推得的表达式的情形，可以要求 Lean 使用 {name}`inferInstance` 执行该推断：

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance -- @inferInstance : {α : Sort u_1} → [i : α] → α
```

:::setup
```
variable (t : T)
```

事实上，可以使用 Lean 的 {lean}`(t : T)` 记法以简洁方式指定你要寻找其实例的类：
:::

```lean
#check (inferInstance : Add Nat)
```

也可以使用辅助定义 {lit}`inferInstanceAs`：

```lean
#check (inferInstanceAs (Add Nat) : Add Nat)
```

:::leanFirst
有时 Lean 找不到实例，是因为该类隐藏在某个定义之下。例如，Lean 无法找到 {leanRef}`Inhabited (Set α)` 的实例。我们可以显式声明一个：

```lean
def Set (α : Type u) := α → Prop

/--
error: failed to synthesize instance of type class
  Inhabited (Set α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Inhabited (Set α) :=
  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```
:::

有时，你可能会发现类型类推断无法找到期望的实例；更糟的是，它可能陷入无限循环并超时。为帮助调试这些情形，Lean 允许你请求搜索轨迹：

```lean
set_option trace.Meta.synthInstance true
```

如果使用 VS Code，可以将鼠标悬停在相关定理或定义上读取结果，或者用 {kbd}[`Ctrl` `Shift` `Enter`] 打开消息窗口。

也可以使用以下选项限制搜索：

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

选项 {option}`synthInstance.maxHeartbeats` 指定每个类型类解析问题的最大心跳数。一个心跳指（小规模）内存分配的次数（以千为单位）；0 表示没有限制。选项 {option}`synthInstance.maxSize` 是在类型类实例合成过程中用于构造解的最大实例数。

还要记住，在 VS Code 和 Emacs 两种编辑器模式中，{kw}`set_option` 中都可以使用 Tab 补全来帮助你找到合适的选项。

如上所述，给定上下文中的类型类实例表示一个类似 Prolog 的程序，由此产生回溯搜索。程序的效率以及找到的解都可能依赖于系统尝试实例的顺序。后声明的实例会先被尝试。此外，如果实例在其他模块中声明，则它们被尝试的顺序取决于命名空间打开的顺序。较晚打开的命名空间中声明的实例会较早被尝试。

可以通过给类型类实例指定 _优先级_ 来改变尝试它们的顺序。声明实例时，它会被赋予一个默认优先级值。定义实例时可以指定其他优先级。下面的例子说明了如何做到这一点：

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

# 使用类型类的强制转换
%%%
tag := "coercions-using-type-classes"
%%%

:::setup
```
variable {n : Nat} {α : Type u} {as : List α}
def Set (α : Type u) := α → Prop

```

最基本的强制转换把一个类型的元素映射到另一个类型。例如，从 {lean}`Nat` 到 {lean}`Int` 的强制转换允许我们把任意元素 {lean}`n : Nat` 看作 {lean}`Int` 的元素。但有些强制转换依赖于参数；例如，对于任意类型 {lean}`α`，我们可以把任意元素 {lean}`as : List α` 看作 {lean}`Set α` 的元素，即列表中出现的元素所组成的集合。相应的强制转换定义在由 {lean}`α` 参数化的类型“族” {lean}`List α` 上。
:::

Lean 允许我们声明三类强制转换：

- 从一个类型族到另一个类型族
- 从一个类型族到 sort 类
- 从一个类型族到函数类型类

第一类强制转换允许我们把源族某个成员的任意元素看作目标族相应成员的元素。第二类强制转换允许我们把源族某个成员的任意元素看作一个类型。第三类强制转换允许我们把源族的任意元素看作一个函数。下面依次考察这三类。

:::setup
```
variable {α : Type u} {β : Type v} [Coe α β]
```

在 Lean 中，强制转换建立在类型类解析框架之上。通过声明 {lean}`Coe α β` 的实例，我们定义从 {lean}`α` 到 {lean}`β` 的强制转换。例如，可以如下定义从 {lean}`Bool` 到 {lean}`Prop` 的强制转换：

```lean
instance : Coe Bool Prop where
  coe b := b = true
```
:::

这使我们能够在 {kw}`if`-{kw}`then`-{kw}`else` 表达式中使用布尔项：

```lean
#eval if true then 5 else 3

#eval if false then 5 else 3
```

:::leanFirst
可以如下定义从 {leanRef}`List α` 到 {leanRef}`Set α` 的强制转换：

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
------
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}

#check s ∪ [2, 3] -- s ∪ [2, 3].toSet : Set Nat
```
:::

可以使用记法 {lit}`↑` 强制在特定位置引入强制转换。这也有助于明确我们的意图，并绕过强制转换解析系统的局限。

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet
instance : Coe (List α) (Set α) where
  coe a := a.toSet
------
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x -- let x := [2, 3].toSet; s ∪ x : Set Nat

#check let x := [2, 3]; s ∪ x -- let x := [2, 3]; s ∪ x.toSet : Set Nat
```


Lean 还通过类型类 {lean}`CoeDep` 支持依赖强制转换。例如，不能把任意命题强制转换为 {lean}`Bool`，只能转换那些实现了 {lean}`Decidable` 类型类的命题。

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

必要时，Lean 还会链接（非依赖的）强制转换。实际上，类型类 {lean}`CoeT` 是 {lean}`Coe` 的传递闭包。

现在考虑第二类强制转换。所谓 _sort 类_，是指宇宙 {lean}`Type u` 的集合。第二类强制转换具有如下形式：

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

其中 {lit}`F` 是如上的一个类型族。这允许我们在 {lit}`t` 的类型为 {lit}`F a₁ ... aₙ` 时写 {lit}`s : t`。换言之，该强制转换允许我们把 {lit}`F a₁ ... aₙ` 的元素看作类型。这在定义代数结构时非常有用，因为其中一个组成部分，即结构的载体，是一个 {lean}`Type`。例如，可以如下定义半群：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

:::setup

```
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

variable {S : Semigroup} (a b : S.carrier)

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
universe u
```
换言之，一个半群由一个类型 {leanRef}`carrier` 和一个乘法 {leanRef}`mul` 组成，并满足乘法结合律这一性质。只要有 {lean}`a b : S.carrier`，{kw}`instance` 命令就允许我们写 {lean}`a * b`，而不是 {lean}`Semigroup.mul S a b`；注意，Lean 可以从 {leanRef}`a` 和 {leanRef}`b` 的类型推断出参数 {leanRef}`S`。函数 {lean}`Semigroup.carrier` 将类 {leanRef}`Semigroup` 映射到 sort {leanRef}`Type u`：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
#check Semigroup.carrier -- Semigroup.carrier.{u} (self : Semigroup) : Type u
```

如果把这个函数声明为强制转换，那么每当有一个半群 {lean}`S : Semigroup` 时，我们就可以写 {lean}`a : S`，而不是 {lean}`a : S.carrier`：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

正是这个强制转换使得写 {leanRef}`(a b c : S)` 成为可能。注意，我们定义的是 {leanRef}`CoeSort Semigroup (Type u)` 的实例，而不是 {lean}`Coe Semigroup (Type u)`。

:::

::::setup
```
variable (B : Type u) (C : Type v)

```

所谓 _函数类型类_，是指 Pi 类型 {lean}`(z : B) → C` 的集合。第三类强制转换具有如下形式：

```
    c : (x₁ : A₁) → ... → (xₙ : Aₙ) → (y : F x₁ ... xₙ) → (z : B) → C
```

:::leanFirst
其中 {lit}`F` 同样是一个类型族，而 {lit}`B` 和 {lit}`C` 可以依赖于 {lit}`x₁, ..., xₙ, y`。这使得每当 {lit}`t` 是 {lit}`F a₁ ... aₙ` 的元素时，都可以写 {lit}`t s`。换言之，该强制转换使我们能够把 {lit}`F a₁ ... aₙ` 的元素看作函数。继续上面的例子，我们可以定义半群 {leanRef}`S1` 与 {leanRef}`S2` 之间的态射概念。也就是说，这是一个从 {leanRef}`S1` 的载体到 {leanRef}`S2` 的载体的函数（注意这里的隐式强制转换），并且它保持乘法。投影 {leanRef}`Morphism.mor` 将一个态射映射到底层函数：


```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
------
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```
:::

因此，它是第三类强制转换的天然候选。
::::

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
------
instance (S1 S2 : Semigroup) :
    CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
```

有了这个强制转换后，我们可以写 {leanRef}`f (a * a * a)`，而不是 {leanRef}`f.mor (a * a * a)`。当 {leanRef}`Morphism` 即 {leanRef}`f` 被用于期望函数的地方时，Lean 会插入该强制转换。类似于 {lean}`CoeSort`，我们还有另一个类 {lean}`CoeFun` 用于这一类强制转换。参数 {lit}`γ` 用于指定要强制转换到的函数类型。该类型可以依赖于被强制转换来源的类型。
