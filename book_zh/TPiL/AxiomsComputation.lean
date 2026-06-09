import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "公理与计算" =>
%%%
tag := "axioms-and-computation"
file := "Axioms-and-Computation"
%%%

我们已经看到，Lean 中实现的构造演算（Calculus of Constructions）的版本包含依值函数类型、
归纳类型，以及一个宇宙层级；该层级以位于底部的
{tech (key := "impredicative")}[非直谓]、{tech (key := "proof irrelevance")}[证明无关性] {lean}`Prop` 为起点。
在本章中，我们考察用额外公理和规则扩展 CIC 的方式。以这种方式扩展一个基础系统通常很方便；
它既可能使我们证明更多定理，也可能使本来可以证明的定理更易于证明。
但是，加入额外公理也可能产生负面后果，而且这些后果可能超出对其正确性的担忧。
特别地，公理的使用会影响定义和定理的计算内容；这正是我们将在这里探讨的问题。

Lean 旨在同时支持计算式推理和经典推理。愿意这样做的用户可以坚持使用一个“计算上纯净”的片段，
该片段保证系统中的闭表达式会求值为规范范式。特别地，例如，任何类型为 {lean}`Nat` 的、
计算上纯净的闭表达式都会规约为一个数码。

Lean 的标准库定义了一个额外公理，即命题外延性，以及一个商构造；
后者又蕴含函数外延性原则。例如，这些扩展被用于发展集合和有限集合的理论。
我们将在下文看到，使用这些定理可能会阻塞 Lean 内核中的求值，
使得类型为 {lean}`Nat` 的闭项不再求值为数码。不过，Lean 在将定义编译为可执行代码时会擦除类型和命题信息；
而这些公理只加入新的命题，因此它们与这种计算解释相容。
即使偏重计算的用户，也可能希望使用经典的排中律来推理计算。
这同样会阻塞内核中的求值，但与编译后的代码相容。

标准库还定义了一个选择原则；它与计算解释完全相悖，因为它会从断言某对象存在的命题中神奇地产生“数据”。
它的使用对某些经典构造至关重要，用户可以在需要时导入它。
但是，使用这一构造来产生数据的表达式没有计算内容；在 Lean 中，我们必须把这样的定义标记为
{kw}`noncomputable`，以表明这一事实。

借助一个巧妙的技巧（称为 Diaconescu 定理），可以从命题外延性、函数外延性和选择原则推出排中律。
然而，如上所述，只要排中律以及其他经典原则不被用来制造数据，它们的使用仍然与编译相容。

概括地说，在宇宙、依值函数类型和归纳类型这一底层框架之上，标准库又加入了三个组成部分：

- 命题外延性公理
- 一个商构造，它蕴含函数外延性
- 一个选择原则，它从存在命题中产生数据。

前两者会阻塞 Lean 内部的规范化，但与代码生成相容；而第三者则不适合计算解释。
下面我们将更精确地说明这些细节。

# 历史与哲学背景
%%%
tag := "historical-and-philosophical-context"
%%%

:::setup
```
variable (x : α) (y : β)
```

在其历史的大部分时期，数学在本质上是计算性的：几何研究几何对象的构造，代数关注方程组的算法解法，
而分析则提供计算随时间演化的系统未来行为的方法。从一个表明“对每个 {lean}`x`，
存在一个 {lean}`y` 使得……”的定理证明中，通常可以直接提取出一个算法，
用于在给定 {lean}`x` 时计算这样的 {lean}`y`。
:::

然而，在十九世纪，数学论证复杂性的增长促使数学家发展出新的推理风格：
这些风格压制算法信息，并使用对数学对象的描述，而这些描述抽象掉了对象表示方式的细节。
其目标是在不陷入计算细节的情况下获得有力的“概念性”理解；
但其结果是允许了一些在直接计算性解读下根本为 _假_ 的数学定理。

今天，人们仍然相当一致地认为计算对数学很重要。但关于如何最好地处理计算方面的关切，却存在不同看法。
从 _构造性_ 的观点看，把数学同其计算根源分离开来是错误的；
每一个有意义的数学定理都应当具有直接的计算解释。从 _经典_ 的观点看，保持关注点分离更有成效：
我们可以使用一种语言和一套方法来编写计算机程序，同时保留使用非构造性理论和方法来推理这些程序的自由。
Lean 被设计为支持这两种进路。库的核心部分以构造性方式发展，
但系统也提供了进行经典数学推理的支持。

:::setup
```
open Nat
notation "… " e "…" => e
```

从计算的角度看，依值类型论中最纯粹的部分完全避免使用 {lean}`Prop`。
归纳类型和依值函数类型可以被视为数据类型，而这些类型的项可以通过不断应用规约规则来“求值”，
直到没有更多规则可用为止。原则上，任何类型为 {lean}`Nat` 的闭项
（也就是没有自由变量的项）都应当求值为一个数码，{lean}`succ (… (succ zero)…)`。
:::

:::setup
```
variable (p : Prop) (s t : α) (prf : p)
notation x " = " y " : " α => @Eq α x y
```

引入证明无关的 {lean}`Prop` 并将定理标记为不可规约，是迈向关注点分离的第一步。
其意图是，类型 {lean}`p : Prop` 的元素不应在计算中扮演任何角色；
因此，从这个意义上说，项 {lean}`prf : p` 的具体构造是“无关的”。
我们仍然可以定义包含 {lean}`Prop` 类型元素的计算对象；要点在于，这些元素可以帮助我们推理计算的效果，
但在从项中提取“代码”时可以被忽略。然而，{lean}`Prop` 类型的元素并非完全无害。
它们包括任意类型 {lean}`α` 上的等式 {lean}`s = t : α`，而这样的等式可作为强制转换使用，
以便对项进行类型检查。下面我们将看到这类强制转换如何阻塞系统中的计算。
不过，在一种会擦除命题内容、忽略中间类型约束并将项规约到范式的求值方案下，计算仍然是可能的。
这正是 Lean 的虚拟机所做的事情。

一旦采用证明无关的 {lean}`Prop`，人们就可能认为使用例如排中律 {lean}`p ∨ ¬p` 是正当的，
其中 {lean}`p` 是任意命题。当然，按照 CIC 的规则，这同样可能阻塞计算；
但如上所述，它并不妨碍生成可执行代码。只有在 {ref "choice"}[关于选择的章节] 中讨论的选择原则，
才会完全抹去理论中证明无关部分与数据相关部分之间的区别。

:::

# 命题外延性
%%%
tag := "propositional-extensionality"
%%%

命题外延性是如下公理：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
axiom propext {a b : Prop} : (a ↔ b) → a = b
------
end Hidden
```

:::setup
```
variable (a : Prop)
```
它断言：当两个命题相互蕴含时，它们实际上相等。这与集合论解释相容；
在这种解释中，任意元素 {lean}`a : Prop` 要么为空，要么是单元素集合
$`\{\ast\}`，其中 $`\ast` 是某个指定元素。该公理的效果是，
等价命题可以在任何语境中相互替换：
:::

```lean
variable (a b c d e : Prop)

theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

:::comment
```
<!--
第一个例子可以不使用 `propext` 而以更繁琐的方式证明，
做法是利用命题联结词尊重命题等价这一事实。第二个例子则体现了
`propext` 更本质的用法。事实上，它与 `propext` 本身等价；
我们鼓励你证明这一点。

给定 Lean 中任意定义或定理，你都可以使用 ``#print
axioms`` 命令显示它所依赖的公理。

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
    propext h ▸ h₁

    -- BEGIN
    #print axioms thm₁  -- propext
    #print axioms thm₂  -- propext
    -- END
-->
```
:::

# 函数外延性
%%%
tag := "function-extensionality"
%%%

:::leanFirst
与命题外延性类似，函数外延性断言：任意两个类型为 {leanRef}`(x : α) → β x` 的函数，
只要它们在所有输入上的取值都相同，就相等：

```signature
funext.{u, v}
  {α : Sort u} {β : α → Sort v}
  {f g : (x : α) → β x}
  (h : ∀ (x : α), f x = g x) :
  f = g
```
:::

从经典的集合论观点看，这正是两个函数相等的含义。这被称为函数的“外延”观点。
然而，从构造性观点看，把函数看作以某种显式方式给出的算法或计算机程序，有时更为自然。
当然，两个计算机程序虽然语法上相当不同，却完全可能对每个输入计算出相同答案。
与此类似，你也许希望保持一种函数观，它并不强迫你把具有相同输入 / 输出行为的两个函数等同起来。
这被称为函数的“内涵”观点。

事实上，函数外延性可以从商的存在推出；我们将在下一节描述商。
因此，在 Lean 标准库中，{leanRef}`funext`
[是由商构造证明的](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)。

:::leanFirst
假设对 {leanRef}`α : Type u`，我们定义 {leanRef}`Set `{leanRef (in := "(α : Type u)")}`α`{leanRef}` := α → Prop`
来表示 {leanRef (in := "(α : Type u)")}`α` 的子集类型，本质上是把子集同谓词等同起来。
结合 {leanRef}`funext` 和 {leanRef}`propext`，我们便得到这类集合的外延理论：

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```
:::

于是，例如，我们可以继续定义空集和集合交，并证明集合恒等式：

```lean
def Set (α : Type u) := α → Prop
namespace Set
def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) "∈" => mem
theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))
------
def empty : Set α := fun _ => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun _ => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
-----
end Set
```

下面的例子说明函数外延性如何阻塞 Lean 内核内部的计算：

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- 不会规约为 0
#reduce val

-- 求值为 0
#eval val
```

首先，我们用函数外延性说明两个函数 {leanRef}`f` 和 {leanRef}`g` 相等；
然后在类型中把 {leanRef}`f` 替换为 {leanRef}`g`，从而对类型为 {leanRef}`Nat` 的 {leanRef}`0` 作强制转换。
当然，这个强制转换是空洞的，因为 {lean}`Nat` 并不依赖于 {leanRef}`f`。
但这已足以造成影响：在系统的计算规则下，我们现在得到一个类型为 {lean}`Nat` 的闭项，
它不会规约为数码。在这个例子中，我们也许会想把该表达式规约为 {lean}`0`。
但在非平凡的例子中，消去强制转换会改变项的类型，从而可能使外围表达式的类型不正确。
不过，虚拟机可以毫无困难地把该表达式求值为 {lean}`0`。
下面是一个类似的人为例子，展示 {lean}`propext` 如何造成阻碍：

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- 不会规约为 0
#reduce val

-- 求值为 0
#eval val
```

当前的一些研究计划，包括关于 _观测类型论_ 和 _立方类型论_ 的工作，
旨在以允许涉及函数外延性、商以及更多构造的强制转换进行规约的方式扩展类型论。
但是，解决方案并不那么清晰明确，而且 Lean 底层演算的规则并不认可这样的规约。

然而，从某种意义上说，强制转换并不改变表达式的含义。
它更像是一种用于推理表达式类型的机制。给定合适的语义，就可以按保持含义的方式规约项，
而忽略为使规约保持类型正确所需的中间簿记。在这种情况下，在 {lean}`Prop` 中加入新公理并不重要；
由于 {tech (key := "proof irrelevance")}[证明无关性]，{lean}`Prop` 中的表达式不携带信息，可以被规约过程安全地忽略。

# 商
%%%
tag := "quotients"
%%%

:::setup
```
variable (α : Sort u) (r : α → α → Prop) (f : α → β) (x y : α) (f' : Quot r → β)
notation α " / " r:max => Quot (α := α) r
notation "⟦" x "⟧" => Quot.mk _ x

```
令 {lean}`α` 为任意类型，令 {lean}`r` 为 {lean}`α` 上的等价关系。
在数学中，形成“商” {lean}`α / r` 是很常见的；也就是说，形成 {lean}`α` 的元素“模” {lean}`r` 所得到的类型。
从集合论角度看，可以把 {lean}`α / r` 看作 {lean}`α` 关于 {lean}`r` 的等价类集合。
如果 {lean}`f : α → β` 是任意尊重该等价关系的函数，即对每个 {lean}`x y : α`，
{lean}`r x y` 都蕴含 {lean}`f x = f y`，那么 {lean}`f` 就“提升”为定义在各个等价类上的函数
{lean}`f' : α / r → β`，满足对 {lean (type := "Quot r")}`⟦x⟧` 有
{lean}`f' ⟦x⟧ = f x`。Lean 的标准库用额外常量扩展构造演算，正是为了实现这些构造，
并将最后这个等式安装为定义性规约规则。

在最基本的形式中，商构造甚至不要求 {lean}`r` 是等价关系。
以下常量内建于 Lean：
:::

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
------
end Hidden
```
:::setup
```
variable (α : Type u) (r : α → α → Prop) (a : α) (f : α → β) (h : ∀ a b, r a b → f a = f b)
```
第一个常量在给定类型 {lean}`α` 以及 {lean}`α` 上任意二元关系 {lean}`r` 时形成类型 {lean}`Quot r`。
第二个常量把 {lean}`α` 映到 {lit}`Quot α`，因此若 {lean}`r : α → α → Prop` 且 {lit}`a : α`，
则 {lean}`Quot.mk r a` 是 {lean}`Quot r` 的元素。第三个原则 {lean}`Quot.ind` 说明，
{lean}`Quot.mk r a` 的每个元素都具有这种形式。至于 {lean}`Quot.lift`，
给定函数 {lean}`f : α → β`，若 {lean}`h` 是 {lean}`f` 尊重关系 {lean}`r` 的证明，
则 {lean}`Quot.lift f h` 是 {lean}`Quot r` 上相应的函数。
其想法是，对 {lean}`α` 中的每个元素 {lean}`a`，函数 {lean}`Quot.lift f h` 把
{lean}`Quot.mk r a`（包含 {lean}`a` 的 {lean}`r`-类）映到 {lean}`f a`，
而 {lean}`h` 说明这个函数是良定义的。事实上，计算原则被声明为规约规则，
如下证明所示。


```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- 商类型
#check (Quot mod7Rel : Type)

-- 与 4 等价的数所在的类
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- 计算原则
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl
```


这四个常量 {lean}`Quot`、{lean}`Quot.mk`、{lean}`Quot.ind` 和
{lean}`Quot.lift` 本身并不很强。你可以检查，如果简单地把 {lean}`Quot r` 取为
{lean}`α`，并把 {lean}`Quot.lift` 取为恒等函数（忽略 {lean}`h`），那么 {lean}`Quot.ind` 仍然成立。
因此，这四个常量并不被视为额外公理。
:::

:::comment
```
<!--
    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl
    -- BEGIN
    #print axioms thm   -- no axioms
    -- END
-->
```
:::

它们和归纳定义的类型及其相关构造子与递归子一样，被视为逻辑框架的一部分。

使 {lean}`Quot` 构造成为真正商的是下面这个额外公理：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u v
------
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
```

这个公理断言：{leanRef}`α` 中任何两个由 {leanRef}`r` 关联的元素，在商中都会被等同。
如果某个定理或定义使用了 {leanRef}`Quot.sound`，它就会出现在 {kw}`#print axioms` 命令的输出中。

:::setup
```
variable (α : Type u) (r : α → α → Prop)  (r' r'': α → α → Prop) (a b : α)
```

当然，商构造最常用于 {lean}`r` 是等价关系的情形。给定如上的 {lean}`r`，
如果我们按规则“{lean}`r' a b` 当且仅当 {lean}`Quot.mk r a = Quot.mk r b`”来定义 {lean}`r'`，
那么显然 {lean}`r'` 是一个等价关系。事实上，{lean}`r'` 是函数 {lean}`fun a => Quot.mk r a` 的 _核_。
公理 {lean}`Quot.sound` 表明 {lean}`r a b` 蕴含 {lean}`r' a b`。
使用 {lean}`Quot.lift` 和 {lean}`Quot.ind`，我们可以说明 {lean}`r'` 是包含 {lean}`r` 的最小等价关系；
也就是说，如果 {lean}`r''` 是任何包含 {lean}`r` 的等价关系，那么 {lean}`r' a b` 蕴含 {lean}`r'' a b`。
特别地，如果 {lean}`r` 一开始就是等价关系，那么对所有 {lean}`a` 和 {lean}`b`，
都有 {lean}`r a b` 当且仅当 {lean}`r' a b`。
:::

为了支持这种常见用法，标准库定义了 _setoid_ 的概念；它不过是一个带有关联等价关系的类型：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
------
end Hidden
```

给定一个类型 {leanRef (in := "Setoid (α")}`α`、{leanRef (in := "Setoid (α")}`α`
上的关系 {leanRef (in := "Equivalence r")}`r`，以及证明 {leanRef}`iseqv`
表明 {leanRef (in := "Equivalence r")}`r` 是等价关系，我们就可以定义
{leanRef (in := "class Setoid")}`Setoid` 类的一个实例。

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
------
end Hidden
```

:::setup
```
variable (α : Type u) [Setoid α] (a b : α)
```


常量 {lean}`Quotient.mk`、{lean}`Quotient.ind`、{lean}`Quotient.lift` 和
{lean}`Quotient.sound` 无非是 {lean}`Quot` 中相应元素的特化。
类型类推断能够找到与类型 {lean}`α` 关联的 setoid，这带来若干好处。
首先，我们可以用记号 {lean}`a ≈ b`（通过 {kbd}`\approx` 输入）表示 {lean}`Setoid.r a b`；
在记号 {lean}`Setoid.r` 中，{lean}`Setoid` 的实例是隐式的。
我们可以使用通用定理 {lean}`Setoid.refl`、{lean}`Setoid.symm`、{lean}`Setoid.trans`
来推理该关系。特别是对商而言，我们可以使用定理 {lean}`Quotient.exact`：

```signature
Quotient.exact {α : Sort u} {s : Setoid α} {a b : α} :
  Quotient.mk s a = Quotient.mk s b →
  a ≈ b
```

结合 {lean}`Quotient.sound`，这表明商的元素与 {lean}`α` 中元素的等价类精确对应。

:::

:::setup
```
variable (α : Type u) (β : Type v)
```

回忆一下，在标准库中，{lean}`α × β` 表示类型 {lean}`α` 和 {lean}`β` 的笛卡尔积。
为了说明商的用法，我们把类型 {lean}`α` 的元素的 _无序_ 对类型定义为类型 {lean}`α × α` 的一个商。
首先，我们定义相关的等价关系：
:::
```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

下一步是证明 {leanRef}`eqv` 确实是等价关系；也就是说，它是自反的、对称的和传递的。
我们可以用依值模式匹配进行分类讨论，并把假设拆成若干部分，再重新组合以得到结论；
这样能以方便且可读的方式证明这三个事实。

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
------
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

:::leanFirst
既然已经证明 {leanRef}`eqv` 是等价关系，我们就可以构造一个 {leanRef}`Setoid (α × α)`，
并用它定义无序对类型 {leanRef}`UProd α`。

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
------
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```
:::

:::setup
```
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)


notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd

variable (a₁ a₂ : α)
```

注意，我们在局部把无序对的记号 {lean}`{a₁, a₂}` 定义为 {lean}`Quotient.mk' (a₁, a₂)`。
这对说明例子很有用，但通常并不是好主意，因为该记号会遮蔽花括号的其他用途，
例如用于记录和集合。

我们可以很容易地用 {lean}`Quot.sound` 证明 {lean}`{a₁, a₂} = {a₂, a₁}`，
因为有 {lean}`(a₁, a₂) ~ (a₂, a₁)`。
:::

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
------
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
end UProd
```

:::leanFirst
为了完成这个例子，给定 {leanRef}`a : α` 和 {leanRef}`u : UProd α`，
我们定义命题 {leanRef (in := "mem (a : α) (u : UProd α)")}`a`{lit}`  ∈  `{leanRef (in := "mem (a : α) (u : UProd α)")}`u`；
当 {leanRef (in := "mem (a : α) (u : UProd α)")}`a` 是无序对
{leanRef (in := "mem (a : α) (u : UProd α)")}`u` 的元素之一时，它应当成立。
首先，我们在（有序）对上定义一个类似命题
{leanRef}`mem_fn`{leanRef (in := "mem (a : α) (u : UProd α)")}` a`{leanRef (in := "mem (a : α) (u : UProd α)")}` u`；
然后用引理 {leanRef}`mem_respects` 说明 {leanRef}`mem_fn` 尊重等价关系 {leanRef}`eqv`。
这是 Lean 标准库中广泛使用的一种惯用法。

```lean
set_option linter.unusedVariables false
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- 用于证明 mem_respects 的辅助引理
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h

private theorem mem_respects : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by
    simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by
    simp_all only
    apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
---------
end UProd
```
:::

为方便起见，标准库还定义了 {lean}`Quotient.lift₂`，用于提升二元函数；
并定义了 {lit}`Quotient.ind₂`，用于对两个变量进行归纳。

:::setup
```
variable (α : Sort u) (β : α → Sort v) (f₁ f₂ f : (x : α) → β x) (a : α)

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} : extfun α β → (x : α) → β x := fun f x =>
  Quot.lift (· x) (by intros; simp [*]) f

```

本节最后，我们提示一下为什么商构造蕴含函数外延性。要说明 {lean}`(x : α) → β x`
上的外延相等是一个等价关系并不困难，因此我们可以考虑函数“模等价”得到的类型
{lean}`extfun α β`。当然，函数应用尊重这种等价：如果 {lean}`f₁` 等价于 {lean}`f₂`，
那么 {lean}`f₁ a` 等于 {lean}`f₂ a`。因此，应用诱导出一个函数
{lean}`extfun_app : extfun α β → (x : α) → β x`。
但对每个 {lean}`f`，{lean}`extfun_app (.mk _ f)` 按定义等于 {lean}`fun x => f x`，
而后者又按定义等于 {lean}`f`。所以，当 {lean}`f₁` 和 {lean}`f₂` 外延相等时，
我们有如下等式链：

```lean
variable {α : Sort u} {β : α → Sort v}

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} (f : extfun α β) (x : α) : β x :=
  Quot.lift (· x) (by intros; simp [*]) f
----------
example (f₁ f₂ : (x : α) → β x) (h : ∀ x, f₁ x = f₂ x) :=
  calc f₁
    _ = extfun_app (.mk _ f₁) := rfl
    _ = extfun_app (.mk _ f₂) := by rw [Quot.sound]; trivial
    _ = f₂ := rfl

```

因此，{leanRef}`f₁` 等于 {leanRef}`f₂`。

:::

# 选择
%%%
tag := "choice"
%%%

:::leanFirst
为了陈述标准库中定义的最后一个公理，我们需要 {leanRef}`Nonempty` 类型，其定义如下：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
------
end Hidden
```
:::

:::setup
```
variable {α : Sort u}
```

由于 {lean}`Nonempty α` 的类型是 {lean}`Prop`，而它的构造子包含数据，因此它只能消去到 {lean}`Prop`。
事实上，{lean}`Nonempty α` 等价于 {lean}`∃ x : α, True`：
:::

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

现在，选择公理可以简单地表述如下：

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
------
axiom choice {α : Sort u} : Nonempty α → α
------
end Hidden
```

:::setup
```
variable {α : Sort u} {h : Nonempty α}
open Classical
```

仅给定断言 {lean}`h`，即 {lean}`α` 非空，{lean}`choice h` 就会神奇地产生 {lean}`α` 的一个元素。
当然，这会阻塞任何有意义的计算：按照 {lean}`Prop` 的解释，{lean}`h` 完全不包含如何找到这样一个元素的信息。

:::

它位于 {lit}`Classical` 命名空间中，因此该定理的全名是 {lean}`Classical.choice`。
选择原则等价于 *不定描述* 原则，后者可以用子类型表述如下：

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
axiom choice {α : Sort u} : Nonempty α → α
------
noncomputable def indefiniteDescription {α : Sort u}
    (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
------
end Hidden
```

:::setup
```
variable {α : Sort u} {h : Nonempty α}
open Classical
```
由于 {lean}`indefiniteDescription` 依赖于 {lean}`choice`，Lean 无法为它生成可执行代码，
因此要求我们把该定义标记为 {kw}`noncomputable`。同样在 {lit}`Classical` 命名空间中，
函数 {lean}`choose` 和性质 {lean}`choose_spec` 分解 {lean}`indefiniteDescription` 输出的两个部分：



```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
open Classical
namespace Hidden
------
variable {α : Sort u} {p : α → Prop}

noncomputable def choose (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
------
end Hidden
```

{lean}`choice` 原则还抹去了作为 {lean}`Nonempty` 的性质与更具构造性的作为 {lean}`Inhabited` 的性质之间的区别：

```lean
open Classical
------
noncomputable def inhabited_of_nonempty (h : Nonempty α) : Inhabited α :=
  choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```
:::

在下一节中，我们将看到 {lean}`propext`、{lean}`funext` 和 {leanRef}`choice` 合在一起
蕴含排中律以及所有命题的可判定性。利用这些原则，可以把不定描述原则加强如下：

::::setup
```
open Classical
```

```signature
strongIndefiniteDescription {α : Sort u} (p : α → Prop)
  (h : Nonempty α) :
  {x // (∃ (y : α), p y) → p x}
```


假设外围类型 {leanRef}`α` 非空，若存在满足 {leanRef}`p` 的 {lit}`α` 的元素，
则 {leanRef}`strongIndefiniteDescription`{leanRef}` `{leanRef}`p` 会产生这样一个元素。
该定义的数据部分通常称为 *Hilbert 的 epsilon 函数*：

```signature
Classical.epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α
```

```lean
#check @Classical.epsilon_spec
```


::::

# 排中律
%%%
tag := "the-law-of-the-excluded-middle"
%%%

排中律如下：

```signature
Classical.em : ∀ (p : Prop), p ∨ ¬p
```


[Diaconescu 定理](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) 表明，
选择公理足以推出排中律。更准确地说，它说明排中律可由
{lean}`Classical.choice`、{lean}`propext` 和 {lean}`funext` 推出。
我们概述标准库中的证明。

```save emProof
-- ANCHOR: emSetup
open Classical
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  -- ^ PROOF_STATE: em1
-- ANCHOR_END: emSetup
-- ANCHOR: emChoose
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  -- ^ PROOF_STATE: em2
-- ANCHOR_END: emChoose
-- ANCHOR: emCases
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut, true_ne_false]
-- ANCHOR_END: emCases
-- ANCHOR: emNext
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
-- ANCHOR_END: emNext
-- ANCHOR: emDone
  match not_uv_or_p with
  | Or.inl hne =>
    exact Or.inr (mt p_implies_uv hne)
  | Or.inr h   =>
    exact Or.inl h
-- ANCHOR_END: emDone
```

:::leanFirst
首先，我们导入必要的公理，并定义两个谓词 {leanRef}`U` 和 {leanRef}`V`：

```savedAnchor emSetup
open Classical
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
```

:::

如果 {leanRef}`p` 为真，那么 {lean}`Prop` 的每个元素都同时属于 {leanRef}`U` 和 {leanRef}`V`。
如果 {leanRef}`p` 为假，那么 {leanRef}`U` 是单元素集合 {leanRef}`True`，而 {leanRef}`V` 是单元素集合 {leanRef}`False`。

:::leanFirst
接下来，我们使用 {leanRef}`choose` 分别从 {leanRef}`U` 和 {leanRef}`V` 中选择一个元素：

```savedAnchor emChoose
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
```
:::

:::leanFirst
{leanRef}`U` 和 {leanRef}`V` 都是析取式，因此 {leanRef}`u_def` 和 {leanRef}`v_def`
表示四种情况。在其中一种情况下，{leanRef}`u = True` 且 {leanRef}`v = False`；
而在所有其他情况下，{leanRef}`p` 为真。因此我们有：

```savedAnchor emCases
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut, true_ne_false]
```
:::

另一方面，如果 {leanRef}`p` 为真，那么由函数外延性和命题外延性，
{leanRef}`U` 与 {leanRef}`V` 相等。根据 {leanRef}`u` 和 {leanRef}`v` 的定义，
这又蕴含它们也相等。

```savedAnchor emNext
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
```


把最后这两个事实合在一起，就得到所需结论：

```savedAnchor emDone
  match not_uv_or_p with
  | Or.inl hne =>
    exact Or.inr (mt p_implies_uv hne)
  | Or.inr h   =>
    exact Or.inl h
```


排中律的后果包括双重否定消去、分类证明和反证法；这些都在
{ref "classical-logic"}[经典逻辑] 一节中描述。
排中律和命题外延性蕴含命题完备性：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha =>
    Or.inl (propext (Iff.intro (fun _ => True.intro) (fun _ => ha)))
  | Or.inr hn =>
    Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
```

再结合选择原则，我们还得到更强的原则：每个命题都是可判定的。
回忆一下，{lean}`Decidable` 命题类定义如下：

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

::::setup
```
variable {p : Prop} {f : α → β} {c : Prop} [Decidable c] {t e : α}
open Classical (choose propDecidable)
```
:::leanFirst
与只能消去到 {lean}`Prop` 的 {lean}`p ∨ ¬ p` 不同，
类型 {lean}`Decidable p` 等价于和类型 {lit}`Sum p (¬ p)`，而后者可以消去到任意类型。
编写 if-then-else 表达式所需要的正是这种数据。

作为经典推理的一个例子，我们使用 {lean}`choose` 说明：如果 {lean}`f : α → β` 是单射且
{lean}`α` 是有居留元的，那么 {lean}`f` 有左逆。为了定义左逆 {leanRef}`linv`，
我们使用依值 if-then-else 表达式。回忆 {lean}`if h : c then t else e` 是
{lean}`dite c (fun h : c => t) (fun h : ¬ c => e)` 的记号。
在 {leanRef}`linv` 的定义中，选择被使用了两次：首先，用来说明
{leanRef}`(∃ a : α, f a = b)` 是“可判定的”；然后，用来选择一个满足
{leanRef}`f a = b` 的 {leanRef}`a`。注意，{lean}`propDecidable` 是一个作用域实例，
由 {leanRef}`open Classical` 命令激活。我们用这个实例来为
{kw}`if`-{kw}`then`-{kw}`else` 表达式提供依据。（另见
{ref "decidable-propositions"}[可判定命题] 中的讨论。）


```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := rfl
      _ = a         := inj feq
```

从经典观点看，{leanRef}`linv` 是一个函数。从构造性观点看，它不可接受；
因为一般而言无法实现这样的函数，所以该构造并不提供信息。
:::
::::
