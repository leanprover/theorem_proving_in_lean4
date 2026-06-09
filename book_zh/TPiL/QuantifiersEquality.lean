import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "量词与等式" =>
%%%
tag := "quantifiers-and-equality"
file := "Quantifiers-and-Equality"
%%%

```setup
variable {α : Type u} (p : α → Prop) (x y t : α) (r : α → α → Prop) {β : α → Type v}
```

上一章介绍了构造涉及命题联结词的陈述之证明的方法。本章将把逻辑构造的工具箱扩展到全称量词、存在量词以及等式关系。

# 全称量词
%%%
tag := "the-universal-quantifier"
%%%

注意，如果 {lean}`α` 是任意类型，那么 {lean}`α` 上的一元谓词 {lean}`p` 可以表示为类型为 {lean}`α → Prop` 的对象。在这种情况下，给定 {lean}`x : α`，{lean}`p x` 表示“{lean}`p` 对 {lean}`x` 成立”这一断言。类似地，对象 {lean}`r : α → α → Prop` 表示 {lean}`α` 上的二元关系：给定 {lean}`x y : α`，{lean}`r x y` 表示“{lean}`x` 与 {lean}`y` 相关”这一断言。

全称量词 {lean}`∀ x : α, p x` 应表示断言“对每个 {lean}`x : α`，{lean}`p x` 成立”。与命题联结词一样，在自然演绎系统中，“全称量词”由引入规则和消去规则刻画。非形式地说，引入规则表述为：

> 在 {lean}`x : α` 任意的上下文中，给定 {lean}`p x` 的一个证明，我们得到 {lean}`∀ x : α, p x` 的一个证明。

消去规则表述为：

> 给定 {lean}`∀ x : α, p x` 的一个证明以及任意项 {lean}`t : α`，我们得到 {lean}`p t` 的一个证明。

与蕴含的情形一样，命题即类型的解释现在发挥作用。回忆依赖箭头类型的引入规则和消去规则：

```setup
variable {α : Type u} (p : α → Prop) (x y : α) (r : α → α → Prop) {β : α → Type v} {t : {x : α} → β x}
```
> 在 {lean}`x : α` 任意的上下文中，给定类型为 {lean}`β x` 的项 {lean}`t`，我们有 {lean}`(fun x : α => t) : (x : α) → β x`。

```setup
variable {α : Type u} (p : α → Prop) (x y : α) (r : α → α → Prop) {β : α → Type v} {t : α} {s : (x : α) → β x}
```

消去规则表述为：

> 给定项 {lean}`s : (x : α) → β x` 以及任意项 {lean}`t : α`，我们有 {lean}`s t : β t`。

在 {lean}`p x` 具有类型 {lean}`Prop` 的情形下，如果把 {lean}`(x : α) → β x` 替换为 {lean}`∀ x : α, p x`，就可以把这些规则读作构造涉及全称量词之证明的正确规则。

:::setup
```
variable {α : Type u} {β : Type v} {p : {x : α} → Prop} (q : Prop)
```
因此，构造演算以这种方式把依赖箭头类型与全称表达式等同起来。如果 {lean}`p` 是任意表达式，{lean}`∀ x : α, p` 只不过是 {lean}`(x : α) → p` 的另一种记法；当 {lean}`p` 是命题时，前一种记法通常比后一种更自然。典型地，表达式 {lean}`p` 会依赖于 {leanRef}`x : α`。回忆普通函数空间的情形：我们可以把 {lean}`α → β` 解释为 {lean}`(x : α) → β` 的特殊情形，其中 {lean}`β` 不依赖于 {leanRef}`x`。类似地，命题之间的蕴含 {lean}`p → q` 可看作 {lean}`∀ x : p, q` 的特殊情形，其中表达式 {lean}`q` 不依赖于 {leanRef}`x`。
:::

下面的例子展示了 {tech}[propositions-as-types] 对应如何在实践中使用。

```lean
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

作为记号约定，我们赋予全称量词尽可能大的作用域，因此在上面的例子中需要用括号把对 {leanRef}`x` 的量化限制在假设内。证明 {lean}`∀ y : α, p y` 的标准方式是取任意的 {leanRef}`y`，然后证明 {leanRef}`p y`。这就是引入规则。现在，既然 {leanRef}`h` 的类型是 {leanRef}`∀ x : α, p x ∧ q x`，表达式 {leanRef}`h y` 的类型就是 {leanRef}`p`{lit}` `{leanRef}`y`{lit}`  ∧  `{leanRef}`q`{lit}` `{leanRef}`y`。这就是消去规则。取左合取项便得到所需结论 {leanRef}`p y`。

:::setup
```
variable {x z : α}
```

记住，只差一个绑定变量重命名的表达式被视为等价。因此，例如我们可以在假设和结论中都使用同一个变量 {lean}`x`，而在证明中用另一个变量 {lean}`z` 来实例化它：
:::

```lean
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

再举一例，下面说明如何表达关系 {lean}`r` 具有传递性这一事实：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- trans_r : ∀ (x y z : α), r x y → r y z → r x z

#check trans_r a b c -- trans_r a b c : r a b → r b c → r a c

#check trans_r a b c hab -- trans_r a b c hab : r b c → r a c

#check trans_r a b c hab hbc -- trans_r a b c hab hbc : r a c
```

思考这里发生了什么。当我们在值 {leanRef}`a b c` 处实例化 {leanRef}`trans_r` 时，最终得到 {leanRef}`r`{lit}` `{leanRef}`a b`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的一个证明。把它应用到“假设”{leanRef}`hab : r a b`，我们得到蕴含 {leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的一个证明。最后，把它应用到假设 {leanRef}`hbc`，便得到结论 {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。

在这种情形中，如果参数 {leanRef}`a b c` 可以由 {leanRef}`hab hbc` 推断出来，那么显式提供它们会显得繁琐。因此，通常把这些参数设为隐式参数：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r

#check trans_r hab

#check trans_r hab hbc
```

其优点是，我们可以直接把 {leanRef}`trans_r hab hbc` 写作 {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。缺点是，对于表达式 {leanRef}`trans_r` 和 {leanRef}`trans_r hab`，Lean 没有足够的信息来推断参数的类型。第一个 {kw}`#check` 命令的输出是 {lit}`r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3`，这表明在此情形中隐式参数尚未指定。

下面的例子说明如何用一个等价关系进行基本推理：

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

为了熟悉全称量词的用法，你应当尝试本节末尾的一些练习。

:::setup
```
universe i j
variable (α : Sort i) (β : {x : α} → Sort j) {x : α}
```

正是依赖箭头类型，尤其是全称量词的类型规则，将 {lean}`Prop` 与其他类型区分开来。假设有 {lean}`α : Sort i` 和 {lean}`β : Sort j`，其中表达式 {lean}`β` 可以依赖于变量 {lean}`x : α`。那么 {lean}`(x : α) → β` 是 {lean}`Sort (imax i j)` 的元素；这里若 {lit}`j` 不是 {lit}`0`，则 {lit}`imax i j` 是 {lit}`i` 与 {lit}`j` 的最大值，否则为 {lit}`0`。

其思想如下。如果 {lit}`j` 不是 {lit}`0`，那么 {lean}`(x : α) → β` 是 {lean}`Sort (max i j)` 的元素。换言之，从 {lean}`α` 到 {lean}`β` 的依赖函数类型“位于”下标为 {lit}`i` 与 {lit}`j` 最大值的宇宙中。然而，若 {lean}`β` 属于 {lean}`Sort 0`，即是 {lean}`Prop` 的元素，那么无论 {lean}`α` 位于哪个类型宇宙，{lean}`(x : α) → β` 也都是 {lean}`Sort 0` 的元素。换言之，如果 {lean}`β` 是依赖于 {lean}`α` 的命题，那么 {lean}`∀ x : α, β` 仍然是命题。这反映了把 {lean}`Prop` 解释为命题而非数据的类型，也正是它使 {lean}`Prop` 成为 {deftech}_impredicative_。

术语“{deftech}[predicative]”源自二十世纪之交的基础研究。当时，Poincaré 和 Russell 等逻辑学家把集合论悖论归咎于一种“恶性循环”：我们通过对一个包含待定义性质本身的集合进行量化来定义某个性质。注意，如果 {lean}`α` 是任意类型，我们可以形成 {lean}`α` 上所有谓词的类型 {lean}`α → Prop`（即“{lean}`α` 的幂类型”）。{lean}`Prop` 的非谓性意味着，我们可以形成对 {lean}`α → Prop` 量化的命题。特别地，我们可以通过对 {lean}`α` 上所有谓词量化来定义 {lean}`α` 上的谓词；这正是曾经被认为有问题的那种循环性。
:::

# 等式
%%%
tag := "equality"
%%%

现在转向 Lean 库中定义的最基本关系之一，即等式关系。在关于 {ref "inductive-types"}[归纳类型] 的章节中，我们将解释等式是_如何_由 Lean 逻辑框架的基本构件定义出来的。这里则先说明如何使用它。

当然，等式的一个基本性质是它构成等价关系：

```lean
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a

#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a

#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

可以告诉 Lean 不要插入隐式参数（这里显示为元变量），从而使输出更易读。

```lean
universe u

#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a

#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a

#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

标记 {lit}`.{u}` 告诉 Lean 在宇宙 {lit}`u` 处实例化这些常量。

因此，例如我们可以把上一节的例子特化到等式关系：

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

我们也可以使用投影记法：

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
------
example : a = d := (hab.trans hcb.symm).trans hcd
```

自反性比表面看起来更强大。回忆一下，构造演算中的项具有计算解释，而逻辑框架把具有共同约化结果的项视为相同。因此，一些非平凡恒等式可以由自反性证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

该框架的这一特性非常重要，因此库为 {lean}`Eq.refl _` 定义了记法 {lean}`rfl`：

```lean
variable (α β : Type)
------
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

:::setup
```
variable {a b : α} {p : α → Prop} {h1 : a = b} {h2 : p a}
```

然而，等式远不只是等价关系。它还具有一个重要性质：每个断言都尊重这种等价；也就是说，我们可以替换相等的表达式而不改变真值。换言之，给定 {lean}`h1 : a = b` 和 {lean}`h2 : p a`，我们可以通过替换构造 {lean}`p b` 的证明：{lean}`Eq.subst h1 h2`。
:::

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

第二种写法中的三角符号是在 {lean}`Eq.subst` 和 {lean}`Eq.symm` 之上构建的宏；可以通过输入 {kbd}`\t` 得到它。

规则 {lean}`Eq.subst` 用于定义以下辅助规则，它们执行更显式的替换。这些规则设计用来处理应用项，即形如 {lean}`s t` 的项。具体地说，{lean}`congrArg` 可用于替换参数，{lean}`congrFun` 可用于替换被应用的项，而 {lean}`congr` 可同时替换二者。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Lean 的库包含大量常用恒等式，例如：

```lean
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

注意，{lean}`Nat.mul_add` 和 {lean}`Nat.add_mul` 分别是 {lean}`Nat.left_distrib` 与 {lean}`Nat.right_distrib` 的别名。上述性质是针对自然数（类型 {lean}`Nat`）陈述的。

下面是一个自然数计算的例子，它结合使用替换、结合律和分配律。

```lean
example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

:::setup
```
variable {α : Type u}
```

```lean (show := false)
example {α : Type u} {x y : α} {h : x = y} {p : α → Prop} {e : p x} : p y := h ▸ e
```


注意，{lean}`Eq.subst` 的第二个隐式参数给出了要发生替换的上下文，其类型为 {lean}`α → Prop`。因此，推断这个谓词需要一个_高阶合一_实例。在完全一般的情形下，判定是否存在高阶合一子是不可判定的，Lean 最多只能为该问题提供不完美的近似解。因此，{lean}`Eq.subst` 并不总能按你的期望工作。宏 {leanRef}`h ▸ e` 使用更有效的启发式方法来计算这个隐式参数，常常能在直接应用 {lean}`Eq.subst` 失败的情况下成功。

:::

由于等式推理非常常见且重要，Lean 提供了若干机制来更有效地进行等式推理。下一节给出一种语法，使你能够以更自然、更清晰的方式书写计算式证明。更重要的是，等式推理由项重写器、化简器以及其他自动化机制支持。项重写器和化简器将在下一节简要介绍，并在下一章更详细地讨论。

# 计算式证明
%%%
tag := "calculational-proofs"
%%%

计算式证明只是由一系列中间结果组成的链条，这些结果意在通过等式传递性等基本原则组合起来。在 Lean 中，计算式证明以关键字 {kw}`calc` 开始，并具有如下语法：

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

注意，{kw}`calc` 中的各个关系具有相同的缩进。每个 {lit}`<proof>_i` 都是 {lit}`<expr>_{i-1} op_i <expr>_i` 的证明。

我们也可以在第一个关系中（紧接 {lit}`<expr>_0` 之后）使用 {lit}`_`，这有助于对齐一串关系/证明对：

```
calc <expr>_0
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

下面是一个例子：

```lean
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

这种证明书写风格在与 {tactic}`simp` 和 {tactic}`rw` 策略结合使用时最为有效；这些策略将在下一章更详细地讨论。例如，使用 {tactic}`rw` 进行重写，上面的证明可以写成如下形式：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

本质上，{kw}`rw` 策略使用给定的等式（它可以是假设、定理名或复杂项）来“重写”目标。如果这样做把目标化为恒等式 {lean}`t = t`，该策略就应用自反性来证明它。

重写可以依次应用，因此上面的证明可以缩短为：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

甚至可以写成：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```


相比之下，{kw}`simp` 策略会反复应用给定恒等式，在项中任何适用位置、以任意顺序重写目标。它还会使用先前向系统声明的其他规则，并明智地应用交换律以避免循环。因此，我们也可以如下证明该定理：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

我们将在下一章讨论 {kw}`rw` 和 {kw}`simp` 的各种变体。

{kw}`calc` 命令可以为任何支持某种传递性的关系进行配置。它甚至可以组合不同的关系。

```lean
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

你可以通过添加 {lean}`Trans` 类型类的新实例，向 {kw}`calc` “教授”新的传递性定理。类型类稍后才会介绍，但下面的小例子展示了如何使用新的 {lean}`Trans` 实例扩展 {kw}`calc` 记法。

```lean
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..
```

上面的例子也表明，即使你的关系没有中缀记法，也可以使用 {kw}`calc`。Lean 已经包含整除性的标准 Unicode 记法（使用 {lit}`∣`，可输入为 {kbd}`\dvd` 或 {kbd}`\mid`），所以上例使用普通竖线以避免冲突。在实践中，这不是一个好主意，因为它可能与 {kw}`match`{lit}`  ...  `{kw}`with` 表达式中使用的 ASCII {lit}`|` 混淆。

借助 {kw}`calc`，我们可以把上一节中的证明写得更自然、更清晰。

```lean
variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [←Nat.add_assoc]
```

这里值得考虑另一种 {kw}`calc` 记法。当第一个表达式占用这么多空间时，在第一个关系中使用 {lit}`_` 会自然地对齐所有关系：

```lean
variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   :=
      by rw [←Nat.add_assoc]
```

这里 {lean}`Nat.add_assoc` 前的左箭头告诉重写器按相反方向使用该恒等式。（可以用 {kbd}`\l` 输入它，或使用 ASCII 等价形式 {lit}`<-`。）如果追求简洁，{tactic}`rw` 和 {tactic}`simp` 都可以独立完成这项工作：

```lean
variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

# 存在量词
%%%
tag := "the-existential-quantifier"
%%%

最后，考虑存在量词，它可以写作 {lean}`exists x : α, p x`，也可以写作 {lean}`∃ x : α, p x`。这两种写法实际上都是 Lean 库中定义的较长表达式 {lean}`Exists (fun x : α => p x)` 的便捷记法缩写。

如你现在应当预料到的那样，库同时包含引入规则和消去规则。引入规则很直接：要证明 {lean}`∃ x : α, p x`，只需给出一个合适的项 {lean}`t` 以及 {lean}`p t` 的证明。下面是一些例子：

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- @Exists.intro : ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p
```

:::setup
```
variable {t : α} {p : α → Prop} (h : p t)
```
当类型可由上下文明确时，可以用匿名构造子记法 {lean (type := "Exists (fun x : α => p x)")}`⟨t, h⟩` 表示 {lean}`Exists.intro t h`。
:::

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

:::setup
```
variable (p : α → Prop) (g : Nat → Nat → Nat) (hg : g 0 0 = 0)
```

注意，{lean}`Exists.intro` 有隐式参数：Lean 必须在结论 {lean}`∃ x, p x` 中推断谓词 {lean}`p : α → Prop`。这并非平凡之事。例如，如果有 {lean}`hg : g 0 0 = 0` 并写下 {lean}`Exists.intro 0 hg`，那么谓词 {lean}`p` 有许多可能取值，分别对应定理 {lean}`∃ x, g x x = x`、{lean}`∃ x, g x x = 0`、{lean}`∃ x, g x 0 = x` 等。Lean 利用上下文来推断哪一个是恰当的。下面的例子展示了这一点，其中我们把选项 {option}`pp.explicit` 设为 true，请求 Lean 的美化打印器显示隐式参数。
:::

```lean
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments

#print gex1

#print gex2

#print gex3

#print gex4
```

:::setup
```
variable (q : Prop) (α : Type u) (p : α → Prop) (w : α) (x : α)
```

可以把 {lean}`Exists.intro` 看作一种信息隐藏操作，因为它隐藏了断言主体的见证。存在量词的消去规则 {lean}`Exists.elim` 执行相反操作。它允许我们通过证明对于任意值 {lean}`w`，{lean}`q` 可由 {lean}`p w` 推出，从而由 {lean}`∃ x : α, p x` 证明命题 {lean}`q`。粗略地说，既然我们知道存在某个满足 {lean}`p x` 的 {lean}`x`，就可以给它取一个名字，比如 {lean}`w`。如果 {lean}`q` 不提到 {lean}`w`，那么证明 {lean}`q` 由 {lean}`p w` 推出，等价于证明 {lean}`q` 由任意这种 {lean}`x` 的存在推出。下面是一个例子：
:::

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

:::setup
```
variable {α : Type u} (p : α → Prop) {β : α → Type} (a : α) (h : p a) (h' : β a)
```

把存在量词消去规则与析取消去规则比较会有所帮助：断言 {lean}`∃ x : α, p x` 可以看作命题 {lean}`p a` 的“大析取”，其中 {lean}`a` 遍历 {lean}`α` 的所有元素。注意，匿名构造子记法 {leanRef}`⟨w, hw.right, hw.left⟩` 缩写了一个嵌套构造子应用；我们同样可以写成 {lit}`⟨`{leanRef}`w`{lit}`, ⟨`{leanRef}`hw.right`{lit}`, `{leanRef}`hw.left`{lit}`⟩⟩`。

注意，存在命题与依赖类型一节中描述的 Sigma 类型非常相似。区别在于，存在命题是_命题_，而 Sigma 类型是_类型_。除此之外，它们非常相似。给定谓词 {lean}`p : α → Prop` 和类型族 {lean}`β : α → Type`，对于项 {lean}`a : α` 以及 {lean}`h : p a`、{lean}`h' : β a`，项 {lean}`Exists.intro a h` 的类型是 {lean}`(∃ x : α, p x) : Prop`，而 {lean}`Sigma.mk a h'` 的类型是 {lean}`(Σ x : α, β x)`。{lit}`∃` 与 {lit}`Σ` 的相似性是 {tech}[Curry-Howard isomorphism] 的又一个实例。
:::

Lean 提供了利用 {kw}`match` 表达式从存在量词中消去的更便捷方式：

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

{kw}`match` 表达式是 Lean 函数定义系统的一部分，该系统为定义复杂函数提供了便捷而富有表达力的方式。再次，是 {tech}[Curry-Howard isomorphism] 使我们也能借用这一机制来书写证明。{kw}`match` 语句把存在断言“解构”为组成部分 {leanRef}`w` 和 {leanRef}`hw`，随后即可在语句主体中使用它们来证明命题。为了更清楚，我们可以标注匹配中使用的类型：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

我们甚至可以用 match 语句同时分解合取：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

Lean 还提供了模式匹配式的 {kw}`let` 表达式：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

这本质上只是上述 {kw}`match` 构造的另一种记法。Lean 甚至允许我们在 {kw}`fun` 表达式中使用隐式的 {kw}`match`：

```lean
variable (α : Type) (p q : α → Prop)
------
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

我们将在 {ref "induction-and-recursion"}[归纳与递归] 中看到，所有这些变体都是更一般的模式匹配构造的实例。

:::setup
```
def IsEven (a : Nat) := ∃ b, a = 2 * b
variable (a : Nat)
```

在下面的例子中，我们把 {lean}`IsEven a` 定义为 {lean}`∃ b, a = 2 * b`，然后证明两个偶数之和仍为偶数。
:::

```lean
def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
```

利用本章介绍的各种工具——match 语句、匿名构造子以及 {tactic}`rewrite` 策略——我们可以把这个证明简洁地写成：

```lean
def IsEven (a : Nat) := ∃ b, a = 2 * b
------
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

:::leanFirst
正如构造性的“或”强于经典的“或”一样，构造性的“存在”也强于经典的“存在”。例如，下面的蕴含需要经典推理，因为从构造主义观点看，知道并非每个 {leanRef}`x` 都满足 {leanRef}`¬ p`，并不等同于拥有某个满足 {leanRef}`p` 的具体 {leanRef}`x`。

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```
:::

下面是一些涉及存在量词的常见恒等式。在后面的练习中，我们鼓励你尽可能多地证明它们。我们也把判断哪些命题是非构造性的、因而需要某种经典推理这一任务留给你。

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

注意，第二个例子和最后两个例子需要假设类型 {leanRef}`α` 至少有一个元素 {leanRef}`a`。

下面给出其中两个较困难命题的解答：

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

# 证明语言补充
%%%
tag := "more-on-the-proof-language"
%%%

我们已经看到，{kw}`fun`、{kw}`have` 和 {kw}`show` 等关键字使我们能够书写形式化证明项，并使其反映非形式数学证明的结构。本节讨论证明语言中一些常用且方便的附加特性。

首先，可以使用匿名 {kw}`have` 表达式引入辅助目标，而无需为其命名。我们可以用关键字 {lit}`this` 引用最近以这种方式引入的表达式：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

证明常常从一个事实推进到下一个事实，因此这可以有效减少大量标签带来的杂乱。

当目标可以推断出来时，我们也可以写 {kw}`by assumption`，让 Lean 填入证明：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))
------
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

这会告诉 Lean 使用 {leanRef}`assumption` 策略；该策略会在局部上下文中寻找合适的假设来证明目标。下一章将进一步学习 {leanRef}`assumption` 策略。

:::setup
```
variable {p : Prop} (prf : p)
```
我们也可以写 {lean}`‹p›`，请求 Lean 填入证明；这里 {lean}`p` 是我们希望 Lean 在上下文中找到其证明的命题。可以分别用 {kbd}`\f<` 和 {kbd}`\f>` 输入这些角引号。字母 “f” 代表 “French”，因为这些 Unicode 符号也可用作法语引号。事实上，该记法在 Lean 中定义如下：
:::

```lean
notation "‹" p "›" => show p by assumption
```

这种方法比使用 {leanRef}`by assumption` 更稳健，因为需要推断的假设类型被显式给出。它也使证明更易读。下面是一个较详细的例子：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

请记住，可以用这种法语引号来引用上下文中的_任何_对象，而不仅限于匿名引入的对象。它的使用也不限于命题，尽管用它来引用数据多少有些奇怪：

```lean
example (n : Nat) : Nat := ‹Nat›
```

稍后，我们将展示如何使用 Lean 的宏系统扩展证明语言。

# 练习
%%%
tag := "quantifiers-and-equality-exercises"
%%%

1. 证明下列等价：

    ```lean
    variable (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
    ```

   你还应当尝试理解为什么最后一个例子的逆蕴含不可导出。

2. 当公式的某个组成部分不依赖于被量化变量时，通常可以把它移到全称量词之外。尝试证明下列命题（其中第二个命题的一个方向需要经典逻辑）：

    ```lean
    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : α → ((∀ x : α, r) ↔ r) := sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
    ```

3. 考虑“理发师悖论”：某个城镇中有一位（男性）理发师，他给且只给那些不给自己刮胡子的人刮胡子。证明这会导致矛盾：

    ```lean
    variable (men : Type) (barber : men)
    variable (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
      sorry
    ```

4. ::::setup
   ```
   variable {n : Nat}
   ```
   :::leanFirst
   记住，在没有任何参数的情况下，类型为 {lean}`Prop` 的表达式就是一个断言。补全下面的 {leanRef}`prime` 和 {leanRef}`Fermat_prime` 定义，并构造给出的每个断言。例如，可以通过断言对每个自然数 {lean}`n`，都存在一个大于 {lean}`n` 的素数，来表达“存在无限多个素数”。Goldbach 弱猜想断言，每个大于 5 的奇数都是三个素数之和。如有必要，请查阅 Fermat 素数或其他陈述的定义。

    ```lean
    def even (n : Nat) : Prop := sorry

    def prime (n : Nat) : Prop := sorry

    def infinitely_many_primes : Prop := sorry

    def Fermat_prime (n : Nat) : Prop := sorry

    def infinitely_many_Fermat_primes : Prop := sorry

    def goldbach_conjecture : Prop := sorry

    def Goldbach's_weak_conjecture : Prop := sorry

    def Fermat's_last_theorem : Prop := sorry
    ```
   :::
   ::::

5. 尽可能多地证明“存在量词”一节中列出的恒等式。
