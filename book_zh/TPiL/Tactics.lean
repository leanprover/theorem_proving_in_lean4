import VersoManual
import TPiL.Examples

open Verso.Genre
open Manual hiding tactic
open TPiL

#doc (Manual) "策略" =>
%%%
tag := "tactics"
file := "Tactics"
%%%

本章介绍一种构造证明的替代方法：使用_策略_。证明项是数学证明的表示；策略则是描述如何构造这种证明的命令或指令。非形式地说，你可能会这样开始一个数学证明：“为了证明正向方向，展开定义，应用前面的引理，然后化简。”正如这些话是在告诉读者如何找到相应证明，策略也是告诉 Lean 如何构造证明项的指令。策略天然支持一种增量式的证明书写方式：将证明分解，并一次处理一个目标。

我们把由一系列策略组成的证明称为“策略式”证明，以区别于此前见过的证明项写法，后者称为“项式”证明。每种风格各有优缺点。例如，策略式证明可能更难阅读，因为读者需要预测或猜测每条指令的结果。但它们也可能更短、更容易书写。此外，策略提供了使用 Lean 自动化能力的入口，因为自动化过程本身也是策略。

# 进入策略模式
%%%
tag := "entering-tactic-mode"
%%%


:::leanFirst
从概念上说，陈述一个定理或引入一个 {kw}`have` 语句都会创建一个目标，即构造具有预期类型的项这一目标。例如，下面的代码在包含常量 {leanRef}`p q : Prop`、{leanRef}`hp : p` 和 {leanRef}`hq : q` 的上下文中，创建了构造类型为 {leanRef}`p ∧ q ∧ p` 的项这一目标：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  --                                   PROOF_STATE: X      ^
  sorry
```
:::

可以把这个目标写作如下形式：

```proofState X
p : Prop
q : Prop
hp : p
hq : q
⊢ p ∧ q ∧ p
```


事实上，如果把上例中的 “sorry” 替换为下划线，Lean 会报告说尚未解决的正是这个目标。

通常，你通过写出一个显式项来满足这样的目标。但在任何需要项的位置，Lean 都允许我们改为插入一个 {lit}`by <tactics>` 块，其中 {lit}`<tactics>` 是由分号或换行分隔的一系列命令。可以用这种方式证明上面的定理：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

我们经常把 {leanRef}`by` 关键字放在前一行，并把上面的例子写成：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
-- ^ PROOF_STATE: intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

{leanRef}`apply` 策略应用一个表达式，该表达式被看作表示一个带有零个或多个参数的函数。它把当前目标中的结论与该表达式进行合一，并为剩余参数创建新目标，前提是后续参数不依赖于这些参数。在上面的例子中，命令 {leanRef}`apply And.intro` 产生两个子目标：

```proofState intro
case left
p : Prop
q : Prop
hp : p
hq : q
⊢ p

case right
p : Prop
q : Prop
hp : p
hq : q
⊢ q ∧ p
```

第一个目标由命令 {leanRef}`exact hp` 解决。{leanRef}`exact` 命令只是 {leanRef}`apply` 的一个变体，它表明给定表达式应当精确填充目标。在策略证明中使用它是一种良好做法，因为它失败时意味着出现了问题。它也比 {leanRef}`apply` 更稳健，因为精化器在处理被应用的表达式时，会考虑由目标给出的预期类型。不过在此例中，{leanRef}`apply` 同样可以工作。

可以用 {kw}`#print` 命令查看得到的证明项：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
------
#print test
```

::: TODO
检查这些。Vim？
:::
可以增量地书写策略脚本。在 VS Code 中，可以按 {kbd}[`Ctrl` `Shift` `Enter`] 打开显示消息的窗口；当光标位于策略块中时，该窗口会显示当前目标。如果证明尚未完成，标记 {kw}`by` 会带有红色波浪线，错误消息中会包含剩余目标。

策略命令可以接受复合表达式，而不只是单个标识符。下面是前一个证明的较短版本：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

不出所料，它产生完全相同的证明项：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
 apply And.intro hp
 exact And.intro hq hp
------
#print test
```

多个策略应用可以用分号连接，写在同一行中。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

可能产生多个子目标的策略通常会给它们加上标签。例如，策略 {leanRef}`apply And.intro` 把第一个子目标标记为 {goal intro}`left`，把第二个标记为 {goal intro}`right`。对于 {leanRef}`apply` 策略而言，这些标签是从 {leanRef}`And.intro` 声明中所用参数名推断出来的。可以使用记法 {kw}`case`{lit}` <tag> => <tactics>` 来组织策略。下面是本章第一个策略证明的结构化版本。

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

:::leanFirst

可以使用 {leanRef}`case` 记法，在 {goal intro2}`left` 之前先解决子目标 {goal intro2}`right`：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  -- ^ PROOF_STATE: intro2
  case right =>
    apply And.intro
    case left => exact hq
  --          ^ PROOF_STATE: leftBranch
    case right => exact hp
  case left => exact hp
```
:::

注意，在 {leanRef}`case` 块内部，Lean 会隐藏其他目标。在 {leanRef}`case left =>` 之后，证明状态为：

```proofState leftBranch
p : Prop
q : Prop
hp : p
hq : q
⊢ q
```

我们说 {leanRef}`case` 正在“聚焦”所选目标。此外，如果在 {leanRef}`case` 块结束时所选目标尚未完全解决，Lean 会报告错误。

对于简单子目标，使用标签选择子目标也许不值得，但你可能仍希望组织证明结构。Lean 还提供“项目符号”记法 {lit}`. <tactics>`（或 {lit}`· <tactics>`）来组织证明：

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

# 基本策略
%%%
tag := "basic-tactics"
%%%

:::leanFirst
除 {leanRef}`apply` 和 {leanRef}`exact` 之外，另一个有用的策略是 {leanRef}`intro`，它用于引入假设。下面是前一章证明过的命题逻辑恒等式，现在用策略来证明。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```
:::

更一般地，{leanRef}`intro` 命令可用于引入任意类型的变量：

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

可以用它引入多个变量：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

:::setup
```
variable {α : Sort u} {p : Prop} {e : p}
```

正如 {leanRef}`apply` 策略是交互式构造函数应用的命令，{leanRef}`intro` 策略则是交互式构造函数抽象的命令（即形如 {lean (type := "∀ (x : α), p")}`fun x => e` 的项）。与 λ 抽象记法一样，{leanRef}`intro` 策略允许我们使用隐式的 {kw}`match`。
:::

```lean
example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

也可以像在 {kw}`match` 表达式中那样提供多个分支。

```lean
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

::::leanFirst
{leanRef}`intros` 策略可以不带任何参数使用；在这种情况下，它会选择名称并尽可能多地引入变量。稍后会看到一个例子。

:::leanFirst
{leanRef}`assumption` 策略会查看当前目标上下文中的假设；如果其中有一个与结论匹配，它就应用该假设。

```lean
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```
:::

必要时，它会对结论中的元变量进行合一：

```lean
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

下面的例子使用 {leanRef}`intros` 命令自动引入三个变量和两个假设：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```
::::

:::leanFirst
注意，Lean 自动生成的名称默认不可访问。这样做的动机是确保你的策略证明不依赖自动生成的名称，从而更加稳健。不过，可以使用组合子 {leanRef}`unhygienic` 来禁用这一限制。

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```
:::

:::leanFirst
还可以使用 {leanRef}`rename_i` 策略来重命名上下文中最近的不可访问名称。在下面的例子中，策略 {leanRef}`rename_i h1 _ h2` 重命名了上下文中最后三个假设中的两个。

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```
:::

:::leanFirst
{leanRef}`rfl` 策略解决那些把自反关系应用于定义相等参数的目标。等式是自反的：

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl
```
:::

:::leanFirst
{leanRef}`repeat` 组合子可用于多次应用一个策略：

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```
:::

:::leanFirst
另一个有时有用的策略是 {leanRef}`revert`；在某种意义上，它是 {leanRef}`intro` 的逆操作：

```lean
example (x : Nat) : x = x := by
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterRevertIntro
  rfl
```

在 {leanRef}`revert x` 之后，证明状态为：

```proofState afterRevert
⊢ ∀ (x : Nat), x = x
```

在 {leanRef}`intro y` 之后，证明状态为：

```proofState afterRevertIntro
y : Nat
⊢ y = y
```

:::

把一个假设移入目标会得到一个蕴含：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- ^ PROOF_STATE: afterRevertH
  intro h₁
  -- ^ PROOF_STATE: afterRevertHIntro
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

在 {leanRef}`revert h` 之后，证明状态为：

```proofState afterRevertH
x : Nat
y : Nat
⊢ x = y → y = x
```

在 {leanRef}`intro h₁` 之后，证明状态为：

```proofState afterRevertHIntro
x : Nat
y : Nat
h₁ : x = y
⊢ y = x
```

:::leanFirst
但 {leanRef}`revert` 更聪明：它不仅会还原上下文中的某个元素，还会同时还原上下文中所有位于其后的、依赖于它的元素。例如，在上面的例子中还原 {leanRef (in := "revert x")}`x` 时，会把 {leanRef}`h` 一并带上：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- ^ PROOF_STATE: afterRevertXH
  intros
  apply Eq.symm
  assumption
```

在 {leanRef}`revert x` 之后，目标为：

```proofState afterRevertXH
y : Nat
⊢ ∀ (x : Nat), x = y → y = x
```

:::

也可以一次还原上下文中的多个元素：

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- ^ PROOF_STATE: revertXY
  intros
  apply Eq.symm
  assumption
```

在 {leanRef}`revert x y` 之后，目标为：

```proofState revertXY
⊢ ∀ (x y : Nat), x = y → y = x
```

:::leanFirst
只能对局部上下文中的元素使用 {leanRef}`revert`，也就是局部变量或假设。但可以使用 {leanRef}`generalize` 策略，用一个新变量替换目标中的任意表达式：

```lean (showProofStates := "afterGen afterRevert afterIntro")
example : 3 = 3 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterIntro
  rfl
```

特别地，在 {leanRef}`generalize` 之后，目标为

```proofState afterGen
x : Nat
⊢ x = x
```

:::

上述记法的助记方式是：通过把 {leanRef}`3` 设为任意变量 {leanRef (in := "revert x")}`x` 来泛化目标。要小心：并非每次泛化都会保持目标的有效性。这里，{leanRef}`generalize` 把一个可用 {tactic}`rfl` 证明的目标替换成一个不可证明的目标：

```lean (showProofStates := "afterGen")
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  sorry
```

在这个例子中，{leanRef}`sorry` 策略类似于 {lean}`sorry` 证明项。它关闭当前目标，并产生通常的警告，说明使用了 {lean}`sorry`。为了保持原目标的有效性，{leanRef}`generalize` 策略允许我们记录 {leanRef}`3` 已被 {leanRef}`x` 替换这一事实。只需提供一个标签，{leanRef}`generalize` 就会用它把该赋值存入局部上下文：

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- ^ PROOF_STATE: afterGen
  rw [← h]
```

在 {leanRef}`generalize h : 3 = x` 之后，{leanRef}`h` 是 {leanRef}`3 = x` 的证明：

```proofState afterGen
x : Nat
h : 3 = x
⊢ 2 + x = 5
```

这里，重写策略 {leanRef}`rw` 使用 {leanRef}`h` 再次把 {leanRef}`x` 替换为 {leanRef}`3`。{leanRef}`rw` 策略将在下文讨论。

# 更多策略
%%%
tag := "more-tactics"
%%%

:::leanFirst
还有一些策略可用于构造和析构命题与数据。例如，当目标形如 {leanRef}`p ∨ q` 时，可以使用 {leanRef}`apply Or.inl` 和 {leanRef}`apply Or.inr` 等策略。反过来，{leanRef}`cases` 策略可用于分解析取：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```
:::

注意，其语法与 {kw}`match` 表达式中使用的语法类似。新的子目标可以按任意顺序解决：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

也可以使用不带 {leanRef}`with` 的（非结构化）{leanRef}`cases`，然后为每种情况给出策略：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

当可以用同一个策略关闭多个子目标时，（非结构化的）{leanRef}`cases` 尤其有用：

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

还可以使用组合子 {lit}`tac1 `{tactic}`<;>`{lit}` tac2`，把 {lit}`tac2` 应用于策略 {lit}`tac1` 产生的每个子目标：

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

:::leanFirst
可以把非结构化的 {leanRef}`cases` 策略与 {leanRef}`case` 和 {leanRef}`.` 记法结合使用：

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```
:::


{leanRef}`cases` 策略也可以用来分解合取：

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
  --             ^ PROOF_STATE: afterIntroCase
```


在这个例子中，应用 {leanRef}`cases` 策略之后只剩一个目标，其中 {leanRef}`h`{lit}`  :  `{leanRef}`p ∧ q` 被一对假设 {leanRef}`hp`{lit}`  :  `{leanRef}`p` 和 {leanRef}`hq`{lit}`  :  `{leanRef}`q` 取代：

```proofState afterIntroCase
case intro
p : Prop
q : Prop
hp : p
hq : q
⊢ q ∧ p
```

{leanRef}`constructor` 策略应用合取的唯一构造子 {lean}`And.intro`。

利用这些策略，上一节中的一个例子可以改写如下：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq =>
        constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr =>
        constructor; exact hp; apply Or.inr; exact hr
```

你将在 {ref "inductive-types"}[归纳类型] 中看到，这些策略相当一般。{leanRef}`cases` 策略可用于分解任意归纳定义类型的元素；{leanRef}`constructor` 总是应用归纳定义类型中第一个适用的构造子。例如，可以把 {leanRef}`cases` 和 {leanRef}`constructor` 用于存在量词：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

这里，{leanRef}`constructor` 策略把存在断言的第一个组成部分，即 {leanRef}`x` 的值，保留为隐式。它由一个元变量表示，稍后应被实例化。在前面的例子中，元变量的适当值由策略 {leanRef}`exact px` 决定，因为 {leanRef}`px` 的类型是 {leanRef}`p x`。如果想显式指定存在量词的见证，可以改用 {tactic}`exists` 策略：

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

下面是另一个例子：

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
```

这些策略既可用于命题，也同样可用于数据。在下一个例子中，它们被用来定义交换乘积类型和和类型分量的函数：

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

注意，除了我们为变量选择的名称之外，这些定义与合取和析取的类似命题证明完全相同。{leanRef}`cases` 策略还会对自然数进行分类讨论：

```lean
open Nat
example (P : Nat → Prop)
    (h₀ : P 0) (h₁ : ∀ n, P (succ n))
    (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

{leanRef}`cases` 策略及其配套的 {tactic}`induction` 策略将在 {ref "tactics-for-inductive-types"}[归纳类型的策略] 一节中更详细地讨论。

:::leanFirst
{leanRef}`contradiction` 策略会在当前目标的假设中搜索矛盾：

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```
:::

:::leanFirst
也可以在策略块中使用 {tactic}`match`。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ =>
      constructor; exact hp; apply Or.inr; exact hr
```
:::

:::leanFirst
可以把 {leanRef}`intro` 与 {tactic}`match` “结合”起来，把前面的例子写成如下形式：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ =>
      apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ =>
      apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption
```
:::

# 组织策略式证明
%%%
tag := "structuring-tactic-proofs"
%%%

策略常常提供一种高效构造证明的方式，但很长的指令序列可能会掩盖论证结构。本节介绍一些为策略式证明提供结构的方法，使此类证明更易读、更稳健。

:::leanFirst
Lean 的证明书写语法有一个优点：可以混合项式证明与策略式证明，并在二者之间自由切换。例如，策略 {leanRef}`apply` 和 {leanRef}`exact` 期望任意项，而这些项可以用 {kw}`have`、{kw}`show` 等书写。反过来，在书写任意 Lean 项时，也总能通过插入 {kw}`by` 块来调用策略模式。下面是一个略显玩具化的例子：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```
:::

下面是一个更自然的例子：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

:::leanFirst
事实上，有一个 {tactic}`show` 策略，它类似于证明项中的 {kw}`show` 表达式。它只是在保持策略模式的同时，声明即将被解决的目标类型。

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```
:::

{tactic}`show` 策略实际上可用于把目标改写为定义相等的形式：

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

还有一个 {tactic}`have` 策略，它像书写证明项时一样引入一个新的子目标：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

:::leanFirst
与证明项一样，可以在 {tactic}`have` 策略中省略标签；此时会使用默认标签 {leanRef}`this`：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```
:::

:::leanFirst
{tactic}`have` 策略中的类型也可以省略，因此可以写 {lit}`have hp := h.left` 和 {lit}`have hqr := h.right`。事实上，使用这种记法时，甚至可以同时省略类型和标签；此时新事实会以标签 {leanRef}`this` 引入：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```
:::

Lean 还有一个 {tactic}`let` 策略，它类似于 {tactic}`have` 策略，但用于引入局部定义，而不是辅助事实。它是证明项中 {kw}`let` 的策略对应物：

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

与 {tactic}`have` 一样，可以通过写 {lit}`let a := 3 * 2` 来省略类型。{tactic}`let` 与 {tactic}`have` 的区别在于，{tactic}`let` 在上下文中引入局部定义，因此该局部声明的定义可以在证明中展开。

我们已经使用 {leanRef}`.` 来创建嵌套策略块。在嵌套块中，Lean 聚焦于第一个目标；如果该目标在块结束时尚未完全解决，就会生成错误。这有助于标明由某个策略引入的多个子目标的各自证明。记法 {leanRef}`.` 对空白敏感，并依靠缩进判断策略块是否结束。另一种做法是使用花括号和分号定义策略块：

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

用缩进来组织证明很有用：每当一个策略留下多个子目标时，我们通过把剩余子目标放入块并缩进来区分它们。因此，如果把定理 {lit}`foo` 应用于单个目标产生四个子目标，证明通常应类似如下形式：

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

或者：

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

或者：

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

# 策略组合子
%%%
tag := "tactic-combinators"
%%%

_策略组合子_是由已有策略形成新策略的操作。{kw}`by` 块中已经隐含了一个顺序组合子：

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

这里，{leanRef}`apply Or.inl; assumption` 在功能上等价于一个单一策略：先应用 {leanRef}`apply Or.inl`，再应用 {leanRef}`assumption`。

在 {lit}`t₁ `{tactic}`<;>`{lit}` t₂` 中，{leanRef}`<;>` 运算符提供顺序操作的_并行_版本：先把 {lit}`t₁` 应用于当前目标，然后把 {lit}`t₂` 应用于产生的_所有_子目标：

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

当所得目标可以用统一方式完成，或者至少可以统一地在所有目标上取得进展时，这尤其有用。

{tactic}`first`{lit}` | t₁ | t₂ | ... | tₙ` 会依次应用每个 {lit}`tᵢ`，直到其中一个成功；如果都不成功，则失败：

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

在第一个例子中，左分支成功；而在第二个例子中，成功的是右分支。在接下来的三个例子中，同一个复合策略在每种情况下都成功：

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

该策略首先尝试用假设立即解决左侧析取项；如果失败，就尝试聚焦到右侧析取项；如果仍不可行，就调用 assumption 策略。

:::leanFirst
到现在你无疑已经注意到，策略可能失败。事实上，正是“失败”状态使 _first_ 组合子回溯并尝试下一个策略。{leanRef}`try` 组合子构造一个总是成功的策略，尽管它可能只是平凡地成功：{tactic}`try`{lit}` t` 执行 {lit}`t`，即使 {lit}`t` 失败也报告成功。它等价于 {tactic}`first`{lit}` | t | `{tactic}`skip`，其中 {tactic}`skip` 是一个什么也不做（并因此成功）的策略。在下一个例子中，第二个 {leanRef}`constructor` 在右侧合取项 {leanRef}`q ∧ r` 上成功（记住析取和合取向右结合），但在第一个目标上失败。{leanRef}`try` 策略确保顺序组合成功：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```
:::

要小心：{tactic}`repeat`{lit}` (`{tactic}`try`{lit}` t)` 会永远循环，因为内部策略永不失败。

在一个证明中，常常会有多个尚未解决的目标。并行顺序组合是一种安排单个策略应用于多个目标的方式，但还有其他方法。例如，{tactic}`all_goals`{lit}` t` 会把 {lit}`t` 应用于所有打开的目标：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

在这种情况下，{tactic}`any_goals` 策略提供了更稳健的解决方案。它类似于 {tactic}`all_goals`，不同之处在于：只要其参数在至少一个目标上成功，它就成功：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

下面 {kw}`by` 块中的第一个策略会反复拆分合取：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

事实上，可以把完整策略压缩成一行：

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

组合子 {tactic}`focus`{lit}` t` 确保 {lit}`t` 只影响当前目标，并暂时把其他目标从作用域中隐藏。因此，如果 {lit}`t` 通常只影响当前目标，那么 {tactic}`focus`{lit}` (`{tactic}`all_goals`{lit}` t)` 与 {lit}`t` 具有相同效果。

# 重写
%%%
tag := "rewriting"
%%%

{tactic}`rw` 策略和 {tactic}`simp` 策略已在 {ref "calculational-proofs"}[计算式证明] 中简要介绍。本节和下一节将更详细地讨论它们。

:::setup
```
variable (x y : α) (h : x = y)
theorem add_comm : ∀ (x y : Nat), x + y = y + x := by omega
```

{tactic}`rw` 策略提供了把替换应用于目标和假设的基本机制，从而为处理等式提供一种方便而高效的方式。该策略最基本的形式是 {tactic}`rw`{lit}` [t]`，其中 {lit}`t` 是一个类型断言某个等式的项。例如，{lit}`t` 可以是上下文中的假设 {lean}`h : x = y`；也可以是一般引理，如 {lean}`add_comm : ∀ x y, x + y = y + x`，此时重写策略会尝试为 {lean}`x` 和 {lean}`y` 寻找合适的实例；还可以是任何断言具体或一般等式的复合项。下面的例子中，我们使用这种基本形式，用一个假设来重写目标。

:::

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

:::setup
```
variable (t : α)
```

在上面的例子中，第一次使用 {leanRef}`rw` 会在目标 {leanRef}`f k = 0` 中把 {leanRef}`k` 替换为 {leanRef}`0`。随后第二次使用会把 {leanRef}`f 0` 替换为 {leanRef}`0`。该策略会自动关闭任何形如 {lean}`t = t` 的目标。下面是使用复合表达式进行重写的例子：
:::

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

这里，{leanRef}`h hq` 建立了等式 {leanRef}`x = y`。

多个重写可以用记法 {tactic}`rw`{lit}` [t_1, ..., t_n]` 组合；它只是 {tactic}`rw`{lit}` [t_1]; ...; `{tactic}`rw`{lit}` [t_n]` 的缩写。前一个例子可写成如下形式：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

默认情况下，{leanRef}`rw` 按正向使用等式：将左端与某个表达式匹配，并用右端替换它。记法 {lit}`←t` 可用于指示策略按反向使用等式 {lit}`t`。

```lean
variable (a b : Nat) (f : Nat → Nat)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

在这个例子中，项 {leanRef}`←h₁` 指示重写器把 {leanRef}`b` 替换为 {leanRef}`a`。在编辑器中，可以输入 {kbd}`\l` 得到反向箭头。也可以使用 ASCII 等价形式 {lit}`<-`。

有时，一个恒等式的左端可以匹配模式中的多个子项；此时 {tactic}`rw` 策略会选择遍历项时找到的第一个匹配。如果这不是你想要的匹配，可以使用额外参数来指定合适的子项。

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

:::TODO
把 `rw` 的中间证明状态加入引用环，以改进这些例子
:::

在上面的第一个例子中，第一步把 {leanRef}`a + b + c` 重写为 {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)`。下一步对项 {leanRef}`b + c` 应用交换律；如果不指定参数，策略反而会把 {leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)` 重写为 {lit}`(`{leanRef}`b + c`{lit}`) + `{leanRef}`a`。最后一步按反向应用结合律，把 {leanRef}`a`{lit}` + (`{leanRef}`c`{lit}`  +  `{leanRef}`b`{lit}`)` 重写为 {leanRef}`a + c + b`。接下来的两个例子则在两边应用结合律，把括号移到右侧，然后交换 {leanRef}`b` 与 {leanRef}`c`。注意，最后一个例子通过指定 {leanRef}`Nat.add_comm` 的第二个参数，说明重写应发生在右端。

默认情况下，{leanRef}`rw` 策略只影响目标。记法 {tactic}`rw`{lit}`  [t]  `{kw}`at`{lit}` h` 会把重写应用于假设：

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

第一步 {leanRef}`rw [Nat.add_zero] at h` 把假设 {leanRef}`a + 0 = 0` 重写为 {leanRef}`a = 0`。然后用新的假设 {leanRef}`a = 0` 把目标重写为 {leanRef}`f 0`{lit}`  =  `{leanRef}`f 0`。

:::leanFirst
{leanRef}`rw` 策略并不限于命题。在下面的例子中，我们使用 {tactic}`rw`{lit}`  [h]  `{kw}`at`{lit}` t`，把假设 {leanRef}`t : Tuple α n` 重写为 {leanRef}`t : Tuple α`{lit}` 0`。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```
:::

# 使用化简器
%%%
tag := "using-the-simplifier"
%%%

{tactic}`rw` 被设计为操纵目标的精细工具，而化简器则提供更强大的自动化形式。Lean 库中的许多恒等式都带有 {attr}`[simp]` 属性，{tactic}`simp` 策略会使用它们来迭代表达式中的子项。

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

在第一个例子中，目标中等式的左端使用涉及 0 和 1 的通常恒等式被化简，将目标化为 {leanRef}`x * y`{lit}`  =  `{leanRef}`x * y`。此时，{leanRef}`simp` 应用自反性完成证明。在第二个例子中，{leanRef}`simp` 把目标化为 {leanRef}`p (x * y)`，此时假设 {leanRef}`h` 完成证明。下面是一些关于列表的更多例子：

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

与 {leanRef}`rw` 一样，可以使用关键字 {leanRef}`at` 来化简一个假设：

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

此外，可以使用“通配符”星号来化简所有假设和目标：

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

:::setup
```
variable (x y z : Nat)
```

对于交换且结合的运算，例如自然数乘法，化简器会使用这两个事实来重写表达式，同时也使用_左交换律_。在乘法的情形中，后者表述为：{lean}`x * (y * z) = y * (x * z)`。{leanRef}`local` 修饰符告诉化简器在当前文件（或视情况在当前节、命名空间）中使用这些规则。交换律和左交换律看起来可能有问题，因为反复应用任一规则都会导致循环。但化简器会检测那些置换参数的恒等式，并使用一种称为_有序重写_的技术。这意味着系统维护项的内部次序，并且只有当应用恒等式会降低该次序时才应用它。对于上面提到的三个恒等式，其效果是表达式中的所有括号都向右结合，并且表达式以一种规范（尽管有些任意）的方式排序。于是，在结合律和交换律意义下等价的两个表达式会被重写为同一个规范形式。
:::

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
------
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

与 {tactic}`rw` 一样，可以向 {tactic}`simp` 传递一个事实列表供其使用，其中包括一般引理、局部假设、要展开的定义以及复合表达式。{tactic}`simp` 策略也识别 {tactic}`rewrite` 所识别的 {lit}`←t` 语法。无论如何，额外规则都会被加入用于化简项的恒等式集合中。

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

一个常见习惯用法是使用局部假设来化简目标：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

:::leanFirst
若要在化简时使用局部上下文中的所有假设，可以使用通配符 {leanRef}`*`：

```lean
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```
:::

下面是另一个例子：

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_comm]
```

:::leanFirst
化简器也会进行命题重写。例如，使用假设 {leanRef (in := "p ∧ q")}`p` 时，它会把 {leanRef}`p ∧ q` 重写为 {leanRef (in := "p ∨ q")}`q`，并把 {leanRef}`p ∨ q` 重写为 {lean}`True`，随后平凡地证明它。迭代这类重写会产生非平凡的命题推理。

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```
:::

下一个例子化简所有假设，然后用它们证明目标。

```lean
set_option linter.unusedVariables false
------
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

化简器尤其有用的一个原因是，它的能力会随着库的发展而增长。例如，假设我们定义一个列表操作，通过追加输入的反转来使其对称化：

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

:::leanFirst
那么对于任意列表 {leanRef (in := "mk_symm xs")}`xs`，{leanRef}`(mk_symm xs).reverse` 等于 {leanRef}`mk_symm xs`；这可以通过展开定义轻易证明：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```
:::

现在可以使用这个定理证明新的结果：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
       : (mk_symm xs).reverse = mk_symm xs := by
 simp [mk_symm]
------
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

但使用 {leanRef}`reverse_mk_symm` 通常是正确做法；如果用户不必显式调用它会更好。可以在定义该定理时把它标记为化简规则来实现这一点：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

记法 {leanRef}`@[simp]` 声明 {leanRef}`reverse_mk_symm` 具有 {attr}`[simp]` 属性，也可以更显式地写出：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

该属性也可以在定理声明后的任何时候应用：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

:::leanFirst
然而，一旦应用了该属性，就无法永久移除它；任何导入赋予该属性之文件的文件都会继承它。正如我们将在 {ref "attributes"}[属性] 中进一步讨论的，可以使用 {leanRef}`local` 修饰符将属性的作用域限制在当前文件或当前节中：

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```
:::

在该节之外，化简器默认不再使用 {leanRef}`reverse_mk_symm`。

注意，我们讨论过的各种 {leanRef}`simp` 选项——给出显式规则列表，以及使用 {leanRef}`at` 指定位置——可以组合使用，但它们列出的顺序是固定的。可以在编辑器中把光标放在 {leanRef}`simp` 标识符上，查看与之关联的文档字符串，从而看到正确顺序。

:::leanFirst
还有两个有用的附加修饰符。默认情况下，{leanRef}`simp` 包含所有标记了 {attr}`[simp]` 属性的定理。写作 {leanRef}`simp only` 会排除这些默认规则，使你可以使用更明确构造的规则列表。在下面的例子中，减号和 {leanRef}`only` 被用来阻止应用 {leanRef}`reverse_mk_symm`。

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```
:::

{leanRef}`simp` 策略有许多配置选项。例如，可以如下启用上下文化化简：

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual
```

使用 {leanRef}`+contextual` 时，{leanRef}`simp` 策略在化简 {leanRef}`y + x = y` 时会使用事实 {leanRef}`x = 0`，而在化简另一个分支时会使用 {leanRef}`x ≠ 0`。下面是另一个例子：

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual
```

:::leanFirst
另一个有用的配置选项是 {leanRef}`+arith`，它启用算术化简。

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith
```
:::

# split 策略
%%%
tag := "split-tactic"
%%%

::::leanFirst


{leanRef}`split` 策略对于按情况拆分嵌套的 {kw}`if`-{kw}`then`-{kw}`else` 和 {kw}`match` 表达式很有用。对于具有 $`n` 个情况的 {kw}`match` 表达式，{leanRef}`split` 策略最多生成 $`n` 个子目标。下面是一个例子：


```lean
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```
::::

可以把上面的策略证明压缩为如下形式。

```lean
def f (x y z : Nat) : Nat :=
 match x, y, z with
 | 5, _, _ => y
 | _, 5, _ => y
 | _, _, 5 => y
 | _, _, _ => 1
------
example (x y z : Nat) :
  x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w →
  f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

策略 {leanRef}`split <;> first | contradiction | rfl` 先应用 {leanRef}`split` 策略，然后对每个生成的目标尝试 {leanRef}`contradiction`；如果 {leanRef}`contradiction` 失败，再尝试 {leanRef}`rfl`。像 {leanRef}`simp` 一样，我们也可以把 {leanRef}`split` 应用于某个特定假设：

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, _] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h
```

# 可扩展策略
%%%
tag := "extensible-tactics"
%%%

:::leanFirst
在下面的例子中，我们使用命令 {leanRef}`syntax` 定义记法 {leanRef}`triv`。然后，使用命令 {leanRef}`macro_rules` 指定当使用 {leanRef}`triv` 时应执行什么操作。可以提供不同展开，策略解释器会逐一尝试，直到其中一个成功：

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```
:::

# 练习
%%%
tag := "tactics-exercises"
%%%

1. 回到 {ref "propositions-and-proofs"}[命题与证明] 和
{ref "quantifiers-and-equality"}[量词与等式] 中的练习，现在尽可能多地用策略证明重做，并在适当时也使用 {tactic}`rw`
和 {tactic}`simp`。

2. 使用策略组合子，为下面的命题给出一行证明：

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry
```
