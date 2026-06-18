import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "转换策略模式" =>
%%%
tag := "conv"
file := "The-Conversion-Tactic-Mode"
%%%

在策略块中，可以使用关键字 {tactic}`conv` 进入
_转换模式_。该模式允许在假设和目标的内部移动，
甚至可以进入函数抽象和依值箭头的内部，以应用重写或
化简步骤。

# 基本导航与重写
%%%
tag := "basic-navigation-and-rewriting"
%%%

:::leanFirst
作为第一个例子，我们来证明
{leanRef}`(a b c : Nat) : a * (b * c) = a * (c * b)`
这个例子（本文件中的例子都有些人为构造，因为
其他策略可以立即完成它们）。朴素的
首次尝试是进入策略模式并尝试 {leanRef}`rw [Nat.mul_comm]`。但这会
交换项中出现的第一个乘法，从而把目标变为
{leanRef}`b * c * a = a * (c * b)`。有几种
方法可以修正这个问题，其中一种是使用更精确的工具：
转换模式。下面的代码块展示了每一行之后的当前目标。

```lean (showProofStates := "oops conv1 conv2 conv3 conv4")
#guard_msgs (drop all) in
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm]
  -- ^ PROOF_STATE: oops

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
--  ^ PROOF_STATE: conv1
    lhs
--  ^ PROOF_STATE: conv2
    congr
--  ^ PROOF_STATE: conv3
    rfl
--  ^ PROOF_STATE: conv4
    rw [Nat.mul_comm]
```
:::

上面的片段展示了三个导航命令：

- {leanRef}`lhs` 导航到关系的左侧（在这里是等式）。
   也有一个 {tactic}`rhs` 用来导航到右侧。
- {leanRef}`congr` 会按照当前头函数的（非依值且显式的）参数数量创建相应数量的目标
  （这里的头函数是乘法）。
- {leanRef}`rfl` 使用自反性关闭目标。

一旦到达相关目标，就可以像在普通
策略模式中那样使用 {leanRef}`rw`。

:::leanFirst
使用转换模式的第二个主要原因是在
绑定器下进行重写。假设我们想证明例子
{leanRef}`(fun x : Nat => 0 + x) = (fun x => x)`。
朴素的首次尝试是进入策略模式并尝试
{leanRef}`rw [Nat.zero_add]`。但这会失败，并给出令人沮丧的

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

解决方法是：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) :=  by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```
:::

其中 {leanRef}`intro x` 是进入 {kw}`fun` 绑定器内部的导航命令。
注意，这个例子有些人为构造，也可以这样做：

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

或者直接

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

{leanRef}`conv` 也可以使用 {kw}`conv at`{lit}` h` 来重写局部上下文中的假设 {lit}`h`。

# 模式匹配
%%%
tag := "pattern-matching-conv"
%%%

使用上述命令进行导航可能会很繁琐。可以如下使用模式匹配作为捷径：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]
```

这只是以下写法的语法糖：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

当然，也允许使用通配符：

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

# 组织转换策略
%%%
tag := "structuring-conversion-tactics"
%%%

在 {lit}`conv` 模式中，也可以使用花括号和 {lit}`.` 来组织策略：

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

# 转换模式中的其他策略
%%%
tag := "other-tactics-inside-conversion-mode"
%%%

- :::leanFirst
  {leanRef}`arg`{lit}` i` 进入应用的第 {lit}`i` 个非依值显式参数。

  ```lean (showProofStates := "arg2 arg3")
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv =>
    -- ^ PROOF_STATE: arg1
      lhs
    -- ^ PROOF_STATE: arg2
      arg 2
    -- ^ PROOF_STATE: arg3
      rw [Nat.mul_comm]
  ```
  :::

- {tactic}`args` 是 {leanRef}`congr` 的另一个名称。

-   {leanRef}`simp` 将化简器应用于当前目标。它支持普通策略模式中可用的相同选项。

    ```lean
    def f (x : Nat) :=
      if x > 0 then x + 1 else x + 2

    example (g : Nat → Nat)
        (h₁ : g x = x + 1) (h₂ : x > 0) :
        g x = f x := by
      conv =>
        rhs
        simp [f, h₂]
      exact h₁
    ```

- {kw}`enter`{lit}` [1, x, 2, y]` 用给定的参数依次执行 {leanRef}`arg` 和 {leanRef}`intro`。

- {tactic}`done` 会在存在未解决目标时失败。

- {tactic}`trace_state` 显示当前策略状态。

- {tactic}`whnf` 将项置于弱头范式。

- {kw}`tactic`{lit}` => <tactic sequence>` 返回普通策略模式。这
  对于解决 {leanRef}`conv` 模式不支持的目标，以及
  应用自定义的同余性和外延性引理很有用。

  ```lean (showProofStates := "convTac1 convTac2 convTac4")
  example (g : Nat → Nat → Nat)
          (h₁ : ∀ x, x ≠ 0 → g x x = 1)
          (h₂ : x ≠ 0)
          : g x x + x = 1 + x := by
    conv =>
      lhs
  --  ^    PROOF_STATE: convTac1
      arg 1
  --  ^    PROOF_STATE: convTac2
      rw [h₁]
      . skip
      . tactic =>
    --  ^    PROOF_STATE: convTac4
         exact h₂
  ```

- {kw}`apply`{lit}` <term>` 是 {kw}`tactic`{lit}` => apply <term>` 的语法糖。

  ```lean
  example (g : Nat → Nat → Nat)
          (h₁ : ∀ x, x ≠ 0 → g x x = 1)
          (h₂ : x ≠ 0)
          : g x x + x = 1 + x := by
    conv =>
      lhs
      arg 1
      rw [h₁]
      . skip
      . apply h₂
  ```
