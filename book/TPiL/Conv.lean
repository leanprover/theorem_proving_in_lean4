import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "The Conversion Tactic Mode" =>
%%%
tag := "conv"
%%%

Inside a tactic block, one can use the keyword {tactic}`conv` to enter
_conversion mode_. This mode allows to travel inside assumptions and
goals, even inside function abstractions and dependent arrows, to apply rewriting or
simplifying steps.

# Basic navigation and rewriting

:::leanFirst
As a first example, let us prove example
{leanRef}`(a b c : Nat) : a * (b * c) = a * (c * b)`
(examples in this file are somewhat artificial since
other tactics could finish them immediately). The naive
first attempt is to enter tactic mode and try {leanRef}`rw [Nat.mul_comm]`. But this
transforms the goal into {leanRef}`b * c * a = a * (c * b)`, after commuting the
very first multiplication appearing in the term. There are several
ways to fix this issue, and one way is to use a more precise tool:
the conversion mode. The following code block shows the current target
after each line.

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

The above snippet shows three navigation commands:

- {leanRef}`lhs` navigates to the left-hand side of a relation (equality, in this case).
   There is also a {tactic}`rhs` to navigate to the right-hand side.
- {leanRef}`congr` creates as many targets as there are (nondependent and explicit) arguments to the current head function
  (here the head function is multiplication).
- {leanRef}`rfl` closes target using reflexivity.

Once arrived at the relevant target, we can use {leanRef}`rw` as in normal
tactic mode.

:::leanFirst
The second main reason to use conversion mode is to rewrite under
binders. Suppose we want to prove example
{leanRef}`(fun x : Nat => 0 + x) = (fun x => x)`.
The naive first attempt is to enter tactic mode and try
{leanRef}`rw [Nat.zero_add]`. But this fails with a frustrating

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

The solution is:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) :=  by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```
:::

where {leanRef}`intro x` is the navigation command entering inside the {kw}`fun` binder.
Note that this example is somewhat artificial, one could also do:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]
```

or just

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
```

{leanRef}`conv` can also rewrite a hypothesis {lit}`h` from the local context, using {kw}`conv at`{lit}` h`.

# Pattern matching

Navigation using the above commands can be tedious. One can shortcut it using pattern matching as follows:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]
```

which is just syntax sugar for

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    pattern b * c
    rw [Nat.mul_comm]
```

Of course, wildcards are allowed:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]
```

# Structuring conversion tactics

Curly brackets and {lit}`.` can also be used in {leanRef}`conv` mode to structure tactics:

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

# Other tactics inside conversion mode

- :::leanFirst
  {leanRef}`arg`{lit}` i` enter the {lit}`i`-th nondependent explicit argument of an application.

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

- {tactic}`args` is an alternative name for {leanRef}`congr`.

-   {leanRef}`simp` applies the simplifier to the current goal. It supports the same options available in regular tactic mode.

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

- {kw}`enter`{lit}` [1, x, 2, y]` iterate {leanRef}`arg` and {leanRef}`intro` with the given arguments.

- {tactic}`done` fail if there are unsolved goals.

- {tactic}`trace_state` display the current tactic state.

- {tactic}`whnf` put term in weak head normal form.

- {kw}`tactic`{lit}` => <tactic sequence>` go back to regular tactic mode. This
  is useful for discharging goals not supported by {leanRef}`conv` mode, and
  applying custom congruence and extensionality lemmas.

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

- {kw}`apply`{lit}` <term>` is syntax sugar for {kw}`tactic`{lit}` => apply <term>`.

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
