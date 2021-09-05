The Conversion Tactic Mode
=========================

Inside a tactic block, one can use the keyword `conv` to enter
conversion mode. This mode allows to travel inside assumptions and
goals, even inside function abstractions and dependent arrows, to apply rewriting or
simplifying steps.

Basic navigation and rewriting
-------

As a first example, let us prove example
`(a b c : Nat) : a * (b * c) = a * (c * b)`
(examples in this file are somewhat artificial since
other tactics could finish them immediately). The naive
first attempt is to enter tactic mode and try `rw [Nat.mul_comm]`. But this
transforms the goal into `b * c * a = a * (c * b)`, after commuting the
very first multiplication appearing in the term. There are several
ways to fix this issue, and one way is to use a more precise tool :
the conversion mode. The following code block shows the current target
after each line.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- |- a * (b * c) = a * (c * b)
    lhs
    -- |- a * (b * c)
    congr
    -- 2 goals : |- a and |- b * c
    skip
    -- |- b * c
    rw [Nat.mul_comm]
```

The above snippet show three navigation commands:

- `lhs` navigates to the left hand side of a relation (here equality), there is also a `rhs` navigating to the right hand side.
- `congr` creates as many targets as there are (nondependent and explicit) arguments to the current head function
  (here the head function is multiplication).
- `skip` goes to the next target.

Once arrived at the relevant target, we can use `rw` as in normal
tactic mode.

The second main reason to use conversion mode is to rewrite under
binders. Suppose we want to prove example
`(fun x : Nat => 0 + x) = (fun x => x)`.
The naive first attempt is to enter tactic mode and try
`rw [zero_add]`. But this fails with a frustrating

```
error: tactic 'rewrite' failed, did not find instance of the pattern
       in the target expression
  0 + ?n
⊢ (fun x => 0 + x) = fun x => x
```

The solution is:

```lean
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]
```

where `intro x` is the navigation command entering inside the `fun` binder.
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

All this is also available to rewrite an hypothesis `h` from the local context using `conv at h`.

Pattern matching
-------

Navigation using the above commands can be tedious. One can shortcut it using pattern matching as follows:

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
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

Structuring conversion tactics
-------

Curly brackets and `.` can also be used in `conv` mode to structure tactics.

```lean
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]
```

Other tactics inside conversion mode
----------

- `arg i` enter the `i`-th nondependent explicit argument of an application.

```lean
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- |- a * (b * c) = a * (c * b)
    lhs
    -- |- a * (b * c)
    arg 2
    -- |- b * c
    rw [Nat.mul_comm]
```

- `args` alternative name for `congr`

- `simp` applies the simplifier to the current goal. It supports the same options available in regular tactic mode.

```lean
def f (x : Nat) :=
  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat) (h₁ : g x = x + 1) (h₂ : x > 0) : g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁
```

- `enter [1, x, 2, y]` iterate `arg` and `intro` with the given arguments. It is just the macro.

```
syntax enterArg := ident <|> num
syntax "enter " "[" (colGt enterArg),+ "]": conv
macro_rules
  | `(conv| enter [$i:numLit]) => `(conv| arg $i)
  | `(conv| enter [$id:ident]) => `(conv| ext $id)
  | `(conv| enter [$arg:enterArg, $args,*]) => `(conv| (enter [$arg]; enter [$args,*]))
```

- `done` fail if there are unsolved goals.

- `traceState` display the current tactic state.

- `whnf` put term in weak head normal form.

- `tactic => <tactic sequence>` go back to regular tactic mode. This
  is useful for discharging goals not supported by `conv` mode, and
  applying custom congruence and extensionality lemmas.

```lean
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    -- |- g x x + x
    arg 1
    -- |- g x x
    rw [h₁]
    -- 2 goals: |- 1, |- x ≠ 0
    . skip
    . tactic => exact h₂
```

- `apply <term>` is syntax sugar for `tactic => apply <term>`

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
