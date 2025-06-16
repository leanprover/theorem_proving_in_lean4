import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "Induction and Recursion" =>
%%%
tag := "induction-and-recursion"
%%%

In the previous chapter, we saw that inductive definitions provide a
powerful means of introducing new types in Lean. Moreover, the
constructors and the recursors provide the only means of defining
functions on these types. By the {tech}[propositions-as-types] correspondence,
this means that induction is the fundamental method of proof.

Lean provides natural ways of defining recursive functions, performing
pattern matching, and writing inductive proofs. It allows you to
define a function by specifying equations that it should satisfy, and
it allows you to prove a theorem by specifying how to handle various
cases that can arise. Behind the scenes, these descriptions are
“compiled” down to primitive recursors, using a procedure that we
refer to as the “equation compiler.” The equation compiler is not part
of the trusted code base; its output consists of terms that are
checked independently by the kernel.

# Pattern Matching
%%%
tag := "pattern-matching"
%%%

The interpretation of schematic patterns is the first step of the
compilation process. We have seen that the {lit}`casesOn` recursor can
be used to define functions and prove theorems by cases, according to
the constructors involved in an inductively defined type. But
complicated definitions may use several nested {lit}`casesOn`
applications, and may be hard to read and understand. Pattern matching
provides an approach that is more convenient, and familiar to users of
functional programming languages.

:::setup
````
open Nat
variable (x : Nat)
````

Consider the inductively defined type of natural numbers. Every
natural number is either {lean}`zero` or {lean}`succ x`, and so you can define
a function from the natural numbers to an arbitrary type by specifying
a value in each of those cases:
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

The equations used to define these functions hold definitionally:

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

Instead of {leanRef}`zero` and {leanRef}`succ`, we can use more familiar notation:

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

Because addition and the zero notation have been assigned the
{attr}`[match_pattern]` attribute, they can be used in pattern matching. Lean
simply normalizes these expressions until the constructors {leanRef}`zero`
and {leanRef}`succ` are exposed.

Pattern matching works with any inductive type, such as products and option types:

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

Here we use it not only to define a function, but also to carry out a
proof by cases:

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

Pattern matching can also be used to destruct inductively defined propositions:

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

This provides a compact way of unpacking hypotheses that make use of logical connectives.

In all these examples, pattern matching was used to carry out a single
case distinction. More interestingly, patterns can involve nested
constructors, as in the following examples.

```lean
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
```

The equation compiler first splits on cases as to whether the input is
{leanRef}`zero` or of the form {leanRef}`succ x`.  It then does a case split on
whether {leanRef}`x` is of the form {leanRef}`zero` or {leanRef}`succ x`.  It determines
the necessary case splits from the patterns that are presented to it,
and raises an error if the patterns fail to exhaust the cases. Once
again, we can use arithmetic notation, as in the version below. In
either case, the defining equations hold definitionally.

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
````
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
````
You can write {leanCommand}`#print sub2` to see how the function was compiled to
recursors. (Lean will tell you that {leanRef}`sub2` has been defined in terms
of an internal auxiliary function, {lean}`sub2.match_1`, but you can print
that out too.) Lean uses these auxiliary functions to compile {kw}`match` expressions.
Actually, the definition above is expanded to
:::
```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0     => 0
    | 1     => 0
    | x + 2 => x
```

Here are some more examples of nested pattern matching:

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

The equation compiler can process multiple arguments sequentially. For
example, it would be more natural to define the previous example as a
function of two arguments:

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

Here is another example:

```lean
set_option linter.unusedVariables false
--------
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

Note that the patterns are separated by commas.

In each of the following examples, splitting occurs on only the first
argument, even though the others are included among the list of
patterns.

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

Notice also that, when the value of an argument is not needed in the
definition, you can use an underscore instead. This underscore is
known as a _wildcard pattern_, or an _anonymous variable_. In contrast
to usage outside the equation compiler, here the underscore does _not_
indicate an implicit argument. The use of underscores for wildcards is
common in functional programming languages, and so Lean adopts that
notation. {ref "wildcards-and-overlapping-patterns"}[Section Wildcards and Overlapping Patterns]
expands on the notion of a wildcard, and {ref "inaccessible-patterns"}[Section Inaccessible Patterns] explains how
you can use implicit arguments in patterns as well.

::::setup
````
set_option linter.unusedVariables false
--------
def tail : List α → List α
  | []      => []
  | a :: as => as
````

:::leanFirst
As described in {ref "inductive-types"}[Chapter Inductive Types],
inductive data types can depend on parameters. The following example defines
the {name}`tail` function using pattern matching. The argument {leanRef}`α : Type u`
is a parameter and occurs before the colon to indicate it does not participate in the pattern matching.
Lean also allows parameters to occur after the {leanRef}`:`, but pattern matching on them requires an explicit {leanRef}`match`.


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

Despite the different placement of the parameter {leanRef}`α` in these two
examples, in both cases it is treated in the same way, in that it does
not participate in a case split.

Lean can also handle more complex forms of pattern matching, in which
arguments to dependent types pose additional constraints on the
various cases. Such examples of _dependent pattern matching_ are
considered in the {ref "dependent-pattern-matching"}[Section Dependent Pattern Matching].

# Wildcards and Overlapping Patterns
%%%
tag := "wildcards-and-overlapping-patterns"
%%%

Consider one of the examples from the last section:

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

An alternative presentation is:

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

In the second presentation, the patterns overlap; for example, the
pair of arguments {lit}`0, 0` matches all three cases. But Lean handles
the ambiguity by using the first applicable equation, so in this example
the net result is the same. In particular, the following equations hold
definitionally:

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

Since the values of {leanRef (in:="m, n")}`m` and {leanRef (in:="m, n")}`n` are not needed, we can just as well use wildcard patterns instead.

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

You can check that this definition of {leanRef}`foo` satisfies the same
definitional identities as before.

:::setup
````
variable (α : Type u) (a : α)
````

Some functional programming languages support _incomplete
patterns_. In these languages, the interpreter produces an exception
or returns an arbitrary value for incomplete cases. We can simulate
the arbitrary value approach using the {lean}`Inhabited` type
class. Roughly, an element of {lean}`Inhabited α` is a witness to the fact
that there is an element of {lean}`α`; in the {ref "type-classes"}[Chapter Type Classes]
we will see that Lean can be instructed that suitable
base types are inhabited, and can automatically infer that other
constructed types are inhabited. On this basis, the
standard library provides a default element, {lean}`default`, of
any inhabited type.

We can also use the type {lean}`Option α` to simulate incomplete patterns.
The idea is to return {lean}`some a` for the provided patterns, and use
{lean (type:="Option α")}`none` for the incomplete cases. The following example demonstrates
both approaches.
:::

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

The equation compiler is clever. If you leave out any of the cases in
the following definition, the error message will let you know what has
not been covered.

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

It will also use an {kw}`if`{lit}`  ...  `{kw}`then`{lit}`  ...  `{kw}`else` instead of a {lit}`casesOn` in appropriate situations.

```lean
set_option pp.proofs true
-------
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

# Structural Recursion and Induction

What makes the equation compiler powerful is that it also supports
recursive definitions. In the next three sections, we will describe,
respectively:

- structurally recursive definitions
- well-founded recursive definitions
- mutually recursive definitions

Generally speaking, the equation compiler processes input of the following form:

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

Here {lit}`(a : α)` is a sequence of parameters, {lit}`(b : β)` is the
sequence of arguments on which pattern matching takes place, and {lit}`γ`
is any type, which can depend on {lit}`a` and {lit}`b`. Each line should
contain the same number of patterns, one for each element of {lit}`β`. As we
have seen, a pattern is either a variable, a constructor applied to
other patterns, or an expression that normalizes to something of that
form (where the non-constructors are marked with the {attr}`[match_pattern]`
attribute). The appearances of constructors prompt case splits, with
the arguments to the constructors represented by the given
variables. In {ref "dependent-pattern-matching"}[Section Dependent Pattern Matching],
we will see that it is sometimes necessary to include explicit terms in patterns that
are needed to make an expression type check, though they do not play a
role in pattern matching. These are called “inaccessible patterns” for
that reason. But we will not need to use such inaccessible patterns
before {ref "dependent-pattern-matching"}[Section Dependent Pattern Matching].

As we saw in the last section, the terms {lit}`t₁, ..., tₙ` can make use
of any of the parameters {lit}`a`, as well as any of the variables that
are introduced in the corresponding patterns. What makes recursion and
induction possible is that they can also involve recursive calls to
{lit}`foo`. In this section, we will deal with _structural recursion_, in
which the arguments to {lit}`foo` occurring on the right-hand side of the
{lit}`=>` are subterms of the patterns on the left-hand side. The idea is
that they are structurally smaller, and hence appear in the inductive
type at an earlier stage. Here are some examples of structural
recursion from the last chapter, now defined using the equation
compiler:

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

The proof of {leanRef}`zero_add` makes it clear that proof by induction is
really a form of recursion in Lean.

The example above shows that the defining equations for {leanRef}`add` hold
definitionally, and the same is true of {leanRef}`mul`. The equation compiler
tries to ensure that this holds whenever possible, as is the case with
straightforward structural induction. In other situations, however,
reductions hold only _propositionally_, which is to say, they are
equational theorems that must be applied explicitly. The equation
compiler generates such theorems internally. They are not meant to be
used directly by the user; rather, the {tactic}`simp` tactic
is configured to use them when necessary. The following
proof of {leanRef}`zero_add` works this way:

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

As with definition by pattern matching, parameters to a structural
recursion or induction may appear before the colon. Such parameters
are simply added to the local context before the definition is
processed. For example, the definition of addition may also be written
as follows:

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

You can also write the example above using {kw}`match`.

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

:::leanFirst
A more interesting example of structural recursion is given by the Fibonacci function {leanRef}`fib`.

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
````
variable (n : Nat)
open Nat
````

Here, the value of the {leanRef}`fib` function at {leanRef}`n + 2` (which is
definitionally equal to {lean}`succ (succ n)`) is defined in terms of the
values at {leanRef}`n + 1` (which is definitionally equivalent to {lean}`succ n`)
and the value at {leanRef}`n`. This is a notoriously inefficient way of
computing the Fibonacci function, however, with an execution time that
is exponential in {lean}`n`. Here is a better way:
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

Here is the same definition using a {kw}`let rec` instead of a {kw}`where`.

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

In both cases, Lean generates the auxiliary function {lit}`fibFast.loop`.

:::leanFirst
To handle structural recursion, the equation compiler uses
_course-of-values_ recursion, using constants {lit}`below` and {lit}`brecOn`
that are automatically generated with each inductively defined
type. You can get a sense of how it works by looking at the types of
{leanRef}`Nat.below` and {leanRef}`Nat.brecOn`:

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```
:::
:::setup
````
variable (C : Nat → Type u) (n : Nat)
````
The type {lean}`@Nat.below C (3 : Nat)` is a data structure that stores elements of {lean}`C 0`, {lean}`C 1`, and {lean}`C 2`.
The course-of-values recursion is implemented by {name}`Nat.brecOn`. It enables us to define the value of a dependent
function of type {lean}`(n : Nat) → C n` at a particular input {lean}`n` in terms of all the previous values of the function,
presented as an element of {lean}`@Nat.below C n`.
:::

:::leanFirst
The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to
the Lean kernel that a function terminates. It does not affect the code generator which compiles recursive
functions as other functional programming language compilers. Recall that {kw}`#eval`{lit}` ` {leanRef}`fib`{lit}` <n>` is exponential in {lit}`<n>`.
On the other hand, {kw}`#reduce`{lit}` `{leanRef}`fib`{lit}` <n>` is efficient because it uses the definition sent to the kernel that
is based on the {lit}`brecOn` construction.

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- Slow:
-- #eval fib 50
-- Fast:
#reduce fib 50

#print fib
```
:::

:::leanFirst
Another good example of a recursive definition is the list {leanRef}`append` function.

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```
:::

Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10] -- [5, 7, 9]
```

You are encouraged to experiment with similar examples in the exercises below.

# Local recursive declarations

You can define local recursive declarations using the {kw}`let rec` keyword.

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop -- @replicate.loop : {α : Type u_1} → α → Nat → List α → List α
```

Lean creates an auxiliary declaration for each {leanRef}`let rec`. In the example above,
it created the declaration {leanRef}`replicate.loop` for the {leanRef}`let rec loop` occurring at {leanRef}`replicate`.
Note that, Lean “closes” the declaration by adding any local variable occurring in the
{leanRef}`let rec` declaration as additional parameters. For example, the local variable {leanRef}`a` occurs
at {leanRef}`let rec loop`.


You can also use {leanRef}`let rec` in tactic mode and for creating proofs by induction.

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

You can also introduce auxiliary recursive declarations using {kw}`where` clause after your definition.
Lean converts them into a {kw}`let rec`.

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

# Well-Founded Recursion and Induction
%%%
tag := "well-founded-recursion-and-induction"
%%%

When structural recursion cannot be used, we can prove termination using well-founded recursion.
We need a well-founded relation and a proof that each recursive application is decreasing with respect to
this relation. Dependent type theory is powerful enough to encode and justify
well-founded recursion. Let us start with the logical background that
is needed to understand how it works.

:::setup
````
variable (α : Type u) (a : α) (r : α → α → Prop)
````

Lean's standard library defines two predicates, {lean}`Acc r a` and
{lean}`WellFounded r`, where {lean}`r` is a binary relation on a type {lean}`α`,
and {lean}`a` is an element of type {lean}`α`.
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


The first, {leanRef}`Acc`, is an inductively defined predicate. According to
its definition, {leanRef}`Acc r x` is equivalent to
{leanRef}`∀ y, r y x → Acc r y`. If you think of {leanRef}`r y x` as denoting a kind of order relation
{leanRef}`y ≺ x`, then {leanRef}`Acc r x` says that {leanRef}`x` is accessible from below,
in the sense that all its predecessors are accessible. In particular,
if {leanRef}`x` has no predecessors, it is accessible. Given any type {leanRef}`α`,
we should be able to assign a value to each accessible element of
{leanRef}`α`, recursively, by assigning values to all its predecessors first.



The statement that {leanRef}`r` is well-founded, denoted {leanRef}`WellFounded r`,
is exactly the statement that every element of the type is
accessible. By the above considerations, if {leanRef}`r` is a well-founded
relation on a type {leanRef}`α`, we should have a principle of well-founded
recursion on {leanRef}`α`, with respect to the relation {leanRef}`r`. And, indeed,
we do: the standard library defines {name}`WellFounded.fix`, which serves
exactly that purpose.

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

There is a long cast of characters here, but the first block we have
already seen: the type, {leanRef}`α`, the relation, {leanRef}`r`, and the
assumption, {leanRef}`h`, that {leanRef}`r` is well-founded. The variable {leanRef}`C`
represents the motive of the recursive definition: for each element
{leanRef}`x : α`, we would like to construct an element of {leanRef}`C x`. The
function {leanRef}`F` provides the inductive recipe for doing that: it tells
us how to construct an element {leanRef}`C x`, given elements of {leanRef}`C y` for
each predecessor {leanRef}`y` of {leanRef}`x`.

:::setup
````
variable {x y : α} (C : α → Sort v) (r : α → α → Prop)

````

Note that {name}`WellFounded.fix` works equally well as an induction
principle. It says that if {leanRef}`≺` is well-founded and you want to prove
{lean}`∀ x, C x`, it suffices to show that for an arbitrary {lean}`x`, if we
have {lean}`∀ y, r y x → C y`, then we have {lean}`C x`.
:::

In the example above we use the modifier {leanRef}`noncomputable` because the code
generator currently does not support {name}`WellFounded.fix`. The function
{name}`WellFounded.fix` is another tool Lean uses to justify that a function
terminates.

Lean knows that the usual order {lit}`<` on the natural numbers is well
founded. It also knows a number of ways of constructing new well
founded orders from others, for example, using lexicographic order.

Here is essentially the definition of division on the natural numbers that is found in the standard library.

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
Missing HL for example
:::
The definition is somewhat inscrutable. Here the recursion is on
{leanRef (in:="def div.F (x")}`x`, and {lit}`div.F x f : Nat → Nat` returns the “divide by {leanRef}`y`”
function for that fixed {leanRef (in:="def div.F (x")}`x`. You have to remember that the second
argument to {leanRef}`div.F`, the recipe for the recursion, is a function
that is supposed to return the divide by {leanRef}`y` function for all values
{leanRef}`x₁` smaller than {leanRef}`x`.

The elaborator is designed to make definitions like this more
convenient. It accepts the following:

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0
```

When Lean encounters a recursive definition, it first
tries structural recursion, and only when that fails, does it fall
back on well-founded recursion. Lean uses the tactic {tactic}`decreasing_tactic`
to show that the recursive applications are smaller. The auxiliary
proposition {leanRef}`x - y < x` in the example above should be viewed as a hint
for this tactic.

The defining equation for {leanRef}`div` does _not_ hold definitionally, but
we can unfold {leanRef}`div` using the {tactic}`unfold` tactic. We use {ref "conv"}[{tactic}`conv`] to select which
{leanRef}`div` application we want to unfold.

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
   -- unfold occurrence in the left-hand-side of the equation:
  conv => lhs; unfold div
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) :
    div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

:::leanFirst
The following example is similar: it converts any natural number to a
binary expression, represented as a list of 0's and 1's. We have to
provide evidence that the recursive call is
decreasing, which we do here with a {leanRef}`sorry`. The {leanRef}`sorry` does not
prevent the interpreter from evaluating the function successfully,
but {leanRef}`#eval!` must be used instead of {kw}`#eval` when a term contains {leanRef}`sorry`.

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
As a final example, we observe that Ackermann's function can be
defined directly, because it is justified by the well-foundedness of
the lexicographic order on the natural numbers. The {leanRef}`termination_by` clause
instructs Lean to use a lexicographic order. This clause is actually mapping
the function arguments to elements of type {lean}`Nat × Nat`. Then, Lean uses typeclass
resolution to synthesize an element of type {lean}`WellFoundedRelation (Nat × Nat)`.

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
```
:::

In many cases, Lean can automatically determine an appropriate lexicographical order.
Ackermann's function is one such case, so the {leanRef}`termination_by` clause is optional:

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
```

:::setup
````
variable {α : Type u} {β : Type v}
````

Note that a lexicographic order is used in the example above because the instance
{lean}`WellFoundedRelation (α × β)` uses a lexicographic order. Lean also defines the instance

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```
:::

:::leanFirst
In the following example, we prove termination by showing that {leanRef}`as.size - i` is decreasing
in the recursive application.

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
Note that, auxiliary function {leanRef}`go` is recursive in this example, but {leanRef}`takeWhile` is not.
Once again, Lean can automatically recognize this pattern, so the {leanRef}`termination_by` clause is unnecessary:
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
By default, Lean uses the tactic {tactic}`decreasing_tactic` to prove recursive applications are decreasing. The modifier {leanRef}`decreasing_by` allows us to provide our own tactic. Here is an example.

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

Note that {leanRef}`decreasing_by` is not replacement for {leanRef}`termination_by`, they complement each other. {leanRef}`termination_by` is used to specify a well-founded relation, and {leanRef}`decreasing_by` for providing our own tactic for showing recursive applications are decreasing. In the following example, we use both of them.

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
   -- unfolds well-founded recursion auxiliary definitions:
  all_goals simp_wf
  · apply Prod.Lex.left; simp +arith
  · apply Prod.Lex.right; simp +arith
  · apply Prod.Lex.left; simp +arith
```

:::leanFirst
We can use {leanRef}`decreasing_by sorry` to instruct Lean to “trust” us that the function terminates.

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
Recall that using {leanRef}`sorry` is equivalent to using a new axiom, and should be avoided. In the following example, we used the {leanRef}`sorry` to prove {leanRef}`False`.
The command {leanRef}`#print axioms unsound` shows that {leanRef}`unsound` depends on the unsound axiom {lean}`sorryAx` used to implement {leanRef}`sorry`.

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound -- 'unsound' depends on axioms: [sorryAx]
```
:::

:::setup
```
variable {α : Type w} {β  : Type u} {γ : Type v} {G : Prop}
```

Summary:

- If there is no {leanRef}`termination_by`, a well-founded relation is derived (if possible) by selecting an argument and then using typeclass resolution to synthesize a well-founded relation for this argument's type.

- If {leanRef}`termination_by` is specified, it maps the arguments of the function to a type {lean}`α` and type class resolution is again used. Recall that, the default instance for {lean}`β × γ` is a lexicographic order based on the well-founded relations for {lean}`β` and {lean}`γ`.

- The default well-founded relation instance for {lean}`Nat` is {lean type:="Nat → Nat → Prop"}`(· < ·)`.

- By default, the tactic {tactic}`decreasing_tactic` is used to show that recursive applications are smaller with respect to the selected well-founded relation. If {tactic}`decreasing_tactic` fails, the error message includes the remaining goal {lit}`... |- G`. Note that, the {tactic}`decreasing_tactic` uses {tactic}`assumption`. So, you can include a {kw}`have`-expression to prove goal {lean}`G`. You can also provide your own tactic using {kw}`decreasing_by`.
:::

# Functional Induction

Lean generates bespoke induction principles for recursive functions. These induction principles follow the recursive structure of the function's definition, rather than the structure of the datatype. Proofs about functions typically follow the recursive structure of the function itself, so these induction principles allow statements about the function to be proved more conveniently.

:::leanFirst
For example, using the functional induction principle for {leanRef}`ack` to prove that the result is always greater than {leanRef}`0` requires one case for each arm of the pattern match in {leanRef}`ack`:

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

In {goal case1}`case1`, the goal is:
````proofState case1
case case1 =>
  y: Nat
⊢ y + 1 > 0
````
The {leanRef}`y + 1` in the goal corresponds to the value returned in the first case of {leanRef}`ack`.

In {goal case2}`case2`, the goal is:
````proofState case2
case case2 =>
  x: Nat
  ih: ack x 1 > 0
⊢ ack x 1 > 0
````
The {leanRef}`ack x 1` in the goal corresponds to the value of {leanRef}`ack` applied to the pattern variables {leanRef}`x + 1` and {leanRef}`0` returned in the second case of {leanRef}`ack`.
This term is automatically simplified to the right-hand side.
Happily, the inductive hypothesis {leanRef}`ih : ack x 1 > 0` corresponds to the recursive call, which is exactly the answer returned in this case.

In {goal case3}`case3`, the goal is:
````proofState case3
case case3 =>
  x: Nat
  y: Nat
  ih1: ack (x + 1) y > 0
  ih2: ack x (ack (x + 1) y) > 0
⊢ ack x (ack (x + 1) y) > 0
````
The {leanRef}`ack x (ack (x + 1) y)` in the goal corresponds to the value returned in the third case of {leanRef}`ack`, when {leanRef}`ack` applied to {leanRef}`x + 1` and {leanRef}`y + 1` has been reduced.
The inductive hypotheses {leanRef}`ih1 : ack (x + 1) y > 0` and {leanRef}`ih2 : ack x (ack (x + 1) y) > 0` correspond to the recursive calls, with {leanRef}`ih1` matching the nested recursive call.
Once again, the induction hypothesis is suitable.

Using {leanRef}`fun_induction ack` results in goals and induction hypotheses that match the recursive structure of {leanRef}`ack`. As a result, the proof can be a single line:
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
There is also a {leanRef}`fun_cases` tactic which is analogous to the {tactic}`cases` tactic.
It generates a case for each branch in a function's control flow.
Both it and {leanRef}`fun_induction` additionally provide assumptions that rule out the paths that were not taken.

This function {leanRef}`f` represents a five-way Boolean disjunction:
```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x

```

To prove that it is disjunction, the last case requires knowledge that none of the arguments are {leanRef}`true`.
This knowledge is provided by the tactic:
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

Each case includes an assumption that rules out the prior cases:

```proofState fOrAll
case case1 =>
  b2: Bool
  b3: Bool
  b4: Bool
  b5: Bool
⊢ true = (true || b2 || b3 || b4 || b5)

case case2 =>
  b1: Bool
  b3: Bool
  b4: Bool
  b5: Bool
  x✝: b1 = true → False
⊢ true = (b1 || true || b3 || b4 || b5)

case case3 =>
  b1: Bool
  b2: Bool
  b4: Bool
  b5: Bool
  x✝¹: b1 = true → False
  x✝: b2 = true → False
⊢ true = (b1 || b2 || true || b4 || b5)

case case4 =>
  b1: Bool
  b2: Bool
  b3: Bool
  b5: Bool
  x✝²: b1 = true → False
  x✝¹: b2 = true → False
  x✝: b3 = true → False
⊢ true = (b1 || b2 || b3 || true || b5)

case case5 =>
  b1: Bool
  b2: Bool
  b3: Bool
  b4: Bool
  b5: Bool
  x✝³: b1 = true → False
  x✝²: b2 = true → False
  x✝¹: b3 = true → False
  x✝: b4 = true → False
⊢ b5 = (b1 || b2 || b3 || b4 || b5)
```

:::leanFirst
The {leanRef}`simp_all` tactic, which simplifies all the assumptions and the goal together, can dispatch all cases:
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


# Mutual Recursion

Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types. Here is an example:

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

What makes this a mutual definition is that {leanRef}`even` is defined recursively in terms of {leanRef}`odd`, while {leanRef}`odd` is defined recursively in terms of {leanRef}`even`. Under the hood, this is compiled as a single recursive definition. The internally defined function takes, as argument, an element of a sum type, either an input to {leanRef}`even`, or an input to {leanRef}`odd`. It then returns an output appropriate to the input. To define that function, Lean uses a suitable well-founded measure. The internals are meant to be hidden from users; the canonical way to make use of such definitions is to use {leanRef}`simp` (or {tactic}`unfold`), as we did above.

:::leanFirst
Mutual recursive definitions also provide natural ways of working with mutual and nested inductive types. Recall the definition of {leanRef}`Even` and {leanRef}`Odd` as mutual inductive predicates as presented before.

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
The constructors, {leanRef}`even_zero`, {leanRef}`even_succ`, and {leanRef}`odd_succ` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command {leanRef}`open Even Odd` allows us to access them more conveniently.

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

For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.

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
As a final example, we define a function {leanRef}`replaceConst a b e` that replaces a constant {leanRef in:="replaceConst a b e"}`a` with {leanRef in:="replaceConst a b e"}`b` in a term {leanRef in:="replaceConst a b e"}`e`, and then prove the number of constants is the same. Note that, our proof uses mutual recursion (aka induction).

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

# Dependent Pattern Matching
%%%
tag := "dependent-pattern-matching"
%%%


::::setup
````
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
````

:::leanFirst
All the examples of pattern matching we considered in
{ref "pattern-matching"}[Section Pattern Matching] can easily be written using {lit}`casesOn`
and {lit}`recOn`. However, this is often not the case with indexed
inductive families such as {leanRef}`Vect α n`, since case splits impose
constraints on the values of the indices. Without the equation
compiler, we would need a lot of boilerplate code to define very
simple functions such as {lean}`map`, {lean}`zip`, and {lean}`unzip` using
recursors. To understand the difficulty, consider what it would take
to define a function {lean}`tail` which takes a vector
{lean}`v : Vect α (n + 1)` and deletes the first element.

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::



A first thought might be to use the {name}`Vect.casesOn` function:

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


But what value should we return in the {name}`nil` case? Something funny
is going on: if {lean}`v` has type {lean}`Vect α (n + 1)`, it _can't_ be
{name}`nil`, but it is not clear how to tell that to {name}`Vect.casesOn`.

::::

One solution is to define an auxiliary function:

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

In the {leanRef}`nil` case, {leanRef in:="m = n + 1"}`m` is instantiated to {leanRef}`0`, and
{leanRef}`Nat.noConfusion` makes use of the fact that {leanRef}`0 = n + 1` cannot
occur.  Otherwise, {leanRef}`v` is of the form {lit}`cons `{leanRef}`a`{lit}` `{leanRef}`as`, and we can simply
return {leanRef}`as`, after casting it from a vector of length {leanRef in:="m + 1 = n + 1"}`m` to a
vector of length {leanRef in:="m + 1= n + 1"}`n`.

The difficulty in defining {leanRef}`tail` is to maintain the relationships between the indices.
The hypothesis {leanRef}`m = n + 1` in {leanRef}`tailAux` is used to communicate the relationship
between {leanRef (in:="m = n + 1")}`n` and the index associated with the minor premise.
Moreover, the {leanRef}`0 = n + 1` case is unreachable, and the canonical way to discard such
a case is to use {leanRef}`Nat.noConfusion`.

:::leanFirst
The {leanRef}`tail` function is, however, easy to define using recursive
equations, and the equation compiler generates all the boilerplate
code automatically for us. Here are a number of similar examples:

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

Note that we can omit recursive equations for “unreachable” cases such
as {leanRef}`head`{lit}` `{leanRef}`nil`. The automatically generated definitions for indexed
families are far from straightforward. For example:

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
````
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
````

The {leanRef}`zipWith` function is even more tedious to define by hand than the
{leanRef}`tail` function. We encourage you to try it, using {name}`Vect.recOn`,
{name}`Vect.casesOn` and {name}`Vect.noConfusion`.
:::

# Inaccessible Patterns
%%%
tag := "inaccessible-patterns"
%%%

Sometimes an argument in a dependent matching pattern is not essential
to the definition, but nonetheless has to be included to specialize
the type of the expression appropriately. Lean allows users to mark
such subterms as _inaccessible_ for pattern matching. These
annotations are essential, for example, when a term occurring in the
left-hand side is neither a variable nor a constructor application,
because these are not suitable targets for pattern matching. We can
view such inaccessible patterns as “don't care” components of the
patterns. You can declare a subterm inaccessible by writing
{lit}`.(t)`. If the inaccessible pattern can be inferred, you can also write
{lit}`_`.

:::leanFirst
The following example, we declare an inductive type that defines the
property of “being in the image of {leanRef in:="(f :"}`f`”. You can view an element of
the type {leanRef}`ImageOf f b` as evidence that {leanRef in:="ImageOf f b"}`b` is in the image of
{leanRef in:="ImageOf f b"}`f`, whereby the constructor {leanRef}`imf` is used to build such
evidence. We can then define any function {leanRef in:="inverse {f"}`f` with an “inverse”
which takes anything in the image of {leanRef in:="inverse {f"}`f` to an element that is
mapped to it. The typing rules forces us to write {leanRef in:=".(f a)"}`f a` for the
first argument, but this term is neither a variable nor a constructor
application, and plays no role in the pattern-matching definition. To
define the function {leanRef}`inverse` below, we _have to_ mark {leanRef in:=".(f a)"}`f a`
inaccessible.

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

In the example above, the inaccessible annotation makes it clear that
{leanRef in:=".(f a)"}`f` is _not_ a pattern matching variable.

:::leanFirst
Inaccessible patterns can be used to clarify and control definitions that
make use of dependent pattern matching. Consider the following
definition of the function {leanRef}`Vect.add`, which adds two vectors of
elements of a type, assuming that type has an associated addition
function:

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

def Vect.add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)
```
:::

The argument {leanRef}`{n : Nat}` appear after the colon, because it cannot
be held fixed throughout the definition.  When implementing this
definition, the equation compiler starts with a case distinction as to
whether the first argument is {leanRef}`0` or of the form {leanRef}`n+1`.  This is
followed by nested case splits on the next two arguments, and in each
case the equation compiler rules out the cases are not compatible with
the first pattern.

But, in fact, a case split is not required on the first argument; the
{lit}`casesOn` eliminator for {leanRef}`Vect` automatically abstracts this
argument and replaces it by {leanRef}`0` and {leanRef}`n + 1` when we do a case
split on the second argument. Using inaccessible patterns, we can prompt
the equation compiler to avoid the case split on {leanRef}`n`.

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

Marking the position as an inaccessible pattern tells the
equation compiler first, that the form of the argument should be
inferred from the constraints posed by the other arguments, and,
second, that the first argument should _not_ participate in pattern
matching.

The inaccessible pattern {leanRef}`.(_)` can be written as {lit}`_` for convenience.

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

As we mentioned above, the argument {leanRef}`{n : Nat}` is part of the
pattern matching, because it cannot be held fixed throughout the
definition. Rather than requiring that these discriminants be provided explicitly, Lean implicitly includes
these extra discriminants automatically for us.

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

When combined with the _auto bound implicits_ feature, you can simplify
the declare further and write:

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

Using these new features, you can write the other vector functions defined
in the previous sections more compactly as follows:

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

# Match Expressions

Lean also provides a compiler for {kw}`match`-{kw}`with` expressions found in
many functional languages:

```lean
set_option linter.unusedVariables false
------
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0     => false
  | n + 1 => true
```

This does not look very different from an ordinary pattern matching
definition, but the point is that a {kw}`match` can be used anywhere in
an expression, and with arbitrary arguments.

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

Here is another example:

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

Lean uses the {kw}`match` construct internally to implement pattern-matching in all parts of the system.
Thus, all four of these definitions have the same net effect:

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

These variations are equally useful for destructing propositions:

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

# Local Recursive Declarations

You can define local recursive declarations using the {kw}`let rec` keyword:

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop -- @replicate.loop : {α : Type u_1} → α → Nat → List α → List α
```

Lean creates an auxiliary declaration for each {leanRef}`let rec`. In the example above,
it created the declaration {leanRef}`replicate.loop` for the {leanRef}`let rec loop` occurring at {leanRef}`replicate`.
Note that, Lean “closes” the declaration by adding any local variable occurring in the
{leanRef}`let rec` declaration as additional parameters. For example, the local variable {leanRef}`a` occurs
at {leanRef}`let rec loop`.

You can also use {leanRef}`let rec` in tactic mode and for creating proofs by induction:

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

You can also introduce auxiliary recursive declarations using a {kw}`where` clause after your definition.
Lean converts them into a {leanRef}`let rec`:

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

# Exercises

```setup

open List

variable {xs : List α} {n : Nat}

```

1. Open a namespace {lit}`Hidden` to avoid naming conflicts, and use the
   equation compiler to define addition, multiplication, and
   exponentiation on the natural numbers. Then use the equation
   compiler to derive some of their basic properties.

2. Similarly, use the equation compiler to define some basic
   operations on lists (like the {lean}`reverse` function) and prove
   theorems about lists by induction (such as the fact that
   {lean}`reverse (reverse xs) = xs` for any list {lean}`xs`).

3. Define your own function to carry out course-of-value recursion on
   the natural numbers. Similarly, see if you can figure out how to
   define {name}`WellFounded.fix` on your own.

4. Following the examples in {ref "dependent-pattern-matching"}[Section Dependent Pattern Matching],
   define a function that will append two vectors.
   This is tricky; you will have to define an auxiliary function.

5.  :::leanFirst

    Consider the following type of arithmetic expressions. The idea is
    that {leanRef}`var`{lit}` `{lean}`n` is a variable, {lit}`vₙ`, and {leanRef}`const`{lit}` `{lean}`n` is the
    constant whose value is {lean}`n`.

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

    Here {leanRef}`sampleExpr` represents {lit}`(v₀ * 7) + (2 * v₁)`.

    :::leanFirst
    Write a function that evaluates such an expression, evaluating each {leanRef}`var n` to {leanRef}`v n`.

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

    -- Try it out. You should get 47 here.
    -- #eval eval sampleVal sampleExpr
    ```
    :::

    :::leanFirst
    Implement “constant fusion,” a procedure that simplifies subterms like
    {lean}`5 + 7` to {lean}`12`. Using the auxiliary function {leanRef}`simpConst`,
    define a function “fuse”: to simplify a plus or a times, first
    simplify the arguments recursively, and then apply {leanRef}`simpConst` to
    try to simplify the result.

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

    The last two theorems show that the definitions preserve the value.
