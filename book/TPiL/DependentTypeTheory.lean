import VersoManual

import TPiL.Examples

open TPiL

open Verso.Genre Manual

#doc (Manual) "Dependent Type Theory" =>
%%%
tag := "dependent-type-theory"
htmlSplit := .never
%%%

Dependent type theory is a powerful and expressive language, allowing
you to express complex mathematical assertions, write complex hardware
and software specifications, and reason about both of these in a
natural and uniform way. Lean is based on a version of dependent type
theory known as the _Calculus of Constructions_, with a countable
hierarchy of non-cumulative universes and inductive types. By the end
of this chapter, you will understand much of what this means.

# Simple Type Theory
%%%
tag := "simple-type-theory"
%%%

“Type theory” gets its name from the fact that every expression has an
associated _type_. For example, in a given context, {lit}`x + 0` may
denote a natural number and {lit}`f` may denote a function on the natural
numbers. For those who like precise definitions, a Lean natural number
is an arbitrary-precision unsigned integer.

Here are some examples of how you can declare objects in Lean and
check their types.

```lean
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- m : Nat
#check n
#check n + 0        -- n + 0 : Nat
#check m * (n + 0)  -- m * (n + 0) : Nat
#check b1           -- b1 : Bool
-- "&&" is the Boolean and
#check b1 && b2     -- b1 && b2 : Bool
-- Boolean or
#check b1 || b2     -- b1 || b2 : Bool
-- Boolean "true"
#check true         -- Bool.true : Bool

/- Evaluate. -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

Any text between {lit}`/-` and {lit}`-/` constitutes a comment block that is
ignored by Lean. Similarly, two dashes {lean}`--` indicate that the rest of
the line contains a comment that is also ignored. Comment blocks can
be nested, making it possible to “comment out” chunks of code, just as
in many programming languages.

The {kw}`def` keyword declares new constant symbols into the
working environment. In the example above, {leanRef}`def m : Nat := 1`
defines a new constant {leanRef}`m` of type {lean}`Nat` whose value is {leanRef}`1`.
The {kw}`#check` command asks Lean to report their
types; in Lean, auxiliary commands that query the system for
information typically begin with the hash (#) symbol.
The {kw}`#eval` command asks Lean to evaluate the given expression.
You should try
declaring some constants and type checking some expressions on your
own. Declaring new objects in this manner is a good way to experiment
with the system.

:::setup
```
variable (a b : Type)
```
What makes simple type theory powerful is that you can build new types
out of others. For example, if {lean}`a` and {lean}`b` are types, {lean}`a -> b`
denotes the type of functions from {lean}`a` to {lean}`b`, and {lean}`a × b`
denotes the type of pairs consisting of an element of {lean}`a` paired
with an element of {lean}`b`, also known as the _Cartesian product_. Note
that {lit}`×` is a Unicode symbol. The judicious use of Unicode improves
legibility, and all modern editors have great support for it. In the
Lean standard library, you often see Greek letters to denote types,
and the Unicode symbol {lit}`→` as a more compact version of {lit}`->`.
:::

```lean (check := false)
#check Nat → Nat      -- type the arrow as “\to” or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"
```
```lean
#check Nat.succ     -- Nat.succ (n : Nat) : Nat
#check (0, 1)       -- (0, 1) : Nat × Nat
#check Nat.add      -- Nat.add : Nat → Nat → Nat

#check Nat.succ 2   -- Nat.succ 2 : Nat
#check Nat.add 3    -- Nat.add 3 : Nat → Nat
#check Nat.add 5 2  -- Nat.add 5 2 : Nat
#check (5, 9).1     -- (5, 9).fst : Nat
#check (5, 9).2     -- (5, 9).snd : Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

Once again, you should try some examples on your own.

Let's take a look at some basic syntax. You can enter the Unicode
arrow {lit}`→` by typing {kbd}`\to` or {kbd}`\r` or {kbd}`\->`. You can also use the
ASCII alternative {lit}`->`, so the expressions {lean}`Nat -> Nat` and {lean}`Nat → Nat`
mean the same thing. Both expressions denote the type of
functions that take a natural number as input and return a natural
number as output. The Unicode symbol {lit}`×` for the Cartesian product
is entered as {kbd}`\times`. You will generally use lower-case Greek
letters like {lit}`α`, {lit}`β`, and {lit}`γ` to range over types. You can
enter these particular ones with {kbd}`\a`, {kbd}`\b`, and {kbd}`\g`.

::::setup
```
variable (α β : Type) (f : α → β) (x : α) (m n : Nat) (p : Nat × Nat)
```
There are a few more things to notice here. First, the application of
a function {lean}`f` to a value {lean}`x` is denoted {lean}`f x` (e.g., {lean}`Nat.succ 2`).
Second, when writing type expressions, arrows associate to the _right_; for
example, the type of {lean}`Nat.add` is {lean}`Nat → Nat → Nat` which is equivalent
to {lean}`Nat → (Nat → Nat)`. Thus you can
view {lean}`Nat.add` as a function that takes a natural number and returns
another function that takes a natural number and returns a natural
number. In type theory, this is generally more convenient than
writing {lean}`Nat.add` as a function that takes a pair of natural numbers as
input and returns a natural number as output. For example, it allows
you to “partially apply” the function {lean}`Nat.add`.  The example above shows
that {lean}`Nat.add 3` has type {lean}`Nat → Nat`, that is, {lean}`Nat.add 3` returns a
function that “waits” for a second argument, {lean}`n`, which is then
equivalent to writing {lean}`Nat.add 3 n`.
:::comment
```
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and “redefining” it to look like ``g`` is a process
known as _currying_. -->
```
:::


You have seen that if you have {lean}`m : Nat` and {lean}`n : Nat`, then
{lean}`(m, n)` denotes the ordered pair of {lean}`m` and {lean}`n` which is of
type {lean}`Nat × Nat`. This gives you a way of creating pairs of natural
numbers. Conversely, if you have {lean}`p : Nat × Nat`, then you can write
{lean}`p.1 : Nat` and {lean}`p.2 : Nat`. This gives you a way of extracting
its two components.
::::

# Types as objects
%%%
tag := "types-as-objects"
%%%

One way in which Lean's dependent type theory extends simple type
theory is that types themselves—entities like {lean}`Nat` and {lean}`Bool`—are first-class citizens, which is to say that they themselves are
objects. For that to be the case, each of them also has to have a
type.

```lean
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

You can see that each one of the expressions above is an object of
type {lean}`Type`. You can also declare new constants for types:

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- α : Type
#check F α      -- F α : Type
#check F Nat    -- F Nat : Type
#check G α      -- G α : Type → Type
#check G α β    -- G α β : Type
#check G α Nat  -- G α Nat : Type
```

As the example above suggests, you have already seen an example of a function of type
{lean}`Type → Type → Type`, namely, the Cartesian product {lean}`Prod`:

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- α × β : Type
#check α × β          -- α × β : Type

#check Prod Nat Nat   -- Nat × Nat : Type
#check Nat × Nat      -- Nat × Nat : Type
```

:::leanFirst
Here is another example: given any type {leanRef}`α`, the type {leanRef}`List α`
denotes the type of lists of elements of type {leanRef}`α`.

```lean
def α : Type := Nat

#check List α    -- List α : Type
#check List Nat  -- List Nat : Type
```
:::

Given that every expression in Lean has a type, it is natural to ask:
what type does {lean}`Type` itself have?

```lean
#check Type      -- Type : Type 1
```

You have actually come up against one of the most subtle aspects of
Lean's typing system. Lean's underlying foundation has an infinite
hierarchy of types:

```lean
#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
#check Type 2   -- Type 2 : Type 3
#check Type 3   -- Type 3 : Type 4
#check Type 4   -- Type 4 : Type 5
```

:::setup
```
universe n
variable (n : Nat)
```
Think of {lean}`Type 0` as a universe of “small” or “ordinary” types.
{lean}`Type 1` is then a larger universe of types, which contains {lean}`Type 0`
as an element, and {lean}`Type 2` is an even larger universe of types,
which contains {lean}`Type 1` as an element. The list is infinite:
there is a {lean}`Type n` for every natural number {lean}`n`. {lean}`Type` is
an abbreviation for {lean}`Type 0`:
:::

```lean
#check Type
#check Type 0
```


The following table may help concretize the relationships being discussed.
Movement along the x-axis represents a change in the universe, while movement
along the y-axis represents a change in what is sometimes referred to as
“degree”.

:::table

*
 * sort
 * {lean}`Prop` ({lean}`Sort 0`)
 * {lean}`Type` ({lean}`Sort 1`)
 * {lean}`Type 1` ({lean}`Sort 2`)
 * {lean}`Type 2` ({lean}`Sort 3`)
 * ...

*
 * type
 * {lean}`True`
 * {lean}`Bool`
 * {lean}`Nat -> Type`
 * {lean}`Type -> Type 1`
 * ...

*
 * term
 * {lean}`True.intro`
 * {lean}`true`
 * {lean}`fun n => Fin n`
 * {lean}`fun (_ : Type) => Type`
 * ...

:::

:::setup

```
universe u
variable (α : Type u)
```

Some operations, however, need to be _polymorphic_ over type
universes. For example, {lean}`List α` should make sense for any type
{lean}`α`, no matter which type universe {lean}`α` lives in. This explains the
type signature of the function {lean}`List`:


```lean
#check List    -- List.{u} (α : Type u) : Type u
```

Here {lit}`u` is a variable ranging over type levels. The output of the
{kw}`#check` command means that whenever {lean}`α` has type {lean}`Type u`,
{lean}`List α` also has type {lean}`Type u`. The function {lean}`Prod` is
similarly polymorphic:
:::

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

To define polymorphic constants, Lean allows you to
declare universe variables explicitly using the {kw}`universe` command:

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```

:::leanFirst
You can avoid the {kw}`universe` command by providing the universe parameters when defining {leanRef}`F`:

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```
:::

# Function Abstraction and Evaluation
%%%
tag := "function-abstraction-and-evaluation"
%%%

Lean provides a {kw}`fun` (or {kw}`λ`) keyword to create a function
from an expression as follows:

```lean
#check fun (x : Nat) => x + 5   -- fun x => x + 5 : Nat → Nat
-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5     -- fun x => x + 5 : Nat → Nat
```

The type {lean}`Nat` can be inferred in this example:
```lean
#check fun x => x + 5   -- fun x => x + 5 : Nat → Nat
#check λ x => x + 5     -- fun x => x + 5 : Nat → Nat
```

You can evaluate a lambda function by passing the required parameters:

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

:::setup
```
variable {x : α} {t : β}
```

Creating a function from another expression is a process known as
_lambda abstraction_. Suppose you have the variable {lean}`x : α` and you can
construct an expression {lean}`t : β`, then the expression {lean}`fun (x : α) => t`,
or, equivalently, {lean}`λ (x : α) => t`, is an object of type {lean}`α → β`. Think of
this as the function from {lean}`α` to {lean}`β` which maps
any value {leanRef}`x` to the value {leanRef}`t`.
:::

Here are some more examples

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
```

Lean interprets the final three examples as the same expression; in
the last expression, Lean infers the type of {leanRef}`x` and {leanRef}`y` from the
expression {leanRef}`if not y then x + 1 else x + 2`.

Some mathematically common examples of operations of functions can be
described in terms of lambda abstraction:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- fun x => x : Nat → Nat
#check fun x : Nat => true     -- fun x => true : Nat → Bool
#check fun x : Nat => g (f x)  -- fun x => g (f x) : Nat → Bool
#check fun x => g (f x)        -- fun x => g (f x) : Nat → Bool
```

Think about what these expressions mean. The expression
{lean}`fun x : Nat => x` denotes the identity function on {lean}`Nat`, the
expression {lean}`fun x : Nat => true` denotes the constant function that
always returns {lean}`true`, and {leanRef}`fun x : Nat => g (f x)` denotes the
composition of {leanRef}`f` and {leanRef}`g`.  You can, in general, leave off the
type annotation and let Lean infer it for you.  So, for example, you
can write {leanRef}`fun x => g (f x)` instead of {leanRef}`fun x : Nat => g (f x)`.

:::leanFirst
You can pass functions as parameters and by giving them names {leanRef}`f`
and {leanRef}`g` you can then use those functions in the implementation:

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
```
:::

You can also pass types as parameters:

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
The last expression, for example, denotes the function that takes
three types, {leanRef}`α`, {leanRef}`β`, and {leanRef}`γ`, and two functions, {leanRef}`g : β → γ`
and {leanRef}`f : α → β`, and returns the composition of {leanRef}`g` and {leanRef}`f`.
(Making sense of the type of this function requires an understanding
of _dependent products_, which will be explained below.)

:::setup
```
variable (α : Type) (t : β)
-- Avoid warnings
axiom whatever : α
def b : γ := whatever
```

The general form of a lambda expression is {lean}`fun (x : α) => t`, where
the variable {leanRef}`x` is a “bound variable”: it is really a placeholder,
whose “scope” does not extend beyond the expression {leanRef}`t`.  For
example, the variable {lit}`b` in the expression {lean}`fun (b : β) (x : α) => b`
has nothing to do with the constant {lean}`b` declared earlier.  In fact,
the expression denotes the same function as {lean}`fun (u : β) (z : α) => u`.


Formally, expressions that are the same up to a renaming of bound
variables are called _alpha equivalent_, and are considered “the
same.” Lean recognizes this equivalence.
:::

:::setup
```
variable (t : α → β) (s : α)
```
Notice that applying a term {lean}`t : α → β` to a term {lean}`s : α` yields
an expression {lean}`t s : β`. Returning to the previous example and
renaming bound variables for clarity, notice the types of the
following expressions:
:::

```lean
#check (fun x : Nat => x) 1     -- (fun x => x) 1 : Nat
#check (fun x : Nat => true) 1  -- (fun x => true) 1 : Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
```

As expected, the expression {lean}`(fun x : Nat =>  x) 1` has type {lean}`Nat`.
In fact, more should be true: applying the expression {lean}`(fun x : Nat => x)` to
{lean}`1` should “return” the value {lean}`1`. And, indeed, it does:

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

You will see later how these terms are evaluated. For now, notice that
this is an important feature of dependent type theory: every term has
a computational behavior, and supports a notion of _normalization_. In
principle, two terms that reduce to the same value are called
_definitionally equal_. They are considered “the same” by Lean's type
checker, and Lean does its best to recognize and support these
identifications.

Lean is a complete programming language. It has a compiler that
generates a binary executable and an interactive interpreter. You can
use the command {kw}`#eval` to execute expressions, and it is the
preferred way of testing your functions.

:::comment
```
<!--
Note that `#eval` and
`#reduce` are _not_ equivalent. The command `#eval` first compiles
Lean expressions into an intermediate representation (IR) and then
uses an interpreter to execute the generated IR. Some builtin types
(e.g., `Nat`, `String`, `Array`) have a more efficient representation
in the IR. The IR has support for using foreign functions that are
opaque to Lean.

In contrast, the ``#reduce`` command relies on a reduction engine
similar to the one used in Lean's trusted kernel, the part of Lean
that is responsible for checking and verifying the correctness of
expressions and proofs. It is less efficient than ``#eval``, and
treats all foreign functions as opaque constants. You will learn later
that there are some other differences between the two commands.
-->
```
:::

# Definitions
%%%
tag := "definitions"
%%%

Recall that the {kw}`def` keyword provides one important way of declaring new named
objects.

```lean
def double (x : Nat) : Nat :=
  x + x
```

This might look more familiar to you if you know how functions work in
other programming languages. The name {leanRef}`double` is defined as a
function that takes an input parameter {leanRef}`x` of type {lean}`Nat`, where the
result of the call is {leanRef}`x + x`, so it is returning type {lean}`Nat`. You
can then invoke this function using:

```lean
def double (x : Nat) : Nat :=
 x + x
-----
#eval double 3    -- 6
```

In this case you can think of {kw}`def` as a kind of named {kw}`fun`.
The following yields the same result:

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

You can omit the type declarations when Lean has enough information to
infer it.  Type inference is an important part of Lean:

```lean
def double :=
  fun (x : Nat) => x + x
```

The general form of a definition is {lit}`def foo : α := bar` where
{lit}`α` is the type returned from the expression {lit}`bar`.  Lean can
usually infer the type {lit}`α`, but it is often a good idea to write it
explicitly.  This clarifies your intention, and Lean will flag an
error if the right-hand side of the definition does not have a matching
type.

The right hand side {lit}`bar` can be any expression, not just a lambda.
So {kw}`def` can also be used to simply name a value like this:

```lean
def pi := 3.141592654
```

{kw}`def` can take multiple input parameters.  Let's create one
that adds two natural numbers:

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

The parameter list can be separated like this:

```lean
def double (x : Nat) : Nat :=
  x + x
-----
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

Notice here we called the {leanRef}`double` function to create the first
parameter to {leanRef}`add`.

You can use other more interesting expressions inside a {kw}`def`:

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

You can probably guess what this one will do.

You can also define a function that takes another function as input.
The following calls a given function twice passing the output of the
first invocation to the second:

```lean
def double (x : Nat) : Nat :=
 x + x
-----
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

Now to get a bit more abstract, you can also specify arguments that
are like type parameters:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

This means {leanRef}`compose` is a function that takes any two functions as input
arguments, so long as those functions each take only one input.
The type algebra {leanRef}`β → γ` and {leanRef}`α → β` means it is a requirement
that the type of the output of the second function must match the
type of the input to the first function—which makes sense, otherwise
the two functions would not be composable.

{leanRef}`compose` also takes a 3rd argument of type {leanRef}`α` which
it uses to invoke the second function (locally named {leanRef}`f`) and it
passes the result of that function (which is type {leanRef}`β`) as input to the
first function (locally named {leanRef}`g`).  The first function returns a type
{leanRef}`γ` so that is also the return type of the {leanRef}`compose` function.

{leanRef}`compose` is also very general in that it works over any type
{leanRef}`α β γ`.  This means {leanRef}`compose` can compose just about any 2 functions
so long as they each take one parameter, and so long as the type of
output of the second matches the input of the first.  For example:

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def double (x : Nat) : Nat :=
  x + x
-----
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

# Local Definitions
%%%
tag := "local-definitions"
%%%

:::setup
```
variable (t1 : α) (t2 : β)
```

Lean also allows you to introduce “local” definitions using the
{kw}`let` keyword. The expression {lean}`let a := t1; t2` is
definitionally equal to the result of replacing every occurrence of
{leanRef}`a` in {leanRef}`t2` by {leanRef}`t1`.
:::

```lean
#check let y := 2 + 2; y * y   -- let y := 2 + 2; y * y : Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

:::setup
```
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

variable (x : Nat)
```

Here, {lean}`twice_double x` is definitionally equal to the term {lean}`(x + x) * (x + x)`.

:::

You can combine multiple assignments by chaining {kw}`let` statements:

```lean
#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

The {lit}`;` can be omitted when a line break is used.
```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

::::leanFirst
:::setup
```
variable (t1 : α) (t2 : β)
```

Notice that the meaning of the expression {lean}`let a := t1; t2` is very
similar to the meaning of {lean}`(fun a => t2) t1`, but the two are not
the same. In the first expression, you should think of every instance
of {leanRef (in:="let a := t1; t2")}`a` in {leanRef (in:="let a := t1; t2")}`t2` as a syntactic abbreviation for {leanRef (in:="let a := t1; t2")}`t1`. In the
second expression, {leanRef (in:="(fun a => t2) t1")}`a` is a variable, and the expression
{leanRef (in:="(fun a => t2) t1")}`fun a => t2` has to make sense independently of the value of {leanRef (in:="(fun a => t2) t1")}`a`.
The {kw}`let` construct is a stronger means of abbreviation, and there
are expressions of the form {lean}`let a := t1; t2` that cannot be
expressed as {lean}`(fun a => t2) t1`. As an exercise, try to understand
why the definition of {leanRef}`foo` below type checks, but the definition of
{lit}`bar` does not.
:::

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
::::

# Variables and Sections
%%%
tag := "variables-and-sections"
%%%

Consider the following three function definitions:
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean provides you with the {kw}`variable` command to make such
declarations look more compact:

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
You can declare variables of any type, not just {lean}`Type` itself:
```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
Printing them out shows that all three groups of definitions have
exactly the same effect.

The {kw}`variable` command instructs Lean to insert the declared
variables as bound variables in definitions that refer to them by
name. Lean is smart enough to figure out which variables are used
explicitly or implicitly in a definition. You can therefore proceed as
though {leanRef}`α`, {leanRef}`β`, {leanRef}`γ`, {leanRef}`g`, {leanRef}`f`, {leanRef}`h`, and {leanRef}`x` are fixed
objects when you write your definitions, and let Lean abstract the
definitions for you automatically.

When declared in this way, a variable stays in scope until the end of
the file you are working on. Sometimes, however, it is useful to limit
the scope of a variable. For that purpose, Lean provides the notion of
a {kw}`section`:

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

When the section is closed, the variables go out of scope, and cannot
be referenced any more.

You do not have to indent the lines within a section. Nor do you have
to name a section, which is to say, you can use an anonymous
{kw}`section` / {kw}`end` pair. If you do name a section, however, you
have to close it using the same name. Sections can also be nested,
which allows you to declare new variables incrementally.

# Namespaces
%%%
tag := "namespaces"
%%%

Lean provides you with the ability to group definitions into nested,
hierarchical _namespaces_:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

When you declare that you are working in the namespace {leanRef}`Foo`, every
identifier you declare has a full name with prefix “{lit}`Foo.`”. Within
the namespace, you can refer to identifiers by their shorter names,
but once you end the namespace, you have to use the longer names.
Unlike {kw}`section`, namespaces require a name. There is only one
anonymous namespace at the root level.

The {leanRef}`open` command brings the shorter names into the current
context. Often, when you import a module, you will want to open one or
more of the namespaces it contains, to have access to the short
identifiers. But sometimes you will want to leave this information
protected by a fully qualified name, for example, when they conflict
with identifiers in another namespace you want to use. Thus namespaces
give you a way to manage names in your working environment.

For example, Lean groups definitions and theorems involving lists into
a namespace {lit}`List`.
```lean
#check List.nil
#check List.cons
#check List.map
```
:::leanFirst
The command {leanRef}`open List` allows you to use the shorter names:
```lean
open List

#check nil
#check cons
#check map
```
:::
Like sections, namespaces can be nested:
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```
Namespaces that have been closed can later be reopened, even in another file:

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

Like sections, nested namespaces have to be closed in the order they
are opened. Namespaces and sections serve different purposes:
namespaces organize data and sections declare variables for insertion
in definitions. Sections are also useful for delimiting the scope of
commands such as {kw}`set_option` and {kw}`open`.

In many respects, however, a {kw}`namespace`{lit}`  ...  `{kw}`end` block behaves the
same as a {kw}`section`{lit}`  ...  `{kw}`end` block. In particular, if you use the
{kw}`variable` command within a namespace, its scope is limited to the
namespace. Similarly, if you use an {kw}`open` command within a
namespace, its effects disappear when the namespace is closed.

# What makes dependent type theory dependent?
%%%
tag := "what-makes-dependent-type-theory-dependent"
%%%

:::setup
```
variable (α : Type) (n : Nat)
```

The short explanation is that types can depend on parameters. You
have already seen a nice example of this: the type {lean}`List α` depends
on the argument {lean}`α`, and this dependence is what distinguishes
{lean}`List Nat` and {lean}`List Bool`. For another example, consider the
type {lean}`Vector α n`, the type of vectors of elements of {lean}`α` of
length {lean}`n`.  This type depends on _two_ parameters: the type of the
elements in the vector ({lean}`α : Type`) and the length of the vector
{lean}`n : Nat`.
:::

::::setup
```
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
variable (α : Type) (a : α) (as : List α)
```
:::leanFirst

Suppose you wish to write a function {leanRef}`cons` which inserts a new
element at the head of a list. What type should {leanRef}`cons` have? Such a
function is _polymorphic_: you expect the {leanRef}`cons` function for
{lean}`Nat`, {lean}`Bool`, or an arbitrary type {leanRef}`α` to behave the same way.
So it makes sense to take the type to be the first argument to
{leanRef}`cons`, so that for any type, {lean}`α`, {lean}`cons α` is the insertion
function for lists of type {lean}`α`. In other words, for every {lean}`α`,
{lean}`cons α` is the function that takes an element {lean}`a : α` and a list
{lean}`as : List α`, and returns a new list, so you have {lean}`cons α a as : List α`.

It is clear that {lean}`cons α` should have type {lean}`α → List α → List α`.
But what type should {leanRef}`cons` have?  A first guess might be
{lean}`Type → α → List α → List α`, but, on reflection, this does not make
sense: the {leanRef}`α` in this expression does not refer to anything,
whereas it should refer to the argument of type {lean}`Type`.  In other
words, _assuming_ {lean}`α : Type` is the first argument to the function,
the type of the next two elements are {lean}`α` and {lean}`List α`. These
types vary depending on the first argument, {leanRef}`α`.

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- cons Nat : Nat → List Nat → List Nat
#check cons Bool       -- cons Bool : Bool → List Bool → List Bool
#check cons            -- cons (α : Type) (a : α) (as : List α) : List α
```
:::
::::

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (f : (a : α) → β a)
```

This is an instance of a _dependent function type_, or *dependent
arrow type*. Given {lean}`α : Type` and {lean}`β : α → Type`, think of {lean}`β`
as a family of types over {lean}`α`, that is, a type {lean}`β a` for each
{lean}`a : α`. In that case, the type {lean}`(a : α) → β a` denotes the type
of functions {lean}`f` with the property that, for each {lean}`a : α`, {lean}`f a`
is an element of {lean}`β a`. In other words, the type of the value
returned by {lean}`f` depends on its input.
:::

:::setup
```
variable (α : Type) (β : Type) (a : α) (f : (a : α) → β a)
```
Notice that {lean}`(a : α) → β` makes sense for any expression {lean}`β : Type`.
When the value of {lean}`β` depends on {leanRef}`a` (as does, for
example, the expression {leanRef}`β a` in the previous paragraph),
{leanRef}`(a : α) → β` denotes a dependent function type. When {lean}`β` doesn't
depend on {leanRef}`a`, {leanRef}`(a : α) → β` is no different from the type
{lean}`α → β`.  Indeed, in dependent type theory (and in Lean), {lean}`α → β`
is just notation for {lean}`(a : α) → β` when {lean}`β` does not depend on {leanRef (in := "a : α")}`a`.
:::

Returning to the example of lists, you can use the command {kw}`#check` to
inspect the type of the following {lean}`List` functions.  The {lit}`@` symbol
and the difference between the round and curly braces will be
explained momentarily.

```lean
#check @List.cons    -- @List.cons : {α : Type u_1} → α → List α → List α
#check @List.nil     -- @List.nil : {α : Type u_1} → List α
#check @List.length  -- @List.length : {α : Type u_1} → List α → Nat
#check @List.append  -- @List.append : {α : Type u_1} → List α → List α → List α
```

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (b : β a)
```
Just as dependent function types {lean}`(a : α) → β a` generalize the
notion of a function type {leanRef}`α → β` by allowing {leanRef (in := "α → β")}`β` to depend on
{lean}`α`, dependent Cartesian product types {lean}`(a : α) × β a` generalize
the Cartesian product {lit}`α × β` in the same way. Dependent products
are also called _sigma_ types, and you can also write them as
{lean}`Σ a : α, β a`. You can use {lean (type := "(a : α) × β a")}`⟨a, b⟩` or {lean}`Sigma.mk a b` to create a
dependent pair.  The {lit}`⟨` and {lit}`⟩` characters may be typed with
{kbd}`\langle` and {kbd}`\rangle` or {kbd}`\<` and {kbd}`\>`, respectively.
:::

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```
The functions {leanRef}`f` and {leanRef}`g` above denote the same function.


# Implicit Arguments
%%%
tag := "implicit-arguments"
%%%

Suppose we have an implementation of lists as:

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

Then, you can construct lists of {lean}`Nat` as follows:

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```
:::setup
```
def Lst (α : Type u) : Type u := List α
variable (α : Type)
```
Because the constructors are polymorphic over types, we have to insert
the type {lean}`Nat` as an argument repeatedly. But this information is
redundant: one can infer the argument {leanRef}`α` in
{leanRef}`Lst.cons Nat 5 (Lst.nil Nat)` from the fact that the second argument, {leanRef}`5`, has
type {lean}`Nat`. One can similarly infer the argument in {leanRef}`Lst.nil Nat`, not
from anything else in that expression, but from the fact that it is
sent as an argument to the function {leanRef}`Lst.cons`, which expects an element
of type {lean}`Lst α` in that position.
:::

This is a central feature of dependent type theory: terms carry a lot
of information, and often some of that information can be inferred
from the context. In Lean, one uses an underscore, {lit}`_`, to specify
that the system should fill in the information automatically. This is
known as an “implicit argument.”

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append
-----
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs -- Lst.append Nat as bs : Lst Nat
```

It is still tedious, however, to type all these underscores. When a
function takes an argument that can generally be inferred from
context, Lean allows you to specify that this argument should, by
default, be left implicit. This is done by putting the arguments in
curly braces, as follows:

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

All that has changed are the braces around {leanRef}`α : Type u` in the
declaration of the variables. We can also use this device in function
definitions:

```lean
universe u
def ident {α : Type u} (x : α) := x
```

Checking the type of {leanRef}`ident` requires wrapping it in parentheses to avoid having its signature shown:
```lean
universe u
def ident {α : Type u} (x : α) := x
---------
#check (ident)       -- ident : ?m.22 → ?m.22
#check ident 1       -- ident 1 : Nat
#check ident "hello" -- ident "hello" : String
#check @ident        -- @ident : {α : Type u_1} → α → α
```

The makes the first argument to {leanRef}`ident` implicit. Notationally,
this hides the specification of the type, making it look as though
{leanRef}`ident` simply takes an argument of any type. In fact, the function
{lean}`id` is defined in the standard library in exactly this way. We have
chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the {kw}`variable` command:

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

This definition of {leanRef}`ident` here has the same effect as the one
above.

Lean has very complex mechanisms for instantiating implicit arguments,
and we will see that they can be used to infer function types,
predicates, and even proofs. The process of instantiating these
“holes,” or “placeholders,” in a term is often known as
_elaboration_. The presence of implicit arguments means that at times
there may be insufficient information to fix the meaning of an
expression precisely. An expression like {lean}`id` or {lean}`List.nil` is
said to be _polymorphic_, because it can take on different meanings in
different contexts.

:::setup
```
variable (T : Type) (e : T)
```

One can always specify the type {lean}`T` of an expression {lean}`e` by
writing {lean}`(e : T)`. This instructs Lean's elaborator to use the value
{lean}`T` as the type of {lean}`e` when trying to resolve implicit
arguments. In the second pair of examples below, this mechanism is
used to specify the desired types of the expressions {lean}`id` and
{lean}`List.nil`:
:::

```lean
#check (List.nil)             -- [] : List ?m.2
#check (id)                   -- id : ?m.1 → ?m.1

#check (List.nil : List Nat)  -- [] : List Nat
#check (id : Nat → Nat)       -- id : Nat → Nat
```

Numerals are overloaded in Lean, but when the type of a numeral cannot
be inferred, Lean assumes, by default, that it is a natural number. So
the expressions in the first two {kw}`#check` commands below are
elaborated in the same way, whereas the third {kw}`#check` command
interprets {lean (type := "Int")}`2` as an integer.

```lean
#check 2            -- 2 : Nat
#check (2 : Nat)    -- 2 : Nat
#check (2 : Int)    -- 2 : Int
```

:::setup
```
variable (foo : {α : Type} → α → β)
```

Sometimes, however, we may find ourselves in a situation where we have
declared an argument to a function to be implicit, but now want to
provide the argument explicitly. If {lean}`foo` is such a function, the
notation {lean}`@foo` denotes the same function with all the arguments
made explicit.
:::

```lean
#check @id        -- @id : {α : Sort u_1} → α → α
#check @id Nat    -- id : Nat → Nat
#check @id Bool   -- id : Bool → Bool

#check @id Nat 1     -- id 1 : Nat
#check @id Bool true -- id true : Bool
```

Notice that now the first {kw}`#check` command gives the type of the
identifier, {leanRef}`id`, without inserting any placeholders. Moreover, the
output indicates that the first argument is implicit.
