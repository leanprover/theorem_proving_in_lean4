Dependent Type Theory
=====================

Dependent type theory is a powerful and expressive language, allowing
you to express complex mathematical assertions, write complex hardware
and software specifications, and reason about both of these in a
natural and uniform way. Lean is based on a version of dependent type
theory known as the *Calculus of Constructions*, with a countable
hierarchy of non-cumulative universes and inductive types. By the end
of this chapter, you will understand much of what this means.

## Simple Type Theory

"Type theory" gets its name from the fact that every expression has an
associated *type*. For example, in a given context, ``x + 0`` may
denote a natural number and ``f`` may denote a function on the natural
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

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

Any text between ``/-`` and ``-/`` constitutes a comment block that is
ignored by Lean. Similarly, two dashes `--` indicate that the rest of
the line contains a comment that is also ignored. Comment blocks can
be nested, making it possible to "comment out" chunks of code, just as
in many programming languages.

The ``def`` keyword declares new constant symbols into the
working environment. In the example above, `def m : Nat := 1`
defines a new constant `m` of type `Nat` whose value is `1`.
The ``#check`` command asks Lean to report their
types; in Lean, auxiliary commands that query the system for
information typically begin with the hash (#) symbol.
The `#eval` command asks Lean to evaluate the given expression.
You should try
declaring some constants and type checking some expressions on your
own. Declaring new objects in this manner is a good way to experiment
with the system.

What makes simple type theory powerful is that you can build new types
out of others. For example, if ``a`` and ``b`` are types, ``a -> b``
denotes the type of functions from ``a`` to ``b``, and ``a × b``
denotes the type of pairs consisting of an element of ``a`` paired
with an element of ``b``, also known as the *Cartesian product*. Note
that `×` is a Unicode symbol. The judicious use of Unicode improves
legibility, and all modern editors have great support for it. In the
Lean standard library, you often see Greek letters to denote types,
and the Unicode symbol `→` as a more compact version of `->`.

```lean
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

Once again, you should try some examples on your own.

Let's take a look at some basic syntax. You can enter the unicode
arrow ``→`` by typing ``\to`` or ``\r`` or ``\->``. You can also use the
ASCII alternative ``->``, so the expressions ``Nat -> Nat`` and ``Nat →
Nat`` mean the same thing. Both expressions denote the type of
functions that take a natural number as input and return a natural
number as output. The unicode symbol ``×`` for the Cartesian product
is entered as ``\times``. You will generally use lower-case Greek
letters like ``α``, ``β``, and ``γ`` to range over types. You can
enter these particular ones with ``\a``, ``\b``, and ``\g``.

There are a few more things to notice here. First, the application of
a function ``f`` to a value ``x`` is denoted ``f x`` (e.g., `Nat.succ 2`).
Second, when writing type expressions, arrows associate to the *right*; for
example, the type of ``Nat.add`` is ``Nat → Nat → Nat`` which is equivalent
to `Nat → (Nat → Nat)`. Thus you can
view ``Nat.add`` as a function that takes a natural number and returns
another function that takes a natural number and returns a natural
number. In type theory, this is generally more convenient than
writing ``Nat.add`` as a function that takes a pair of natural numbers as
input and returns a natural number as output. For example, it allows
you to "partially apply" the function ``Nat.add``.  The example above shows
that ``Nat.add 3`` has type ``Nat → Nat``, that is, ``Nat.add 3`` returns a
function that "waits" for a second argument, ``n``, which is then
equivalent to writing ``Nat.add 3 n``.
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and "redefining" it to look like ``g`` is a process
known as *currying*. -->

You have seen that if you have ``m : Nat`` and ``n : Nat``, then
``(m, n)`` denotes the ordered pair of ``m`` and ``n`` which is of
type ``Nat × Nat``. This gives you a way of creating pairs of natural
numbers. Conversely, if you have ``p : Nat × Nat``, then you can write
``p.1 : Nat`` and ``p.2 : Nat``. This gives you a way of extracting
its two components.

## Types as objects

One way in which Lean's dependent type theory extends simple type
theory is that types themselves --- entities like ``Nat`` and ``Bool``
--- are first-class citizens, which is to say that they themselves are
objects. For that to be the case, each of them also has to have a
type.

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

You can see that each one of the expressions above is an object of
type ``Type``. You can also declare new constants for types:

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

As the example above suggests, you have already seen an example of a function of type
``Type → Type → Type``, namely, the Cartesian product `Prod`:

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

Here is another example: given any type ``α``, the type ``List α``
denotes the type of lists of elements of type ``α``.

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

Given that every expression in Lean has a type, it is natural to ask:
what type does ``Type`` itself have?

```lean
#check Type      -- Type 1
```

You have actually come up against one of the most subtle aspects of
Lean's typing system. Lean's underlying foundation has an infinite
hierarchy of types:

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

Think of ``Type 0`` as a universe of "small" or "ordinary" types.
``Type 1`` is then a larger universe of types, which contains ``Type
0`` as an element, and ``Type 2`` is an even larger universe of types,
which contains ``Type 1`` as an element. The list is infinite:
there is a ``Type n`` for every natural number ``n``. ``Type`` is
an abbreviation for ``Type 0``:

```lean
#check Type
#check Type 0
```


The following table may help concretize the relationships being discussed.
Movement along the x-axis represents a change in the universe, while movement
along the y-axis represents a change in what is sometimes referred to as
"degree".

|        |               |               |                 |                        |     |
|:------:|:-------------:|:-------------:|:---------------:|:----------------------:|:---:|
| sort   | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
| type   | True          | Bool          |   Nat -> Type   | Type -> Type 1         | ... |
| term   | trivial       | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |


Some operations, however, need to be *polymorphic* over type
universes. For example, ``List α`` should make sense for any type
``α``, no matter which type universe ``α`` lives in. This explains the
type signature of the function ``List``:

```lean
#check List    -- List.{u} (α : Type u) : Type u
```

Here ``u`` is a variable ranging over type levels. The output of the
``#check`` command means that whenever ``α`` has type ``Type n``,
``List α`` also has type ``Type n``. The function ``Prod`` is
similarly polymorphic:

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

To define polymorphic constants, Lean allows you to
declare universe variables explicitly using the `universe` command:

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

You can avoid the `universe` command by providing the universe parameters when defining `F`:

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```


## Function Abstraction and Evaluation

Lean provides a `fun` (or `λ`) keyword to create a function
from an expression as follows:

```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
```

You can evaluate a lambda function by passing the required parameters:

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

Creating a function from another expression is a process known as
*lambda abstraction*. Suppose you have the variable ``x : α`` and you can
construct an expression ``t : β``, then the expression ``fun (x : α)
=> t``, or, equivalently, ``λ (x : α) => t``, is an object of type ``α
→ β``. Think of this as the function from ``α`` to ``β`` which maps
any value ``x`` to the value ``t``.

Here are some more examples

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

Lean interprets the final three examples as the same expression; in
the last expression, Lean infers the type of ``x`` and ``y`` from the
expression `if not y then x + 1 else x + 2`.

Some mathematically common examples of operations of functions can be
described in terms of lambda abstraction:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

Think about what these expressions mean. The expression
``fun x : Nat => x`` denotes the identity function on ``Nat``, the
expression ``fun x : Nat => true`` denotes the constant function that
always returns ``true``, and ``fun x : Nat => g (f x)`` denotes the
composition of ``f`` and ``g``.  You can, in general, leave off the
type annotation and let Lean infer it for you.  So, for example, you
can write ``fun x => g (f x)`` instead of ``fun x : Nat => g (f x)``.

You can pass functions as parameters and by giving them names `f`
and `g` you can then use those functions in the implementation:

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

You can also pass types as parameters:

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
The last expression, for example, denotes the function that takes
three types, ``α``, ``β``, and ``γ``, and two functions, ``g : β → γ``
and ``f : α → β``, and returns the composition of ``g`` and ``f``.
(Making sense of the type of this function requires an understanding
of *dependent products*, which will be explained below.)

The general form of a lambda expression is ``fun x : α => t``, where
the variable ``x`` is a "bound variable": it is really a placeholder,
whose "scope" does not extend beyond the expression ``t``.  For
example, the variable ``b`` in the expression ``fun (b : β) (x : α) => b``
has nothing to do with the constant ``b`` declared earlier.  In fact,
the expression denotes the same function as ``fun (u : β) (z : α) => u``.

Formally, expressions that are the same up to a renaming of bound
variables are called *alpha equivalent*, and are considered "the
same." Lean recognizes this equivalence.

Notice that applying a term ``t : α → β`` to a term ``s : α`` yields
an expression ``t s : β``. Returning to the previous example and
renaming bound variables for clarity, notice the types of the
following expressions:

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

As expected, the expression ``(fun x : Nat =>  x) 1`` has type ``Nat``.
In fact, more should be true: applying the expression ``(fun x : Nat
=> x)`` to ``1`` should "return" the value ``1``. And, indeed, it does:

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

You will see later how these terms are evaluated. For now, notice that
this is an important feature of dependent type theory: every term has
a computational behavior, and supports a notion of *normalization*. In
principle, two terms that reduce to the same value are called
*definitionally equal*. They are considered "the same" by Lean's type
checker, and Lean does its best to recognize and support these
identifications.

Lean is a complete programming language. It has a compiler that
generates a binary executable and an interactive interpreter. You can
use the command `#eval` to execute expressions, and it is the
preferred way of testing your functions.

<!--
Note that `#eval` and
`#reduce` are *not* equivalent. The command `#eval` first compiles
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

## Definitions

Recall that the ``def`` keyword provides one important way of declaring new named
objects.

```lean
def double (x : Nat) : Nat :=
  x + x
```

This might look more familiar to you if you know how functions work in
other programming languages. The name `double` is defined as a
function that takes an input parameter `x` of type `Nat`, where the
result of the call is `x + x`, so it is returning type `Nat`. You
can then invoke this function using:

```lean
# def double (x : Nat) : Nat :=
#  x + x
#eval double 3    -- 6
```

In this case you can think of `def` as a kind of named `lambda`.
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

The general form of a definition is ``def foo : α := bar`` where
``α`` is the type returned from the expression ``bar``.  Lean can
usually infer the type ``α``, but it is often a good idea to write it
explicitly.  This clarifies your intention, and Lean will flag an
error if the right-hand side of the definition does not have a matching
type.

The right hand side `bar` can be any expression, not just a lambda.
So `def` can also be used to simply name a value like this:

```lean
def pi := 3.141592654
```

`def` can take multiple input parameters.  Let's create one
that adds two natural numbers:

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

The parameter list can be separated like this:

```lean
# def double (x : Nat) : Nat :=
#  x + x
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

Notice here we called the `double` function to create the first
parameter to `add`.

You can use other more interesting expressions inside a `def`:

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
# def double (x : Nat) : Nat :=
#  x + x
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

This means `compose` is a function that takes any two functions as input
arguments, so long as those functions each take only one input.
The type algebra `β → γ` and `α → β` means it is a requirement
that the type of the output of the second function must match the
type of the input to the first function - which makes sense, otherwise
the two functions would not be composable.

`compose` also takes a 3rd argument of type `α` which
it uses to invoke the second function (locally named `f`) and it
passes the result of that function (which is type `β`) as input to the
first function (locally named `g`).  The first function returns a type
`γ` so that is also the return type of the `compose` function.

`compose` is also very general in that it works over any type
`α β γ`.  This means `compose` can compose just about any 2 functions
so long as they each take one parameter, and so long as the type of
output of the second matches the input of the first.  For example:

```lean
# def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
#  g (f x)
# def double (x : Nat) : Nat :=
#  x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

Local Definitions
-----------------

Lean also allows you to introduce "local" definitions using the
``let`` keyword. The expression ``let a := t1; t2`` is
definitionally equal to the result of replacing every occurrence of
``a`` in ``t2`` by ``t1``.

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

Here, ``twice_double x`` is definitionally equal to the term ``(x + x) * (x + x)``.

You can combine multiple assignments by chaining ``let`` statements:

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

The ``;`` can be omitted when a line break is used.
```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

Notice that the meaning of the expression ``let a := t1; t2`` is very
similar to the meaning of ``(fun a => t2) t1``, but the two are not
the same. In the first expression, you should think of every instance
of ``a`` in ``t2`` as a syntactic abbreviation for ``t1``. In the
second expression, ``a`` is a variable, and the expression
``fun a => t2`` has to make sense independently of the value of ``a``.
The ``let`` construct is a stronger means of abbreviation, and there
are expressions of the form ``let a := t1; t2`` that cannot be
expressed as ``(fun a => t2) t1``. As an exercise, try to understand
why the definition of ``foo`` below type checks, but the definition of
``bar`` does not.

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
# Variables and Sections

Consider the following three function definitions:
```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

Lean provides you with the ``variable`` command to make such
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
You can declare variables of any type, not just ``Type`` itself:
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

The ``variable`` command instructs Lean to insert the declared
variables as bound variables in definitions that refer to them by
name. Lean is smart enough to figure out which variables are used
explicitly or implicitly in a definition. You can therefore proceed as
though ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, and ``x`` are fixed
objects when you write your definitions, and let Lean abstract the
definitions for you automatically.

When declared in this way, a variable stays in scope until the end of
the file you are working on. Sometimes, however, it is useful to limit
the scope of a variable. For that purpose, Lean provides the notion of
a ``section``:

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
``section`` / ``end`` pair. If you do name a section, however, you
have to close it using the same name. Sections can also be nested,
which allows you to declare new variables incrementally.

# Namespaces

Lean provides you with the ability to group definitions into nested,
hierarchical *namespaces*:

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

When you declare that you are working in the namespace ``Foo``, every
identifier you declare has a full name with prefix "``Foo.``". Within
the namespace, you can refer to identifiers by their shorter names,
but once you end the namespace, you have to use the longer names.
Unlike `section`, namespaces require a name. There is only one
anonymous namespace at the root level.

The ``open`` command brings the shorter names into the current
context. Often, when you import a module, you will want to open one or
more of the namespaces it contains, to have access to the short
identifiers. But sometimes you will want to leave this information
protected by a fully qualified name, for example, when they conflict
with identifiers in another namespace you want to use. Thus namespaces
give you a way to manage names in your working environment.

For example, Lean groups definitions and theorems involving lists into
a namespace ``List``.
```lean
#check List.nil
#check List.cons
#check List.map
```
The command ``open List`` allows you to use the shorter names:
```lean
open List

#check nil
#check cons
#check map
```
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
commands such as ``set_option`` and ``open``.

In many respects, however, a ``namespace ... end`` block behaves the
same as a ``section ... end`` block. In particular, if you use the
``variable`` command within a namespace, its scope is limited to the
namespace. Similarly, if you use an ``open`` command within a
namespace, its effects disappear when the namespace is closed.

## What makes dependent type theory dependent?

The short explanation is that types can depend on parameters. You
have already seen a nice example of this: the type ``List α`` depends
on the argument ``α``, and this dependence is what distinguishes
``List Nat`` and ``List Bool``. For another example, consider the
type ``Vector α n``, the type of vectors of elements of ``α`` of
length ``n``.  This type depends on *two* parameters: the type of the
elements in the vector (``α : Type``) and the length of the vector
``n : Nat``.

Suppose you wish to write a function ``cons`` which inserts a new
element at the head of a list. What type should ``cons`` have? Such a
function is *polymorphic*: you expect the ``cons`` function for
``Nat``, ``Bool``, or an arbitrary type ``α`` to behave the same way.
So it makes sense to take the type to be the first argument to
``cons``, so that for any type, ``α``, ``cons α`` is the insertion
function for lists of type ``α``. In other words, for every ``α``,
``cons α`` is the function that takes an element ``a : α`` and a list
``as : List α``, and returns a new list, so you have ``cons α a as : List α``.

It is clear that ``cons α`` should have type ``α → List α → List α``.
But what type should ``cons`` have?  A first guess might be
``Type → α → List α → List α``, but, on reflection, this does not make
sense: the ``α`` in this expression does not refer to anything,
whereas it should refer to the argument of type ``Type``.  In other
words, *assuming* ``α : Type`` is the first argument to the function,
the type of the next two elements are ``α`` and ``List α``. These
types vary depending on the first argument, ``α``.

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

This is an instance of a *dependent function type*, or *dependent
arrow type*. Given ``α : Type`` and ``β : α → Type``, think of ``β``
as a family of types over ``α``, that is, a type ``β a`` for each
``a : α``. In that case, the type ``(a : α) → β a`` denotes the type
of functions ``f`` with the property that, for each ``a : α``, ``f a``
is an element of ``β a``. In other words, the type of the value
returned by ``f`` depends on its input.

Notice that ``(a : α) → β`` makes sense for any expression ``β :
Type``. When the value of ``β`` depends on ``a`` (as does, for
example, the expression ``β a`` in the previous paragraph),
``(a : α) → β`` denotes a dependent function type. When ``β`` doesn't
depend on ``a``, ``(a : α) → β`` is no different from the type
``α → β``.  Indeed, in dependent type theory (and in Lean), ``α → β``
is just notation for ``(a : α) → β`` when ``β`` does not depend on ``a``.

Returning to the example of lists, you can use the command `#check` to
inspect the type of the following `List` functions.  The ``@`` symbol
and the difference between the round and curly braces will be
explained momentarily.

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

Just as dependent function types ``(a : α) → β a`` generalize the
notion of a function type ``α → β`` by allowing ``β`` to depend on
``α``, dependent Cartesian product types ``(a : α) × β a`` generalize
the Cartesian product ``α × β`` in the same way. Dependent products
are also called *sigma* types, and you can also write them as
`Σ a : α, β a`. You can use `⟨a, b⟩` or `Sigma.mk a b` to create a
dependent pair.  The `⟨` and `⟩` characters may be typed with
`\langle` and `\rangle` or `\<` and `\>`, respectively.

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
The functions `f` and `g` above denote the same function.


Implicit Arguments
------------------

Suppose we have an implementation of lists as:

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

Then, you can construct lists of `Nat` as follows:

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```

Because the constructors are polymorphic over types, we have to insert
the type ``Nat`` as an argument repeatedly. But this information is
redundant: one can infer the argument ``α`` in
``Lst.cons Nat 5 (Lst.nil Nat)`` from the fact that the second argument, ``5``, has
type ``Nat``. One can similarly infer the argument in ``Lst.nil Nat``, not
from anything else in that expression, but from the fact that it is
sent as an argument to the function ``Lst.cons``, which expects an element
of type ``Lst α`` in that position.

This is a central feature of dependent type theory: terms carry a lot
of information, and often some of that information can be inferred
from the context. In Lean, one uses an underscore, ``_``, to specify
that the system should fill in the information automatically. This is
known as an "implicit argument."

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs
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

All that has changed are the braces around ``α : Type u`` in the
declaration of the variables. We can also use this device in function
definitions:

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

This makes the first argument to ``ident`` implicit. Notationally,
this hides the specification of the type, making it look as though
``ident`` simply takes an argument of any type. In fact, the function
``id`` is defined in the standard library in exactly this way. We have
chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the ``variable`` command:

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

This definition of ``ident`` here has the same effect as the one
above.

Lean has very complex mechanisms for instantiating implicit arguments,
and we will see that they can be used to infer function types,
predicates, and even proofs. The process of instantiating these
"holes," or "placeholders," in a term is often known as
*elaboration*. The presence of implicit arguments means that at times
there may be insufficient information to fix the meaning of an
expression precisely. An expression like ``id`` or ``List.nil`` is
said to be *polymorphic*, because it can take on different meanings in
different contexts.

One can always specify the type ``T`` of an expression ``e`` by
writing ``(e : T)``. This instructs Lean's elaborator to use the value
``T`` as the type of ``e`` when trying to resolve implicit
arguments. In the second pair of examples below, this mechanism is
used to specify the desired types of the expressions ``id`` and
``List.nil``:

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

Numerals are overloaded in Lean, but when the type of a numeral cannot
be inferred, Lean assumes, by default, that it is a natural number. So
the expressions in the first two ``#check`` commands below are
elaborated in the same way, whereas the third ``#check`` command
interprets ``2`` as an integer.

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

Sometimes, however, we may find ourselves in a situation where we have
declared an argument to a function to be implicit, but now want to
provide the argument explicitly. If ``foo`` is such a function, the
notation ``@foo`` denotes the same function with all the arguments
made explicit.

```lean
#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

Notice that now the first ``#check`` command gives the type of the
identifier, ``id``, without inserting any placeholders. Moreover, the
output indicates that the first argument is implicit.
