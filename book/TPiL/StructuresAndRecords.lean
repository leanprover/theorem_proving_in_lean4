import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "Structures and Records" =>
%%%
tag := "structures-and-records"
%%%

We have seen that Lean's foundational system includes inductive
types. We have, moreover, noted that it is a remarkable fact that it
is possible to construct a substantial edifice of mathematics based on
nothing more than the type universes, dependent arrow types, and inductive types;
everything else follows from those. The Lean standard library contains
many instances of inductive types (e.g., {lean}`Nat`, {lean}`Prod`, {lean}`List`),
and even the logical connectives are defined using inductive types.

Recall that a non-recursive inductive type that contains only one
constructor is called a _structure_ or _record_. The product type is a
structure, as is the dependent product (Sigma) type.
In general, whenever we define a structure {lit}`S`, we usually
define _projection_ functions that allow us to “destruct” each
instance of {lit}`S` and retrieve the values that are stored in its
fields. The functions {lean}`Prod.fst` and {lean}`Prod.snd`, which return the
first and second elements of a pair, are examples of such projections.

When writing programs or formalizing mathematics, it is not uncommon
to define structures containing many fields. The {kw}`structure`
command, available in Lean, provides infrastructure to support this
process. When we define a structure using this command, Lean
automatically generates all the projection functions. The
{kw}`structure` command also allows us to define new structures based on
previously defined ones. Moreover, Lean provides convenient notation
for defining instances of a given structure.

# Declaring Structures

The structure command is essentially a “front end” for defining
inductive data types. Every {kw}`structure` declaration introduces a
namespace with the same name. The general form is as follows:

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

Most parts are optional. Here is an example:

```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
```

:::setup
```
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
variable (p : Point α) (a b : α)
```
Values of type {leanRef}`Point` are created using {lean}`Point.mk a b`, and the
fields of a point {lean}`p` are accessed using {lean}`Point.x p` and
{lean}`Point.y p` (but {lean}`p.x` and {lean}`p.y` also work, see below).
The structure command also generates useful recursors and
theorems. Here are some of the constructions generated for the
declaration above.
:::

```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
------
-- a Type
#check Point

-- the eliminator
#check @Point.rec

-- the constructor
#check @Point.mk -- @Point.mk : {α : Type u_1} → α → α → Point α

-- a projection
#check @Point.x -- @Point.x : {α : Type u_1} → Point α → α

-- a projection
#check @Point.y -- @Point.y : {α : Type u_1} → Point α → α
```

If the constructor name is not provided, then a constructor is named
{lit}`mk` by default.

:::leanFirst
Here are some simple theorems and expressions that use the generated
constructions. As usual, you can avoid the prefix {leanRef}`Point` by using
the command {leanRef}`open Point`.

```lean
structure Point (α : Type u) where
  x : α
  y : α
------
#eval Point.x (Point.mk 10 20) -- 10

#eval Point.y (Point.mk 10 20) -- 20

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```
:::


:::setup
````
structure Point (α : Type u) where
  x : α
  y : α
variable (p : Point Nat)
````


Given {lean}`p : Point Nat`, the dot notation {lean}`p.x` is shorthand for
{lean}`Point.x p`. This provides a convenient way of accessing the fields
of a structure.
:::

```lean
structure Point (α : Type u) where
 x : α
 y : α
------
def p := Point.mk 10 20

#check p.x  -- p.x : Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

:::leanFirst
The dot notation is convenient not just for accessing the projections
of a record, but also for applying functions defined in a namespace
with the same name. Recall from the {ref "conjunction"}[Conjunction section] if {leanRef}`p`
has type {leanRef}`Point`, the expression {lit}`p.foo` is interpreted as
{lit}`Point.foo p`, assuming that the first non-implicit argument to
{lit}`foo` has type {leanRef}`Point`. The expression {leanRef}`p.add q` is therefore
shorthand for {lit}`Point.add p q` in the example below.

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- { x := 4, y := 6 }
```
:::

:::setup
````
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

variable {α : Type u}
````

In the next chapter, you will learn how to define a function like
{leanRef}`add` so that it works generically for elements of {lean}`Point α`
rather than just {lean}`Point Nat`, assuming {lean}`α` has an associated
addition operation.
:::

:::leanFirst
More generally, given an expression {lit}`p.foo x y z` where {lit}`p : Point`,
Lean will insert {lit}`p` at the first argument to {lit}`Point.foo` of type
{lit}`Point`. For example, with the definition of scalar multiplication
below, {leanRef}`p.smul 3` is interpreted as {leanRef}`Point.smul 3 p`.

```lean
structure Point (α : Type u) where
 x : α
 y : α
 deriving Repr
------
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- { x := 3, y := 6 }

example {p : Point Nat} : p.smul 3 = Point.smul 3 p := rfl
```
:::

It is common to use a similar trick with the {name}`List.map` function,
which takes a list as its second non-implicit argument:

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]

example {xs : List α} {f : α → β} :
    xs.map f = List.map f xs :=
  rfl
```

Here {leanRef}`xs.map f` is interpreted as {leanRef}`List.map f xs`.

# Objects

We have been using constructors to create elements of a structure
type. For structures containing many fields, this is often
inconvenient, because we have to remember the order in which the
fields were defined. Lean therefore provides the following alternative
notations for defining elements of a structure type.

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

The suffix {lit}`: structure-type` can be omitted whenever the name of
the structure can be inferred from the expected type. For example, we
use this notation to define “points.” The order that the fields are
specified does not matter, so all the expressions below define the
same point.

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- { x := 10, y := 20 } : Point Nat

#check { y := 20, x := 10 : Point _ } -- { x := 10, y := 20 } : Point Nat

#check ({ x := 10, y := 20 } : Point Nat) -- { x := 10, y := 20 } : Point Nat

example : Point Nat :=
  { y := 20, x := 10 }
```

Fields can be marked as implicit using curly braces.
Implicit fields become implicit parameters to the constructor.

If the value of a field is not specified, Lean tries to infer it. If
the unspecified fields cannot be inferred, Lean flags an error
indicating the corresponding placeholder could not be synthesized.

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

_Record update_ is another common operation which amounts to creating
a new record object by modifying the value of one or more fields in an
old one. Lean allows you to specify that unassigned fields in the
specification of a record should be taken from a previously defined
structure object {lit}`s` by adding the annotation {lit}`s `{kw}`with` before the field
assignments. If more than one record object is provided, then they are
visited in order until Lean finds one that contains the unspecified
field. Lean raises an error if any of the field names remain
unspecified after all the objects are visited.

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

# Inheritance

We can _extend_ existing structures by adding new fields. This feature
allows us to simulate a form of _inheritance_.

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

In the next example, we define a structure using multiple inheritance,
and then define an object using objects of the parent structures.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```
