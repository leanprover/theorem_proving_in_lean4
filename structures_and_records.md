Structures and Records
======================

We have seen that Lean's foundational system includes inductive
types. We have, moreover, noted that it is a remarkable fact that it
is possible to construct a substantial edifice of mathematics based on
nothing more than the type universes, dependent arrow types, and inductive types;
everything else follows from those. The Lean standard library contains
many instances of inductive types (e.g., ``Nat``, ``Prod``, ``List``),
and even the logical connectives are defined using inductive types.

Recall that a non-recursive inductive type that contains only one
constructor is called a *structure* or *record*. The product type is a
structure, as is the dependent product (Sigma) type.
In general, whenever we define a structure ``S``, we usually
define *projection* functions that allow us to "destruct" each
instance of ``S`` and retrieve the values that are stored in its
fields. The functions ``prod.pr1`` and ``prod.pr2``, which return the
first and second elements of a pair, are examples of such projections.

When writing programs or formalizing mathematics, it is not uncommon
to define structures containing many fields. The ``structure``
command, available in Lean, provides infrastructure to support this
process. When we define a structure using this command, Lean
automatically generates all the projection functions. The
``structure`` command also allows us to define new structures based on
previously defined ones. Moreover, Lean provides convenient notation
for defining instances of a given structure.

Declaring Structures
--------------------

The structure command is essentially a "front end" for defining
inductive data types. Every ``structure`` declaration introduces a
namespace with the same name. The general form is as follows:

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

Most parts are optional. Here is an example:

```lean
structure Point (α : Type u) where
  mk :: (x : α) (y : α)
```

Values of type ``Point`` are created using ``Point.mk a b``, and the
fields of a point ``p`` are accessed using ``Point.x p`` and
``Point.y p``. The structure command also generates useful recursors and
theorems. Here are some of the constructions generated for the
declaration above.

```lean
# structure Point (α : Type u) where
#  mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection
```

If the constructor name is not provided, then a constructor is named
``mk`` by default.  You can also avoid the parentheses around field
names if you add a line break between each field.

```lean
structure Point (α : Type u) where
  x : α
  y : α
```

Here are some simple theorems and expressions that use the generated
constructions. As usual, you can avoid the prefix ``Point`` by using
the command ``open Point``.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```

Given ``p : Point Nat``, the notation ``p.x`` is shorthand for
``Point.x p``. This provides a convenient way of accessing the fields
of a structure.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

The dot notation is convenient not just for accessing the projections
of a record, but also for applying functions defined in a namespace
with the same name. Recall from the [Conjunction section](./propositions_and_proofs.md#_conjunction) if ``p``
has type ``Point``, the expression ``p.foo`` is interpreted as
``Point.foo p``, assuming that the first non-implicit argument to
``foo`` has type ``Point``. The expression ``p.add q`` is therefore
shorthand for ``Point.add p q`` in the example below.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p := Point.mk 1 2
def q := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}
```
Note that in the implementation of `Point.add` the name `mk`
is short for `Point.mk` which is the generated constructor
for the `structure Point`.  The qualifier `Point.` can be
safely dropped because we are in the scope of `Point.add`.

Note: The `deriving Repr` instruction implements a default
representation so that you can `#eval` a Point and see a nice readable
output message `{x := 4, y := 6}`. Without this instruction you will
get an error from the `#eval` statement saying:

```
failed to be synthesized, this instance instructs Lean on how to display
the resulting value, recall that any type implementing the `Repr` class
also implements the `Lean.Eval` class
```

In the next chapter, you will learn how to define a function like
``add`` so that it works generically for elements of ``Point α``
rather than just ``Point Nat``, assuming ``α`` has an associated
addition operation.

More generally, given an expression ``p.foo x y z`` where `p : Point`,
Lean will insert ``p`` at the first argument to ``Point.foo`` of type
``Point``. For example, with the definition of scalar multiplication
below, ``p.smul 3`` is interpreted as ``Point.smul 3 p``.

```lean
# structure Point (α : Type u) where
#  x : α
#  y : α
#  deriving Repr
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}
```

Dot notation is very popular with list operations like  ``List.map``
as follows:

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def square (x : Nat) := x * x

#eval xs.map square  -- [1, 4, 9]
```

Here ``xs.map f`` is interpreted as ``List.map f xs``.

Objects
-------

We have been using constructors to create elements of a structure
type. For structures containing many fields, this is often
inconvenient, because we have to remember the order in which the
fields were defined. Lean therefore provides the following alternative
notations for defining elements of a structure type using the field
names also:

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

So for example, you can create a Point object using just this syntax:

```lean
# structure Point (α : Type u) where
#   x : α
#   y : α
#  deriving Repr
#eval { x := 10, y := 20 : Point Nat}
#eval { x := 10, y := 20 : Point Nat }
#eval { y := 20, x := 10 : Point _ }
#eval ({ x := 10, y := 20 } : Point Nat)
```

The suffix ``: structure-type`` can be omitted whenever the name of
the structure can be inferred from the expected type. For example,
the Lean compiler can infer the type `Point Nat` in the following
call to `Point.smul`:

```lean
# structure Point (α : Type u) where
#   x : α
#   y : α
#  deriving Repr
# def Point.smul (n : Nat) (p : Point Nat) :=
#   Point.mk (n * p.x) (n * p.y)
#eval Point.smul 3 { y := 20, x := 10 } -- { x := 30, y := 60 }
```
Notice we can write `{ y := 20, x := 10 }` here instead of the more
verbose `{ x := 10, y := 20 : Point Nat }`.  Notice also that the
order that the fields are specified does not matter.

If the value of a field is not specified, Lean tries to infer it. If
the unspecified fields cannot be inferred, Lean flags an error
indicating the corresponding placeholder could not be synthesized.

```lean
structure MyStruct {α : Type u} {β : Type v} where
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```
Instances of a structure are immutable, but Lean makes it easy to
create a new record object by modifying the value of one or more
fields in an old one. Lean allows you to specify that the unassigned
fields in the specification of a record should be taken from a
previously defined structure object ``s`` by adding the annotation ``s
with`` before the field assignments.

```lean
# structure Point (α : Type u) where
#   x : α
#   y : α
#   deriving Repr
def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }
```

You can also provide more than one input record object, and then they
are visited in order until Lean finds one that contains the
unspecified field. Lean raises an error if any of the field names
remain unspecified after all the objects are visited.  The first input
that defines the field wins.

```lean
# structure Point (α : Type u) where
#   x : α
#   y : α
#   deriving Repr
def p : Point Nat :=
  { x := 1, y := 2 }

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

In the above example, notice it is creating `r` by combining the `p`
and `q`. So it takes `x` and `y` fields from `p`, and the `z` field
from `q`.  Then the `with` clause overrides the value of `x` from `p`
which is how it ends up with `{ x := 6, y := 2, z := 5 }`.

You can combine `p` and `q` with no override by writing `{ p, q with }`


Inheritance
-----------

We can *extend* existing structures by adding new fields. This feature
allows you to simulate a form of *inheritance*.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

inductive Color where
  | red | green | blue
  deriving Repr

structure ColorPoint (α : Type u) extends Point α where
  c : Color
  deriving Repr

#check (ColorPoint.mk {x := 1, y := 2} Color.red)

def cp : ColorPoint Nat :=
  { x := 1, y := 2, c := Color.red }

#eval cp -- { toPoint := { x := 1, y := 2 }, c := Color.red }
```

In the next example, we define a structure using multiple inheritance,
and then define an object using objects of the parent structures.

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α
  deriving Repr

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr

structure ColorPoint (α : Type u) extends Point α, RGBValue where
  deriving Repr

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

#eval p  -- { x := 10, y := 10, z := 20 }

def rgb : RGBValue := {red := 200, green := 40, blue := 0 }

#eval rgb -- { red := 200, green := 40, blue := 20 }

def cp : ColorPoint Nat :=
  { p, rgb with blue := 0 }

#eval cp -- { toPoint := { x := 10, y := 10, z := 20 },
         --   toRGBValue := { red := 200, green := 40, blue := 0 } }

example : cp.x   = 10 := rfl
example : cp.red = 200 := rfl
example : cp.blue = 0 := rfl
```

Notice that the `toPoint` and `toRGBValue` accessors have been automatically
generated.
