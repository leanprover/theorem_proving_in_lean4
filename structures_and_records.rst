.. _structures_and_records:

Structures and Records
======================

We have seen that Lean's foundational system includes inductive types. We have, moreover, noted that it is a remarkable fact that it is possible to construct a substantial edifice of mathematics based on nothing more than the type universes, Pi types, and inductive types; everything else follows from those. The Lean standard library contains many instances of inductive types (e.g., ``nat``, ``prod``, ``list``), and even the logical connectives are defined using inductive types.

Remember that a non-recursive inductive type that contains only one constructor is called a *structure* or *record*. The product type is a structure, as is the dependent product type, that is, the Sigma type. In general, whenever we define a structure ``S``, we usually define *projection* functions that allow us to "destruct" each instance of ``S`` and retrieve the values that are stored in its fields. The functions ``prod.pr1`` and ``prod.pr2``, which return the first and second elements of a pair, are examples of such projections.

When writing programs or formalizing mathematics, it is not uncommon to define structures containing many fields. The ``structure`` command, available in Lean, provides infrastructure to support this process. When we define a structure using this command, Lean automatically generates all the projection functions. The ``structure`` command also allows us to define new structures based on previously defined ones. Moreover, Lean provides convenient notation for defining instances of a given structure.

Declaring Structures
--------------------

The structure command is essentially a "front end" for defining inductive data types. Every ``structure`` declaration introduces a namespace with the same name. The general form is as follows:

.. code-block:: text

    structure <name> <parameters> <parent-structures> : Sort u :=
      <constructor> :: <fields>

Most parts are optional. Here is an example:

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

Values of type ``point`` are created using ``point.mk a b``, and the fields of a point ``p`` are accessed using ``point.x p`` and ``point.y p``. The structure command also generates useful recursors and theorems. Here are some of the constructions generated for the declaration above.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    -- BEGIN
    #check point              -- a Type
    #check point.rec_on       -- the eliminator
    #check point.x            -- a projection / field accessor
    #check point.y            -- a projection / field accessor
    -- END

You can obtain the complete list of generated constructions using the command ``#print prefix``.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    -- BEGIN
    #print prefix point
    -- END

Here are some simple theorems and expressions that use the generated constructions. As usual, you can avoid the prefix ``point`` by using the command ``open point``.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    -- BEGIN
    #reduce point.x (point.mk 10 20)
    #reduce point.y (point.mk 10 20)

    open point

    example (α : Type) (a b : α) : x (mk a b) = a :=
    rfl

    example (α : Type) (a b : α) : y (mk a b) = b :=
    rfl
    -- END

Given ``p : point nat``, the notation ``p.x`` is shorthand for ``point.x p``. This provides a convenient way of accessing the fields of a structure.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    -- BEGIN
    def p := point.mk 10 20

    #check p.x  -- nat
    #reduce p.x  -- 10
    #reduce p.y  -- 20
    -- END

If the constructor is not provided, then a constructor is named ``mk`` by default.

.. code-block:: lean

    namespace hidden
    -- BEGIN
    structure prod (α : Type) (β : Type) :=
    (pr1 : α) (pr2 : β)

    #check prod.mk
    -- END
    end hidden

The dot notation is convenient not just for accessing the projections of a record, but also for applying functions defined in a namespace with the same name. Recall from :numref:`conjunction` that if ``p`` has type ``point``, the expression ``p.foo`` is interpreted as ``point.foo p``, assuming that the first non-implicit argument to ``foo`` has type ``point``. The expression ``p.add q`` is therefore shorthand for ``point.add p q`` in the example below.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    namespace point

    def add (p q : point ℕ) := mk (p.x + q.x) (p.y + q.y)

    end point

    def p : point ℕ := point.mk 1 2
    def q : point ℕ := point.mk 3 4

    #reduce p.add q  -- {x := 4, y := 6}

In the next chapter, you will learn how to define a function like ``add`` so that it works generically for elements of ``point α`` rather than just ``point ℕ``, assuming ``α`` has an associated addition operation.

More generally, given an expression ``p.foo x y z``, Lean will insert ``p`` at the first non-implicit argument to ``foo`` of type ``point``. For example, with the definition of scalar multiplication below, ``p.smul 3`` is interpreted as ``point.smul 3 p``.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    def point.smul (n : ℕ) (p : point ℕ) :=
    point.mk (n * p.x) (n * p.y)

    def p : point ℕ := point.mk 1 2

    #reduce p.smul 3  -- {x := 3, y := 6}

It is common to use a similar trick with the ``list.map`` function, which takes a list as its second non-implicit argument:

.. code-block:: lean

    #check @list.map
    -- Π {α : Type u_1} {β : Type u_2}, (α → β) → list α → list β

    def l : list nat := [1, 2, 3]
    def f : nat → nat := λ x, x * x

    #eval l.map f  -- [1, 4, 9]

Here ``l.map f`` is interpreted as ``list.map f l``.

If you have a structure definition that depends on a type, you can make it polymorphic over universe levels using a previously declared universe variable, declaring a universe variable on the fly, or using an underscore:

.. code-block:: lean

    universe u

    structure point (α : Type u) :=
    mk :: (x : α) (y : α)

    structure {v} point2 (α : Type v) :=
    mk :: (x : α) (y : α)

    structure point3 (α : Type _) :=
    mk :: (x : α) (y : α)

    #check @point
    #check @point2
    #check @point3

The three variations have the same net effect. The annotations in the next example force the parameters ``α`` and ``β`` to be types from the same universe, and set the return type to also be in the same universe.

.. code-block:: lean

    namespace hidden
    -- BEGIN
    structure {u} prod (α : Type u) (β : Type u) :
      Type u :=
    (pr1 : α) (pr2 : β)

    set_option pp.universes true
    #check prod.mk
    -- END
    end hidden

The ``set_option`` command above instructs Lean to display the universe levels. We can use the anonymous constructor notation to build structure values whenever the expected type is known.

.. code-block:: lean

    namespace hidden
    -- BEGIN
    structure {u} prod (α : Type u) (β : Type u) :
      Type u :=
    (pr1 : α) (pr2 : β)

    example : prod nat nat :=
    ⟨1, 2⟩

    #check (⟨1, 2⟩ : prod nat nat)
    -- END
    end hidden

Objects
-------

We have been using constructors to create elements of a structure type. For structures containing many fields, this is often inconvenient, because we have to remember the order in which the fields were defined. Lean therefore provides the following alternative notations for defining elements of a structure type.

.. code-block:: text

    { structure-name . (<field-name> := <expr>)* }
    or
    { (<field-name> := <expr>)* }

The prefix ``structure-name .`` can be omitted whenever the name of the structure can be inferred from the expected type. For example, we use this notation to define "points." The order that the fields are specified does not matter, so all the expressions below define the same point.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    #check { point . x := 10, y := 20 }  -- point ℕ
    #check { point . y := 20, x := 10 }
    #check ({x := 10, y := 20} : point nat)

    example : point nat :=
    { y := 20, x := 10 }

If the value of a field is not specified, Lean tries to infer it. If the unspecified fields cannot be inferred, Lean signs an error indicating the corresponding placeholder could not be synthesized.

.. code-block:: lean

    structure my_struct :=
    mk :: {α : Type} {β : Type} (a : α) (b : β)

    #check { my_struct . a := 10, b := true }

*Record update* is another common operation which amounts to creating a new record object by modifying the value of one or more fields in an old one. Lean allows you to specify that unassigned fields in the specification of a record should be taken from a previous defined record  object ``r`` by adding the annotation ``..r`` after the field assignments. If more than one record object is provided, then they are visited in order until Lean finds one the contains the unspecified field. Lean raises an error if any of the field names remain unspecified after all the objects are visited.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    def p : point nat :=
    {x := 1, y := 2}

    #reduce {y := 3, ..p}  -- {x := 1, y := 3}
    #reduce {x := 4, ..p}  -- {x := 4, y := 2}

    structure point3 (α : Type) :=
    mk :: (x : α) (y : α) (z : α)

    def q : point3 nat :=
    {x := 5, y := 5, z := 5}

    def r : point3 nat := {x := 6, ..p, ..q}

    #print r  -- {x := 6, y := p.y, z := q.z}
    #reduce r  -- {x := 6, y := 2, z := 5}

Inheritance
-----------

We can *extend* existing structures by adding new fields. This feature allow us to simulate a form of *inheritance*.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    inductive color
    | red | green | blue

    structure color_point (α : Type) extends point α :=
    mk :: (c : color)

In the next example, we define a structure using multiple inheritance, and then define an object using objects of the parent structures.

.. code-block:: lean

    structure point (α : Type) :=
    (x : α) (y : α) (z : α)

    structure rgb_val :=
    (red : nat) (green : nat) (blue : nat)

    structure red_green_point (α : Type) extends point α, rgb_val :=
    (no_blue : blue = 0)

    def p   : point nat := {x := 10, y := 10, z := 20}
    def rgp : red_green_point nat :=
    {red := 200, green := 40, blue := 0, no_blue := rfl, ..p}

    example : rgp.x   = 10 := rfl
    example : rgp.red = 200 := rfl
