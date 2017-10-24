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

    #check p.x -- nat
    #reduce  p.x -- 10
    #reduce  p.y -- 20
    -- END

If the constructor is not provided, then a constructor is named ``mk`` by default.

.. code-block:: lean

    namespace hide
    -- BEGIN
    structure prod (α : Type) (β : Type) :=
    (pr1 : α) (pr2 : β)

    #check prod.mk
    -- END
    end hide

You can provide universe levels explicitly. The annotations in the next example force the parameters ``α`` and ``β`` to be types from the same universe, and set the return type to also be in the same universe.

.. code-block:: lean

    namespace hide
    -- BEGIN
    structure {u} prod (α : Type u) (β : Type u) : 
      Type (max 1 u) :=
    (pr1 : α) (pr2 : β)

    set_option pp.universes true
    #check prod.mk
    -- END
    end hide

The ``set_option`` command above instructs Lean to display the universe levels.

We use ``max 1 l`` as the resultant universe level to ensure the universe level is never ``0`` even when the parameter ``α`` and ``β`` are propositions. Recall that in Lean, ``Type 0`` is ``Prop``, which is impredicative and proof irrelevant.

We can use the anonymous constructor notation to build structure values whenever the expected type is known.

.. code-block:: lean

    namespace hide
    -- BEGIN
    structure {u} prod (α : Type u) (β : Type u) : 
      Type (max 1 u) :=
    (pr1 : α) (pr2 : β)

    example : prod nat nat :=
    ⟨1, 2⟩

    #check (⟨1, 2⟩ : prod nat nat)
    -- END
    end hide

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

    #check { point . x := 10, y := 20 }   -- point ℕ
    #check { point . y := 20, x := 10 }
    #check ({x := 10, y := 20} : point nat)

    example : point nat :=
    { y := 20, x := 10 }

If the value of a field is not specified, Lean tries to infer it. If the unspecified fields cannot be inferred, Lean signs an error indicating the corresponding placeholder could not be synthesized.

.. code-block:: lean

    structure my_struct :=
    mk :: {α : Type} {β : Type} (a : α) (b : β)

    #check { my_struct . a := 10, b := true }

*Record update* is another common operation. It consists in creating a new record object by modifying the value of one or more fields. Lean provides a variation of the notation described above for record updates.

.. code-block:: text

    { record-obj with (<field-name> := <expr>)* }

The semantics are straightforward: record objects ``<record-obj>`` provide the values for the unspecified fields. If more than one record object is provided, then they are visited in order until Lean finds one the contains the unspecified field. Lean raises an error if any of the field names remain unspecified after all the objects are visited.

.. code-block:: lean

    structure point (α : Type) :=
    mk :: (x : α) (y : α)

    def p : point nat :=
    {x := 1, y := 2}

    #reduce {p with y := 3}
    #reduce {p with x := 3}

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
    {p with red := 200, green := 40, blue := 0, no_blue := rfl}

    example : rgp.x   = 10 := rfl
    example : rgp.red = 200 := rfl

