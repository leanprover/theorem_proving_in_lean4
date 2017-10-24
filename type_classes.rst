.. _type_classes:

Type Classes
============

We have seen that Lean's elaborator provides helpful automation, filling in information that is tedious to enter by hand. In this section we will explore a simple but powerful technical device known as *type class inference*, which provides yet another mechanism for the elaborator to supply missing information.

The notion of a *type class* originated with the *Haskell* programming language. Many of the original uses carry over, but, as we will see, the realm of interactive theorem proving raises even more possibilities for their use.

Type Classes and Instances
--------------------------

Any family of types can be marked as a *type class*. Then we can declare particular elements of a type class to be *instances*. These provide hints to the elaborator: any time the elaborator is looking for an element of a type class, it can consult a table of declared instances to find a suitable element.

More precisely, there are three steps involved:

-  First, we declare a family of inductive types to be a type class.
-  Second, we declare instances of the type class.
-  Finally, we mark some implicit arguments with square brackets instead of curly brackets, to inform the elaborator that these arguments should be inferred by the type class mechanism.

Here is a somewhat frivolous example:

.. code-block:: lean

    attribute [class] nat

    instance nat_one : ℕ := 1
    /- The command instance is syntax sugar for
    def nat_one : ℕ := 1
    attribute [instance, reducible] nat_one
    -/

    def foo [x : ℕ] : nat := x

    #check @foo
    #reduce foo

    example : foo = 1 := rfl

Here we declare ``nat`` to be a class with a "canonical" instance ``1``. Then we declare ``foo`` to be, essentially, the identity function on the natural numbers, but we mark the argument implicit, and indicate that it should be inferred by type class inference. When we write ``foo``, the preprocessor interprets it as ``foo ?x``, where ``?x`` is an implicit argument. But when the elaborator gets hold of the expression, it sees that ``?x : ℕ`` is supposed to be solved by type class inference. It looks for a suitable element of the class, and it finds the instance ``one``. Thus, when we evaluate ``foo``, we simply get ``1``.

It is tempting to think of ``foo`` as defined to be equal to ``1``, but that is misleading. Every time we write ``foo``, the elaborator searches for a value. If we declare other instances of the class, that can change the value that is assigned to the implicit argument. This can result in seemingly paradoxical behavior. For example, we might continue the development above as follows:

.. code-block:: lean

    attribute [class] nat

    instance nat_one : ℕ := 1

    def foo [x : ℕ] : nat := x

    #reduce foo

    example : foo = 1 := rfl

    -- BEGIN
    instance nat_two : ℕ := 2

    #reduce foo

    example : foo ≠ 1 :=
    λ h : 2 = 1, nat.no_confusion h (λ h : 1 = 0, nat.no_confusion h)
    -- END

Now the "same" expression ``foo`` evaluates to ``2``. Whereas before we could prove ``foo = 1``, now we can prove ``foo ≠ 1``, because the inferred implicit argument has changed. When searching for a suitable instance of a type class, the elaborator tries the most recent instance declaration first, by default. We will see below, however, that it is possible to give individual instances higher or lower priority.

As with other attributes, you can assign the ``class`` or ``instance`` attributes in a definition, or after the fact, with an ``attribute`` command. To limit the scope of an assignment to the current file, use the ``local attribute`` variant.

The reason the example is frivolous is that there is rarely a need to "infer" a natural number; we can just hard-code the choice of ``1`` or ``2`` into the definition of ``foo``. Type classes become useful when they depend on parameters, in which case, the value that is inferred depends on these parameters.

Let us work through a simple example. Many theorems hold under the additional assumption that a type is inhabited, which is to say, it has at least one element. For example, if ``α`` is a type, ``∃ x : α, x = x`` is true only if ``α`` is inhabited. Similarly, it often happens that we would like a definition to return a default element in a "corner case." For example, we would like the expression ``head l`` to be of type ``α`` when ``l`` is of type ``list α``; but then we are faced with the problem that ``head l`` needs to return an "arbitrary" element of ``α`` in the case where ``l`` is the empty list, ``nil``.

For purposes like this, the standard library defines a type class ``inhabited : Type → Type``, to enable type class inference to infer a "default" or "arbitrary" element of an inhabited type. We will carry out a similar development in the examples that follow, using a namespace ``hide`` to avoid conflicting with the definitions in the standard library.

Let us start with the first step of the program above, declaring an appropriate class:

.. code-block:: lean

    namespace hide

    -- BEGIN
    class inhabited (α : Type) :=
    (value : α)
    /- The command 'class' above is shorthand for

    @[class] structure inhabited (α : Type) :=
    (value : α)
    -/
    -- END

    end hide

An element of the class ``inhabited α`` is simply an expression of the form ``inhabited.mk a``, for some element ``a : α``. The projection ``inhabited.value`` will allow us to "extract" such an element of ``α`` from an element of ``inhabited α``.

The second step of the program is to populate the class with some instances:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    -- BEGIN
    instance Prop_inhabited : inhabited Prop :=
    inhabited.mk true

    instance bool_inhabited : inhabited bool :=
    inhabited.mk tt

    instance nat_inhabited : inhabited nat :=
    inhabited.mk 0

    instance unit_inhabited : inhabited unit :=
    inhabited.mk ()
    -- END
    end hide

In the Lean standard library, we regularly use the anonymous constructor when defining instances. It is particularly useful when the class name is long.

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    -- BEGIN
    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩
    -- END
    end hide

This arranges things so that when type class inference is asked to infer an element ``?M : Prop``, it can find the element ``true`` to assign to ``?M``, and similarly for the elements ``tt``, ``0``, and ``()`` of the types ``bool``, ``nat``, and ``unit``, respectively.

The final step of the program is to define a function that infers an element ``s : inhabited α`` and puts it to good use. The following function simply extracts the corresponding element ``a : α``:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩
    -- BEGIN
    definition default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s
    -- END
    end hide

This has the effect that given a type expression ``α``, whenever we write ``default α``, we are really writing ``default α ?s``, leaving the elaborator to find a suitable value for the metavariable ``?s``. When the elaborator succeeds in finding such a value, it has effectively produced an element of type ``α``, as though by magic.

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩

    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s
    -- BEGIN
    #check default Prop    -- Prop
    #check default nat     -- ℕ
    #check default bool    -- bool
    #check default unit    -- unit
    -- END
    end hide

In general, whenever we write ``default α``, we are asking the elaborator to synthesize an element of type ``α``.

Notice that we can "see" the value that is synthesized with ``#reduce``:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩

    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s
    -- BEGIN
    #reduce default Prop    -- true
    #reduce default nat     -- 0
    #reduce default bool    -- tt
    #reduce default unit    -- ()
    -- END
    end hide

Sometimes we want to think of the default element of a type as being an *arbitrary* element, whose specific value should not play a role in our proofs. For that purpose, we can write ``arbitrary α`` instead of ``default α``. The definition of ``arbitrary`` is the same as that of default, but is marked ``irreducible`` to discourage the elaborator from unfolding it. This does not preclude proofs from making use of the value, however, so the use of ``arbitrary`` rather than ``default`` functions primarily to signal intent.

Chaining Instances
------------------

If that were the extent of type class inference, it would not be all the impressive; it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table. What makes type class inference powerful is that one can *chain* instances. That is, an instance declaration can in turn depend on an implicit instance of a type class. This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types ``α`` and ``β`` are inhabited, then so is their product:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩

    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s
    -- BEGIN
    instance prod_inhabited {α β : Type} [inhabited α] [inhabited β]
                            : inhabited (prod α β) :=
    ⟨(default α, default β)⟩
    -- END
    end hide

With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``nat × bool × unit``:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩

    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s

    instance prod_inhabited {α β : Type} 
        [inhabited α] [inhabited β] : 
      inhabited (prod α β) :=
    ⟨(default α, default β)⟩

    -- BEGIN
    #check default (nat × bool)
    #reduce default (nat × bool)
    -- END
    end hide

Given the expression ``default (nat × bool)``, the elaborator is called on to infer an implicit argument ``?M : inhabited (nat × bool)``. The instance ``prod_inhabited`` reduces this to inferring ``?M1 : inhabited nat`` and ``?M2 : inhabited bool``. The first one is solved by the instance ``nat_inhabited``. The second uses ``bool_inhabited``.

Similarly, we can inhabit function spaces with suitable constant functions:

.. code-block:: lean

    namespace hide

    class inhabited (α : Type) :=
    (value : α)

    instance Prop_inhabited : inhabited Prop :=
    ⟨true⟩

    instance bool_inhabited : inhabited bool :=
    ⟨tt⟩

    instance nat_inhabited : inhabited nat :=
    ⟨0⟩

    instance unit_inhabited : inhabited unit :=
    ⟨()⟩

    def default (α : Type) [s : inhabited α] : α :=
    @inhabited.value α s

    instance prod_inhabited {α β : Type} 
        [inhabited α] [inhabited β] :
      inhabited (prod α β) :=
    ⟨(default α, default β)⟩

    -- BEGIN
    instance inhabited_fun (α : Type) {β : Type} [inhabited β] : 
      inhabited (α → β) :=
    ⟨(λ a : α, default β)⟩

    #check default (nat → nat × bool)
    #reduce default (nat → nat × bool)
    -- END
    end hide

In this case, type class inference finds the default element
``λ (a : nat), (0, tt)``.

As an exercise, try defining default instances for other types, such as sum types and the list type.

Decidable Propositions
----------------------

Let us consider another example of a type class defined in the standard library, namely the type class of ``decidable`` propositions. Roughly speaking, an element of ``Prop`` is said to be decidable if we can decide whether it is true or false. The distinction is only useful in constructive mathematics; classically, every proposition is decidable. Nonetheless, as we will see, the implementation of the type class allows for a smooth transition between constructive and classical logic.

In the standard library, ``decidable`` is defined formally as follows:

.. code-block:: lean

    namespace hide

    -- BEGIN
    class inductive decidable (p : Prop) : Type
    | is_false : ¬p → decidable
    | is_true  :  p → decidable
    -- END
    end hide

Logically speaking, having an element ``t : decidable p`` is stronger than having an element ``t : p ∨ ¬p``; it enables us to define values of an arbitrary type depending on the truth value of ``p``. For example, for the expression ``if p then a else b`` to make sense, we need to know that ``p`` is decidable. That expression is syntactic sugar for ``ite p a b``, where ``ite`` is defined as follows:

.. code-block:: lean

    namespace hide

    -- BEGIN
    def ite (c : Prop) [d : decidable c] {α : Type} 
      (t e : α) : α :=
    decidable.rec_on d (λ hnc, e) (λ hc, t)
    -- END
    end hide

The standard library also contains a variant of ``ite`` called ``dite``, the dependent if-then-else expression. It is defined as follows:

.. code-block:: lean

    namespace hide

    -- BEGIN
    def dite (c : Prop) [d : decidable c] {α : Type} 
      (t : c → α) (e : ¬ c → α) : α :=
    decidable.rec_on d (λ hnc : ¬ c, e hnc) (λ hc : c, t hc)
    -- END
    end hide

That is, in ``dite c t e``, we can assume ``hc : c`` in the "then" branch, and ``hnc : ¬ c`` in the "else" branch. To make ``dite`` more convenient to use, Lean allows us to write ``if h : c then t else e`` instead of ``dite c (λ h : c, t) (λ h : ¬ c, e)``.

In the standard library, we cannot prove that every proposition is decidable. But we can prove that *certain* propositions are decidable. For example, we can prove the decidability of basic operations like equality and comparisons on the natural numbers and the integers. Moreover, decidability is preserved under propositional connectives:

.. code-block:: lean

    #check @and.decidable
    -- Π {p q : Prop} [hp : decidable p] [hq : decidable q], 
    --   decidable (p ∧ q)

    #check @or.decidable
    #check @not.decidable
    #check @implies.decidable

Thus we can carry out definitions by cases on decidable predicates on the natural numbers:

.. code-block:: lean

    open nat

    def step (a b x : ℕ) : ℕ :=
    if x < a ∨ x > b then 0 else 1

    set_option pp.implicit true
    #print definition step

Turning on implicit arguments shows that the elaborator has inferred the decidability of the proposition ``x < a ∨ x > b``, simply by applying appropriate instances.

With the classical axioms, we can prove that every proposition is decidable. When you import the classical axioms, then, ``decidable p`` has an instance for every ``p``, and the elaborator infers that value quickly. Thus all theorems in the library that rely on decidability assumptions are freely available when you want to reason classically.

The ``decidable`` type class also provides a bit of small-scale automation for proving theorems. The standard library introduces the following definitions and notation:

.. code-block:: lean

    namespace hide

    -- BEGIN
    def as_true (c : Prop) [decidable c] : Prop :=
    if c then true else false

    def of_as_true {c : Prop} [h₁ : decidable c] (h₂ : as_true c) : 
      c :=
    match h₁, h₂ with
    | (is_true h_c),  h₂ := h_c
    | (is_false h_c), h₂ := false.elim h₂
    end

    notation `dec_trivial` := of_as_true (by tactic.triv)
    -- END

    end hide

They work as follows. The expression ``as_true c`` tries to infer a decision procedure for ``c``, and, if it is successful, evaluates to either ``true`` or ``false``. In particular, if ``c`` is a true closed expression, ``as_true c`` will reduce definitionally to ``true``. On the assumption that ``as_true c`` holds, ``of_as_true`` produces a proof of ``c``. The notation ``dec_trivial`` puts it all together: to prove a target ``c``, it applies ``of_as_true`` and then using the ``triv`` tactic to prove ``as_true c``. By the previous observations, it will succeed any time the inferred decision procedure for ``c`` has enough information to evaluate, definitionally, to the ``is_true`` case. Here is an example of how ``dec_trivial`` can be used:

.. code-block:: lean

    example : 1 ≠ 0 ∧ (5 < 2 ∨ 3 < 7) := dec_trivial

Try changing the ``3`` to ``10``, thereby rendering the expression false. The resulting error message complains that ``of_as_true (1 ≠ 0 ∧ (5 < 2 ∨ 10 < 7))`` is not definitionally equal to ``true``.

Overloading with Type Classes
-----------------------------

We now consider the application of type classes that motivates their use in functional programming languages like Haskell, namely, to overload notation in a principled way. In Lean, a symbol like ``+`` can be given entirely unrelated meanings, a phenomenon that is sometimes called "ad-hoc" overloading. Typically, however, we use the ``+`` symbol to denote a binary function from a type to itself, that is, a function of type ``α → α → α`` for some type ``α``. We can use type classes to infer an appropriate addition function for suitable types ``α``. We will see in the next section that this is especially useful for developing algebraic hierarchies of structures in a formal setting.

We can declare a type class ``has_add α`` as follows:

.. code-block:: lean

    namespace hide
    -- BEGIN
    universes u

    class has_add (α : Type u) :=
    (add : α → α → α)

    def add {α : Type u} [has_add α] : α → α → α := has_add.add

    local notation a `+` b := add a b
    -- END
    end hide

The class ``has_add α`` is supposed to be inhabited exactly when there is an appropriate addition function for ``α``. The ``add`` function is designed to find an instance of ``has_add α`` for the given type, ``α``, and apply the corresponding binary addition function. The notation ``a + b`` thus refers to the addition that is appropriate to the type of ``a`` and ``b``. We can then declare instances for ``nat``, and ``bool``:

.. code-block:: lean

    namespace hide
    universes u

    class has_add (α : Type u) :=
    (add : α → α → α)

    def add {α : Type u} [has_add α] : α → α → α := has_add.add

    local notation a `+` b := add a b

    -- BEGIN
    instance nat_has_add : has_add nat :=
    ⟨nat.add⟩

    instance bool_has_add : has_add bool :=
    ⟨bor⟩

    #check 2 + 2    -- nat
    #check tt + ff  -- bool
    -- END
    end hide

As with ``inhabited`` and ``decidable``, the power of type class inference stems not only from the fact that the class enables the elaborator to look up appropriate instances, but also from the fact that it can chain instances to infer complex addition operations. For example, assuming that there are appropriate addition functions for types ``α`` and ``β``, we can define addition on ``α × β`` pointwise:

.. code-block:: lean

    namespace hide
    universes u v
    class has_add (α : Type u) :=
    (add : α → α → α)

    def add {α : Type u} [has_add α] : α → α → α := has_add.add

    local notation a `+` b := add a b

    instance nat_has_add : has_add nat :=
    ⟨nat.add⟩

    instance bool_has_add : has_add bool :=
    ⟨bor⟩

    -- BEGIN
    instance prod_has_add {α : Type u} {β : Type v} 
        [has_add α] [has_add β] : 
      has_add (α × β) :=
    ⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, ⟨a₁+a₂, b₁+b₂⟩⟩

    #check (1, 2) + (3, 4)    -- ℕ × ℕ
    #reduce  (1, 2) + (3, 4)  -- (4, 6)
    -- END
    end hide

We can similarly define pointwise addition of functions:

.. code-block:: lean

    namespace hide
    universes u v
    class has_add (α : Type u) :=
    (add : α → α → α)

    def add {α : Type u} [has_add α] : α → α → α := has_add.add

    local notation a `+` b := add a b

    instance nat_has_add : has_add nat :=
    ⟨nat.add⟩

    instance bool_has_add : has_add bool :=
    ⟨bor⟩

    instance prod_has_add {α : Type u} {β : Type v} 
      [has_add α] [has_add β] : has_add (α × β) :=
    ⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, ⟨a₁+a₂, b₁+b₂⟩⟩

    -- BEGIN
    instance fun_has_add {α : Type u} {β : Type v} [has_add β] : 
      has_add (α → β) :=
    ⟨λ f g x, f x + g x⟩

    #check (λ x : nat, 1) + (λ x, 2)   -- ℕ → ℕ
    #reduce (λ x : nat, 1) + (λ x, 2)    -- λ (x : ℕ), 3
    -- END
    end hide

As an exercise, try defining instances of ``has_add`` for lists, and show that they work as expected.

Managing Type Class Inference
-----------------------------

You can ask Lean for information about the classes and instances that are currently in scope:

.. code-block:: lean

    #print classes
    #print instances inhabited

At times, you may find that the type class inference fails to find an expected instance, or, worse, falls into an infinite loop and times out. To help debug in these situations, Lean enables you to request a trace of the search:

.. code-block:: lean

    set_option trace.class_instances true

If you add this to your file in Emacs mode and use ``C-c C-x`` to run an independent Lean process on your file, the output buffer will show a trace every time the type class resolution procedure is subsequently triggered.

You can also limit the search depth (the default is 32):

.. code-block:: lean

    set_option class.instance_max_depth 5

Remember also that in the Emacs Lean mode, tab completion works in ``set_option``, to help you find suitable options.

As noted above, the type class instances in a given context represent a Prolog-like program, which gives rise to a backtracking search. Both the efficiency of the program and the solutions that are found can depend on the order in which the system tries the instance. Instances which are declared last are tried first. Moreover, if instances are declared in other modules, the order in which they are tried depends on the order in which namespaces are opened. Instances declared in namespaces which are opened later are tried earlier.

You can change the order that type classes instances are tried by assigning them a *priority*. When an instance is declared, it is assigned a priority value ``std.priority.default``, defined to be 1000 in module ``init.core`` in the standard library. You can assign other priorities when defining an instance, and you can later change the priority with the ``attribute`` command. The following example illustrates how this is done:

.. code-block:: lean

    class foo :=
    (a : nat) (b : nat)

    @[priority std.priority.default+1]
    instance i1 : foo :=
    ⟨1, 1⟩

    instance i2 : foo :=
    ⟨2, 2⟩

    example : foo.a = 1 := rfl

    @[priority std.priority.default+20]
    instance i3 : foo :=
    ⟨3, 3⟩

    example : foo.a = 3 := rfl

    attribute [instance, priority 10] i3

    example : foo.a = 1 := rfl

    attribute [instance, priority std.priority.default-10] i1

    example : foo.a = 2 := rfl

.. _coercions_using_type_classes:

Coercions using Type Classes
----------------------------

The most basic type of coercion maps elements of one type to another. For example, a coercion from ``nat`` to ``int`` allows us to view any element ``n : nat`` as an element of ``int``. But some coercions depend on parameters; for example, for any type ``α``, we can view any element ``l : list α`` as an element of ``set α``, namely, the set of elements occurring in the list. The corresponding coercion is defined on the "family" of types ``list α``, parameterized by ``α``.

Lean allows us to declare three kinds of coercions:

-  from a family of types to another family of types
-  from a family of types to the class of sorts
-  from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.

In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from ``α`` to ``β`` by declaring an instance of ``has_coe α β``. For example, we can define a coercion from ``bool`` to ``Prop`` as follows:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩

This enables us to use boolean terms in if-then-else expressions:

.. code-block:: lean

    instance bool_to_Prop : has_coe bool Prop :=
    ⟨λ b, b = tt⟩
    -- BEGIN
    #reduce if tt then 3 else 5
    #reduce if ff then 3 else 5
    -- END

We can define a coercion from ``list α`` to ``set α`` as follows:

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}
    def l : list nat := [3, 4]

    #check s ∪ l -- set nat

Coercions are only considered if the given and expected types do not contain metavariables at elaboration time. In the following example, when we elaborate the union operator, the type of ``[3, 2]`` is ``list ?m``, and a coercion will not be considered since it contains metavariables.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    /- The following #check command produces an error. -/
    -- #check s ∪ [3, 2]
    -- END

We can work around this issue by using a type ascription.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ [(3:nat), 2]
    -- or
    #check s ∪ ([3, 2] : list nat)
    -- END

In the examples above, you may have noticed the symbol ``↑`` produced by the ``#check`` commands. It is the lift operator, ``↑t`` is notation for ``coe t``. We can use this operator to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.

.. code-block:: lean

    universe u

    def list.to_set {α : Type u} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type u) : 
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    #check s ∪ ↑[3, 2]

    variables n m : nat
    variable i : int
    #check i + ↑n + ↑m
    #check i + ↑(n + m)
    #check ↑n + i
    -- END

In the first two examples, the coercions are not strictly necessary since Lean will insert implicit nat → int coercions. However, ``#check n + i`` would raise an error, because the expected type of ``i`` is nat in order to match the type of n, and no int → nat coercion exists). In the third example, we therefore insert an explicit ``↑`` to coerce ``n`` to ``int``. 

The standard library defines a coercion from subtype ``{x : α // p x}`` to ``α`` as follows:

.. code-block:: lean

    namespace hide
    universe u
    -- BEGIN
    instance coe_subtype {α : Type u} {p : α → Prop} : 
      has_coe {x // p x} α :=
    ⟨λ s, subtype.val s⟩
    -- END
    end hide

Lean will also chain coercions as necessary. Actually, the type class ``has_coe_t`` is the transitive closure of ``has_coe``. You may have noticed that the type of ``coe`` depends on ``has_lift_t``, the transitive closure of the type class ``has_lift``, instead of ``has_coe_t``. Every instance of ``has_coe_t`` is also an instance of ``has_lift_t``, but the elaborator only introduces automatically instances of ``has_coe_t``. That is, to be able to coerce using an instance of ``has_lift_t``, we must use the operator ``↑``. In the standard library, we have the following instance:

.. code-block:: lean

    namespace hide
    universes u v

    instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] : 
      has_lift (list a) (list b) :=
    ⟨λ l, list.map (@coe a b _) l⟩

    variables s : list nat
    variables r : list int
    #check ↑s ++ r

    end hide

It is not an instance of ``has_coe`` because lists are frequently used for writing programs, and we do not want a linear-time operation to be silently introduced by Lean, and potentially mask mistakes performed by the user. By forcing the user to write ``↑``, she is making her intent clear to Lean.

Let us now consider the second kind of coercion. By the *class of sorts*, we mean the collection of universes ``Type u``. A coercion of the second kind is of the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, F x1 ... xn → Type u

where ``F`` is a family of types as above. This allows us to write ``s : t`` whenever ``t`` is of type ``F a1 ... an``. In other words, the coercion allows us to view the elements of ``F a1 ... an`` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, 
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : 
      has_mul (S.carrier) :=
    ⟨S.mul⟩

In other words, a semigroup consists of a type, ``carrier``, and a multiplication, ``mul``, with the property that the multiplication is associative. The ``instance`` command allows us to write ``a * b`` instead of ``Semigroup.mul S a b`` whenever we have ``a b : S.carrier``; notice that Lean can infer the argument ``S`` from the types of ``a`` and ``b``. The function ``Semigroup.carrier`` maps the class ``Semigroup`` to the sort ``Type u``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, 
                   mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩
    -- BEGIN
    #check Semigroup.carrier
    -- END

If we declare this function to be a coercion, then whenever we have a semigroup ``S : Semigroup``, we can write ``a : S`` instead of ``a : S.carrier``:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := Type u, coe := λ S, S.carrier}

    example (S : Semigroup) (a b c : S) : 
      (a * b) * c = a * (b * c) :=
    Semigroup.mul_assoc _ a b c
    -- END

It is the coercion that makes it possible to write ``(a b c : S)``. Note that, we define an instance of ``has_coe_to_sort Semigroup`` instead of ``has_coe Semigroup Type``. The reason is that when Lean needs a coercion to sort, it only knows it needs a type, but, in general, the universe is not known. The field ``S`` in the class ``has_coe_to_sort`` is used to specify the universe we are coercing too.

By the *class of function types*, we mean the collection of Pi types ``Π z : B, C``. The third kind of coercion has the form

.. code-block:: text

    c : Π x1 : A1, ..., xn : An, y : F x1 ... xn, Π z : B, C

where ``F`` is again a family of types and ``B`` and ``C`` can depend on ``x1, ..., xn, y``. This makes it possible to write ``t s`` whenever ``t`` is an element of ``F a1 ... an``. In other words, the coercion enables us to view elements of ``F a1 ... an`` as functions. Continuing the example above, we can define the notion of a morphism between semigroups ``S1`` and ``S2``. That is, a function from the carrier of ``S1`` to the carrier of ``S2`` (note the implicit coercion) that respects the multiplication. The projection ``morphism.mor`` takes a morphism to the underlying function:

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    -- BEGIN
    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    #check @morphism.mor
    -- END

As a result, it is a prime candidate for the third type of coercion.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩


    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    -- BEGIN
    instance morphism_to_fun (S1 S2 : Semigroup) : 
      has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup} 
        (f : morphism S1 S2) (a b : S1) : 
      f (a * b) = f a * f b :=
    f.resp_mul a b

    example (S1 S2 : Semigroup) (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]
    -- END

With the coercion in place, we can write ``f (a * a * a)`` instead of ``morphism.mor f (a * a * a)``. When the ``morphism``, ``f``, is used where a function is expected, Lean inserts the coercion. Similar to ``has_coe_to_sort``, we have yet another class ``has_coe_to_fun`` for the this class of coercions. The field ``F`` is used to specify function type we are coercing too. This type may depend on the type we are coercing from.

Finally, ``⇑f`` and ``↥S`` are notations for ``coe_fn f`` and ``coe_sort S``. They are the coercion operators for the function and sort classes.

We can instruct Lean's pretty-printer to hide the operators ``↑`` and ``⇑`` with ``set_option``.

.. code-block:: lean

    universe u

    structure Semigroup : Type (u+1) :=
    (carrier : Type u)
    (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

    instance Semigroup_has_mul (S : Semigroup) : has_mul (S.carrier) :=
    ⟨S.mul⟩

    instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
    {S := _, coe := λ S, S.carrier}

    structure morphism (S1 S2 : Semigroup) :=
    (mor : S1 → S2)
    (resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

    instance morphism_to_fun (S1 S2 : Semigroup) : has_coe_to_fun (morphism S1 S2) :=
    { F   := λ _, S1 → S2,
      coe := λ m, m.mor }

    lemma resp_mul {S1 S2 : Semigroup} (f : morphism S1 S2) (a b : S1) : f (a * b) = f a * f b :=
    f.resp_mul a b

    -- BEGIN
    theorem test (S1 S2 : Semigroup) 
        (f : morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
    calc
      f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
                ... = f a * f a * f a : by rw [resp_mul f]

    #check @test
    set_option pp.coercions false
    #check @test
    -- END