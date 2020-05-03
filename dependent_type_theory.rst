.. _dependent_type_theory:

Dependent Type Theory
=====================

Dependent type theory is a powerful and expressive language, allowing us to express complex mathematical assertions, write complex hardware and software specifications, and reason about both of these in a natural and uniform way. Lean is based on a version of dependent type theory known as the *Calculus of Constructions*, with a countable hierarchy of non-cumulative universes and inductive types. By the end of this chapter, you will understand much of what this means.

Simple Type Theory
------------------

As a foundation for mathematics, set theory has a simple ontology that is rather appealing. Everything is a set, including numbers, functions, triangles, stochastic processes, and Riemannian manifolds. It is a remarkable fact that one can construct a rich mathematical universe from a small number of axioms that describe a few basic set-theoretic constructions.

But for many purposes, including formal theorem proving, it is better to have an infrastructure that helps us manage and keep track of the various kinds of mathematical objects we are working with. "Type theory" gets its name from the fact that every expression has an associated *type*. For example, in a given context, ``x + 0`` may denote a natural number and ``f`` may denote a function on the natural numbers.

Here are some examples of how we can declare objects in Lean and check their types.

.. code-block:: lean

    /- declare some constants -/

    constant m : nat        -- m is a natural number
    constant n : nat
    constants b1 b2 : bool  -- declare two constants at once

    /- check their types -/

    #check m            -- output: nat
    #check n
    #check n + 0        -- nat
    #check m * (n + 0)  -- nat
    #check b1           -- bool
    #check b1 && b2     -- "&&" is boolean and
    #check b1 || b2     -- boolean or
    #check tt           -- boolean "true"

    -- Try some examples of your own.

Any text between the ``/-`` and ``-/`` constitutes a comment that is ignored by Lean. Similarly, two dashes indicate that the rest of the line contains a comment that is also ignored. Comment blocks can be nested, making it possible to "comment out" chunks of code, just as in many programming languages.

The ``constant`` and ``constants`` commands introduce new constant symbols into the working environment. The ``#check`` command asks Lean to report their types; in Lean, commands that query the system for information typically begin with the hash symbol. You should try declaring some constants and type checking some expressions on your own. Declaring new objects in this way is a good way to experiment with the system, but it is ultimately undesirable: Lean is a foundational system, which is to say, it provides us with powerful mechanisms to *define* all the mathematical objects we need, rather than simply postulating them. We will explore these mechanisms in the chapters to come.

What makes simple type theory powerful is that one can build new types out of others. For example, if ``α`` and ``β`` are types, ``α → β`` denotes the type of functions from ``α`` to ``β``, and ``α × β`` denotes the cartesian product, that is, the type of ordered pairs consisting of an element of ``α`` paired with an element of ``β``.

.. code-block:: lean

    constants m n : nat

    constant f : nat → nat           -- type the arrow as "\to" or "\r"
    constant f' : nat -> nat         -- alternative ASCII notation
    constant f'' : ℕ → ℕ             -- alternative notation for nat
    constant p : nat × nat           -- type the product as "\times"
    constant q : prod nat nat        -- alternative notation
    constant g : nat → nat → nat
    constant g' : nat → (nat → nat)  -- has the same type as g!
    constant h : nat × nat → nat

    constant F : (nat → nat) → nat   -- a "functional"

    #check f               -- ℕ → ℕ
    #check f n             -- ℕ
    #check g m n           -- ℕ
    #check g m             -- ℕ → ℕ
    #check (m, n)          -- ℕ × ℕ
    #check p.1             -- ℕ
    #check p.2             -- ℕ
    #check (m, n).1        -- ℕ
    #check (p.1, n)        -- ℕ × ℕ
    #check F f             -- ℕ

Once again, you should try some examples on your own.

Let us dispense with some basic syntax. You can enter the unicode arrow ``→`` by typing ``\to`` or ``\r``. You can also use the ASCII alternative ``->``, so that the expression ``nat -> nat`` and ``nat → nat`` mean the same thing. Both expressions denote the type of functions that take a natural number as input and return a natural number as output. The symbol ``ℕ`` is alternative unicode notation for ``nat``; you can enter it by typing ``\nat``. The unicode symbol ``×`` for the cartesian product is entered ``\times``. We will generally use lower-case greek letters like ``α``, ``β``, and ``γ`` to range over types. You can enter these particular ones with ``\a``, ``\b``, and ``\g``.

There are a few more things to notice here. First, the application of a function ``f`` to a value ``x`` is denoted ``f x``. Second, when writing type expressions, arrows associate to the *right*; for example, the type of ``g`` is ``nat → (nat → nat)``. Thus we can view ``g`` as a function that takes natural numbers and returns another function that takes a natural number and returns a natural number. In type theory, this is generally more convenient than writing ``g`` as a function that takes a pair of natural numbers as input, and returns a natural number as output. For example, it allows us to "partially apply" the function ``g``. The example above shows that ``g m`` has type ``nat → nat``, that is, the function that "waits" for a second argument, ``n``, and then returns ``g m n``. Taking a function ``h`` of type ``nat × nat → nat`` and "redefining" it to look like ``g`` is a process known as *currying*, something we will come back to below.

By now you may also have guessed that, in Lean, ``(m, n)`` denotes the ordered pair of ``m`` and ``n``, and if ``p`` is a pair, ``p.1`` and ``p.2`` denote the two projections.

Types as Objects
----------------

One way in which Lean's dependent type theory extends simple type theory is that types themselves --- entities like ``nat`` and ``bool`` --- are first-class citizens, which is to say that they themselves are objects of study. For that to be the case, each of them also has to have a type.

.. code-block:: lean

    #check nat               -- Type
    #check bool              -- Type
    #check nat → bool        -- Type
    #check nat × bool        -- Type
    #check nat → nat         -- ...
    #check nat × nat → nat
    #check nat → nat → nat
    #check nat → (nat → nat)
    #check nat → nat → bool
    #check (nat → nat) → nat

We see that each one of the expressions above is an object of type ``Type``. We can also declare new constants and constructors for types:

.. code-block:: lean

    constants α β : Type
    constant F : Type → Type
    constant G : Type → Type → Type

    #check α        -- Type
    #check F α      -- Type
    #check F nat    -- Type
    #check G α      -- Type → Type
    #check G α β    -- Type
    #check G α nat  -- Type

Indeed, we have already seen an example of a function of type ``Type → Type → Type``, namely, the Cartesian product.

.. code-block:: lean

    constants α β : Type

    #check prod α β       -- Type
    #check prod nat nat   -- Type

Here is another example: given any type ``α``, the type ``list α`` denotes the type of lists of elements of type ``α``.

.. code-block:: lean

    constant α : Type

    #check list α    -- Type
    #check list nat  -- Type

For those more comfortable with set-theoretic foundations, it may be helpful to think of a type as nothing more than a set, in which case, the elements of the type are just the elements of the set. Given that every expression in Lean has a type, it is natural to ask: what type does ``Type`` itself have?

.. code-block:: lean

    #check Type      -- Type 1

We have actually come up against one of the most subtle aspects of Lean's typing system. Lean's underlying foundation has an infinite hierarchy of types:

.. code-block:: lean

    #check Type     -- Type 1
    #check Type 1   -- Type 2
    #check Type 2   -- Type 3
    #check Type 3   -- Type 4
    #check Type 4   -- Type 5

Think of ``Type 0`` as a universe of "small" or "ordinary" types. ``Type 1`` is then a larger universe of types, which contains ``Type 0`` as an element, and ``Type 2`` is an even larger universe of types, which contains ``Type 1`` as an element. The list is indefinite, so that there is a ``Type n`` for every natural number ``n``. ``Type`` is an abbreviation for ``Type 0``:

.. code-block:: lean

    #check Type
    #check Type 0

There is also another type, ``Prop``, which has special properties.

.. code-block:: lean

    #check Prop -- Type

We will discuss ``Prop`` in the next chapter.

We want some operations, however, to be *polymorphic* over type universes. For example, ``list α`` should make sense for any type ``α``, no matter which type universe ``α`` lives in. This explains the type annotation of the function ``list``:

.. code-block:: lean

    #check list    -- Type u_1 → Type u_1

Here ``u_1`` is a variable ranging over type levels. The output of the ``#check`` command means that whenever ``α`` has type ``Type n``, ``list α`` also has type ``Type n``. The function ``prod`` is similarly polymorphic:

.. code-block:: lean

    #check prod    -- Type u_1 → Type u_2 → Type (max u_1 u_2)

To define polymorphic constants and variables, Lean allows us to declare universe variables explicitly:

.. code-block:: lean

    universe u
    constant α : Type u
    #check α

Throughout this book, we will do this in examples when we want type constructions to have as much generality as possible. We will come to learn that the ability to treat type constructors as instances of ordinary mathematical functions is a powerful feature of dependent type theory.

Function Abstraction and Evaluation
-----------------------------------

We have seen that if we have ``m n : nat``, then we have ``(m, n) : nat × nat``. This gives us a way of creating pairs of natural numbers. Conversely, if we have ``p : nat × nat``, then we have ``fst p : nat`` and ``snd p : nat``. This gives us a way of "using" a pair, by extracting its two components.

We already know how to "use" a function ``f : α → β``, namely, we can apply it to an element ``a : α`` to obtain ``f a : β``. But how do we create a function from another expression?

The companion to application is a process known as "abstraction," or "lambda abstraction." Suppose that by temporarily postulating a variable ``x : α`` we can construct an expression ``t : β``. Then the expression ``fun x : α, t``, or, equivalently, ``λ x : α, t``, is an object of type ``α → β``. Think of this as the function from ``α`` to ``β`` which maps any value ``x`` to the value ``t``, which depends on ``x``. For example, in mathematics it is common to say "let ``f`` be the function which maps any natural number ``x`` to ``x + 5``." The expression ``λ x : nat, x + 5`` is just a symbolic representation of the right-hand side of this assignment.

.. code-block:: lean

    #check fun x : nat, x + 5
    #check λ x : nat, x + 5

Here are some more abstract examples:

.. code-block:: lean

    constants α β  : Type
    constants a1 a2 : α
    constants b1 b2 : β

    constant f : α → α
    constant g : α → β
    constant h : α → β → α
    constant p : α → α → bool

    #check fun x : α, f x                      -- α → α
    #check λ x : α, f x                        -- α → α
    #check λ x : α, f (f x)                    -- α → α
    #check λ x : α, h x b1                     -- α → α
    #check λ y : β, h a1 y                     -- β → α
    #check λ x : α, p (f (f x)) (h (f a1) b2)  -- α → bool
    #check λ x : α, λ y : β, h (f x) y         -- α → β → α
    #check λ (x : α) (y : β), h (f x) y        -- α → β → α
    #check λ x y, h (f x) y                    -- α → β → α

Lean interprets the final three examples as the same expression; in the last expression, Lean infers the type of ``x`` and ``y`` from the types of ``f`` and ``h``.

Try writing some expressions on your own. Some mathematically common examples of operations of functions can be described in terms of lambda abstraction:

.. code-block:: lean

    constants α β γ : Type
    constant f : α → β
    constant g : β → γ
    constant b : β

    #check λ x : α, x        -- α → α
    #check λ x : α, b        -- α → β
    #check λ x : α, g (f x)  -- α → γ
    #check λ x, g (f x)

Think about what these expressions mean. The expression ``λ x : α, x`` denotes the identity function on ``α``, the expression ``λ x : α, b`` denotes the constant function that always returns ``b``, and ``λ x : α, g (f x)``, denotes the composition of ``f`` and ``g``. We can, in general, leave off the type annotations on the variable and let Lean infer it for us. So, for example, we can write ``λ x, g (f x)`` instead of ``λ x : α, g (f x)``.

We can abstract over any of the constants in the previous definitions:

.. code-block:: lean

    constants α β γ : Type
    constant f : α → β
    constant g : β → γ
    constant b : β

    -- BEGIN
    #check λ b : β, λ x : α, x     -- β → α → α
    #check λ (b : β) (x : α), x    -- β → α → α
    #check λ (g : β → γ) (f : α → β) (x : α), g (f x)
                                  -- (β → γ) → (α → β) → α → γ
    -- END

Lean lets us combine lambdas, so the second example is equivalent to the first. We can even abstract over the type:

.. code-block:: lean

    constants α β γ : Type
    constant f : α → β
    constant g : β → γ
    constant b : β

    -- BEGIN
    #check λ (α β : Type) (b : β) (x : α), x
    #check λ (α β γ : Type) (g : β → γ) (f : α → β) (x : α), g (f x)
    -- END

The last expression, for example, denotes the function that takes three types, ``α``, ``β``, and ``γ``, and two functions, ``g : β → γ`` and ``f : α → β``, and returns the composition of ``g`` and ``f``. (Making sense of the type of this function requires an understanding of dependent products, which we will explain below.) Within a lambda expression ``λ x : α, t``, the variable ``x`` is a "bound variable": it is really a placeholder, whose "scope" does not extend beyond ``t``. For example, the variable ``b`` in the expression ``λ (b : β) (x : α), x`` has nothing to do with the constant ``b`` declared earlier. In fact, the expression denotes the same function as ``λ (u : β) (z : α), z``. Formally, the expressions that are the same up to a renaming of bound variables are called *alpha equivalent*, and are considered "the same." Lean recognizes this equivalence.

Notice that applying a term ``t : α → β`` to a term ``s : α`` yields an expression ``t s : β``. Returning to the previous example and renaming bound variables for clarity, notice the types of the following expressions:

.. code-block:: lean

    constants α β γ : Type
    constant f : α → β
    constant g : β → γ
    constant h : α → α
    constants (a : α) (b : β)

    #check (λ x : α, x) a                -- α
    #check (λ x : α, b) a                -- β
    #check (λ x : α, b) (h a)            -- β
    #check (λ x : α, g (f x)) (h (h a))  -- γ

    #check (λ (v : β → γ) (u : α → β) x, v (u x)) g f a   -- γ

    #check (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
            v (u x)) α β γ g f a        -- γ

As expected, the expression ``(λ x : α, x) a`` has type ``α``. In fact, more should be true: applying the expression ``(λ x : α, x)`` to ``a`` should "return" the value ``a``. And, indeed, it does:

.. code-block:: lean

    constants α β γ : Type
    constant f : α → β
    constant g : β → γ
    constant h : α → α
    constants (a : α) (b : β)

    #reduce (λ x : α, x) a                -- a
    #reduce (λ x : α, b) a                -- b
    #reduce (λ x : α, b) (h a)            -- b
    #reduce (λ x : α, g (f x)) a          -- g (f a)

    #reduce (λ (v : β → γ) (u : α → β) x, v (u x)) g f a   -- g (f a)

    #reduce (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
           v (u x)) α β γ g f a        -- g (f a)

The command ``#reduce`` tells Lean to evaluate an expression by *reducing* it to normal form, which is to say, carrying out all the computational reductions that are sanctioned by the underlying logic. The process of simplifying an expression ``(λ x, t)s`` to ``t[s/x]`` -- that is, ``t`` with ``s`` substituted for the variable ``x`` -- is known as *beta reduction*, and two terms that beta reduce to a common term are called *beta equivalent*. But the ``#reduce`` command carries out other forms of reduction as well:

.. code-block:: lean

    constants m n : nat
    constant b : bool

    #print "reducing pairs"
    #reduce (m, n).1        -- m
    #reduce (m, n).2        -- n

    #print "reducing boolean expressions"
    #reduce tt && ff        -- ff
    #reduce ff && b         -- ff
    #reduce b && ff         -- bool.rec ff ff b

    #print "reducing arithmetic expressions"
    #reduce n + 0           -- n
    #reduce n + 2           -- nat.succ (nat.succ n)
    #reduce 2 + 3           -- 5

In a later chapter, we will explain how these terms are evaluated. For now, we only wish to emphasize that this is an important feature of dependent type theory: every term has a computational behavior, and supports a notion of reduction, or *normalization*. In principle, two terms that reduce to the same value are called *definitionally equal*. They are considered "the same" by the underlying logical framework, and Lean does its best to recognize and support these identifications.

It is this computational behavior that makes it possible to use Lean as a programming language as well. Indeed, Lean extracts bytecode from terms in a computationally pure fragment of the logical framework, and can evaluate them quite efficiently:

.. code-block:: lean

    #eval 12345 * 54321

In contrast, the ``#reduce`` command relies on Lean's trusted kernel, the part of Lean that is responsible for checking and verifying the correctness of expressions and proofs. As such, the ``#reduce`` command is more trustworthy, but far less efficient. We will have more to say about ``#eval`` in :numref:`Chapter %s <axioms_and_computation>`, and it will play a central role in `Programming in Lean <https://leanprover.github.io/programming_in_lean>`__. In this tutorial, however, we will generally rely on ``#reduce`` instead.

.. _introducing_definitions:

Introducing Definitions
-----------------------

As we have noted above, declaring constants in the Lean environment is a good way to postulate new objects to experiment with, but most of the time what we really want to do is *define* objects in Lean and prove things about them. The ``def`` command provides one important way of defining new objects.

.. code-block:: lean

    def foo : (ℕ → ℕ) → ℕ := λ f, f 0

    #check foo    -- (ℕ → ℕ) → ℕ
    #print foo    -- λ (f : ℕ → ℕ), f 0

We can omit the type when Lean has enough information to infer it:

.. code-block:: lean

    def foo' := λ f : ℕ → ℕ, f 0

The general form of a definition is ``def foo : α := bar``. Lean can usually infer the type ``α``, but it is often a good idea to write it explicitly. This clarifies your intention, and Lean will flag an error if the right-hand side of the definition does not have the right type.

Lean also allows us to use an alternative format that puts the abstracted variables before the colon and omits the lambda:

.. code-block:: lean

    def double (x : ℕ) : ℕ := x + x
    #print double
    #check double 3
    #reduce double 3    -- 6

    def square (x : ℕ) := x * x
    #print square
    #check square 3
    #reduce square 3    -- 9

    def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)

    #reduce do_twice double 2    -- 8

These definitions are equivalent to the following:

.. code-block:: lean

    def double : ℕ → ℕ := λ x, x + x
    def square : ℕ → ℕ := λ x, x * x
    def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

We can even use this approach to specify arguments that are types:

.. code-block:: lean

    def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : 
      γ :=
    g (f x)

As an exercise, we encourage you to use ``do_twice`` and ``double`` to define functions that quadruple their input, and multiply the input by 8. As a further exercise, we encourage you to try defining a function ``Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)`` which applies *its* argument twice, so that ``Do_Twice do_twice`` is a function that applies its input four times. Then evaluate ``Do_Twice do_twice double 2``.

Above, we discussed the process of "currying" a function, that is, taking a function ``f (a, b)`` that takes an ordered pair as an argument, and recasting it as a function ``f' a b`` that takes two arguments successively. As another exercise, we encourage you to complete the following definitions, which "curry" and "uncurry" a
function.

.. code-block:: lean

    def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := sorry

    def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := sorry

Local Definitions
-----------------

Lean also allows you to introduce "local" definitions using the ``let`` construct. The expression ``let a := t1 in t2`` is definitionally equal to the result of replacing every occurrence of ``a`` in ``t2`` by ``t1``.

.. code-block:: lean

    #check let y := 2 + 2 in y * y   -- ℕ
    #reduce  let y := 2 + 2 in y * y   -- 16

    def t (x : ℕ) : ℕ :=
    let y := x + x in y * y

    #reduce t 2   -- 16

Here, ``t`` is definitionally equal to the term ``(x + x) * (x + x)``. You can combine multiple assignments in a single ``let`` statement:

.. code-block:: lean

    #check   let y := 2 + 2, z := y + y in z * z   -- ℕ
    #reduce  let y := 2 + 2, z := y + y in z * z   -- 64

Notice that the meaning of the expression ``let a := t1 in t2`` is very similar to the meaning of ``(λ a, t2) t1``, but the two are not the same. In the first expression, you should think of every instance of ``a`` in ``t2`` as a syntactic abbreviation for ``t1``. In the second expression, ``a`` is a variable, and the expression ``λ a, t2`` has to make sense independently of the value of ``a``. The ``let`` construct is a stronger means of abbreviation, and there are expressions of the form ``let a := t1 in t2`` that cannot be expressed as ``(λ a, t2) t1``. As an exercise, try to understand why the definition of ``foo`` below type checks, but the definition of ``bar`` does not.

.. code-block:: lean

    def foo := let a := nat  in λ x : a, x + 2

    /-
    def bar := (λ a, λ x : a, x + 2) nat
    -/

.. _variables_and_sections:

Variables and Sections
----------------------

This is a good place to introduce some organizational features of Lean that are not a part of the axiomatic framework *per se*, but make it possible to work in the framework more efficiently.

We have seen that the ``constant`` command allows us to declare new objects, which then become part of the global context. Declaring new objects in this way is somewhat crass. Lean enables us to *define* all of the mathematical objects we need, and *declaring* new objects willy-nilly is therefore somewhat lazy. In the words of Bertrand Russell, it has all the advantages of theft over honest toil. We will see in the next chapter that it is also somewhat dangerous: declaring a new constant is tantamount to declaring an axiomatic extension of our foundational system, and may result in inconsistency.

So far, in this tutorial, we have used the ``constant`` command to create "arbitrary" objects to work with in our examples. For example, we have declared types ``α``, ``β``, and ``γ`` to populate our context. This can be avoided, using implicit or explicit lambda abstraction in our definitions to declare such objects "locally":

.. code-block:: lean

    def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) :
      γ := g (f x)

    def do_twice (α : Type) (h : α → α) (x : α) : α := h (h x)

    def do_thrice (α : Type) (h : α → α) (x : α) : α := h (h (h x))

Repeating declarations in this way can be tedious, however. Lean provides us with the ``variable`` and ``variables`` commands to make such declarations look global:

.. code-block:: lean

    variables (α β γ : Type)

    def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
    def do_twice (h : α → α) (x : α) : α := h (h x)
    def do_thrice (h : α → α) (x : α) : α := h (h (h x))

We can declare variables of any type, not just ``Type`` itself:

.. code-block:: lean

    variables (α β γ : Type)
    variables (g : β → γ) (f : α → β) (h : α → α)
    variable x : α

    def compose := g (f x)
    def do_twice := h (h x)
    def do_thrice := h (h (h x))

    #print compose
    #print do_twice
    #print do_thrice

Printing them out shows that all three groups of definitions have exactly the same effect.

The ``variable`` and ``variables`` commands look like the ``constant`` and ``constants`` commands we have used above, but there is an important difference. Rather than creating permanent entities, the former commands simply instruct Lean to insert the declared variables as bound variables in definitions that refer to them. Lean is smart enough to figure out which variables are used explicitly or implicitly in a definition. We can therefore proceed as though ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, and ``x`` are fixed objects when we write our definitions, and let Lean abstract the definitions for us automatically.

When declared in this way, a variable stays in scope until the end of the file we are working on, and we cannot declare another variable with the same name. Sometimes, however, it is useful to limit the scope of a variable. For that purpose, Lean provides the notion of a ``section``:

.. code-block:: lean

    section useful
      variables (α β γ : Type)
      variables (g : β → γ) (f : α → β) (h : α → α)
      variable x : α

      def compose := g (f x)
      def do_twice := h (h x)
      def do_thrice := h (h (h x))
    end useful

When the section is closed, the variables go out of scope, and become nothing more than a distant memory.

You do not have to indent the lines within a section, since Lean treats any string of returns, spaces, and tabs equivalently as whitespace. Nor do you have to name a section, which is to say, you can use an anonymous ``section`` / ``end`` pair. If you do name a section, however, you have to close it using the same name. Sections can also be nested, which allows you to declare new variables incrementally.

We will see in :numref:`Chapter %s <interacting_with_lean>` that, as a scoping mechanism, sections govern more than just variables; other commands have effects that are only operant in the current section. Similarly, if we use the ``open`` command inside a section, it only remains in effect until that section is closed.

.. _namespaces:

Namespaces
----------

Lean provides us with the ability to group definitions into nested, hierarchical *namespaces*:

.. code-block:: lean

    namespace foo
      def a : ℕ := 5
      def f (x : ℕ) : ℕ := x + 7

      def fa : ℕ := f a
      def ffa : ℕ := f (f a)

      #print "inside foo"

      #check a
      #check f
      #check fa
      #check ffa
      #check foo.fa
    end foo

    #print "outside the namespace"

    -- #check a  -- error
    -- #check f  -- error
    #check foo.a
    #check foo.f
    #check foo.fa
    #check foo.ffa

    open foo

    #print "opened foo"

    #check a
    #check f
    #check fa
    #check foo.fa

When we declare that we are working in the namespace ``foo``, every identifier we declare has a full name with prefix "``foo.``" Within the namespace, we can refer to identifiers by their shorter names, but once we end the namespace, we have to use the longer names.

The ``open`` command brings the shorter names into the current context. Often, when we import a theory file, we will want to open one or more of the namespaces it contains, to have access to the short identifiers. But sometimes we will want to leave this information hidden, for example, when they conflict with identifiers in another namespace we want to use. Thus namespaces give us a way to manage our working environment.

For example, Lean groups definitions and theorems involving lists into a namespace ``list``.

.. code-block:: lean

    #check list.nil
    #check list.cons
    #check list.append

We will discuss their types, below. The command ``open list`` allows us to use the shorter names:

.. code-block:: lean

    open list

    #check nil
    #check cons
    #check append

Like sections, namespaces can be nested:

.. code-block:: lean

    namespace foo
      def a : ℕ := 5
      def f (x : ℕ) : ℕ := x + 7

      def fa : ℕ := f a

      namespace bar
        def ffa : ℕ := f (f a)

        #check fa
        #check ffa
      end bar

      #check fa
      #check bar.ffa
    end foo

    #check foo.fa
    #check foo.bar.ffa

    open foo

    #check fa
    #check bar.ffa

Namespaces that have been closed can later be reopened, even in another file:

.. code-block:: lean

    namespace foo
      def a : ℕ := 5
      def f (x : ℕ) : ℕ := x + 7

      def fa : ℕ := f a
    end foo

    #check foo.a
    #check foo.f

    namespace foo
      def ffa : ℕ := f (f a)
    end foo

Like sections, nested namespaces have to be closed in the order they are opened. Also, a namespace cannot be declared within a section; namespaces have to live on the outer levels.

Namespaces and sections serve different purposes: namespaces organize data and sections declare variables for insertion in theorems. In many respects, however, a ``namespace ... end`` block behaves the same as a ``section ... end`` block. In particular, if you use the ``variable`` command within a namespace, its scope is limited to the namespace. Similarly, if you use an ``open`` command within a namespace, its effects disappear when the namespace is closed.

.. _dependent_types:

Dependent Types
---------------

You have now seen one way of defining functions and objects in Lean, and we will gradually introduce you to many more. But an important goal in Lean is to *prove* things about the objects we define, and the next chapter will introduce you to Lean's mechanisms for stating theorems and constructing proofs. Meanwhile, let us remain on the topic of defining objects in dependent type theory for just a moment longer. In this section, we will explain what makes dependent type theory *dependent*, and why dependent types are useful.

The short explanation is that what makes dependent type theory dependent is that types can depend on parameters. You have already seen a nice example of this: the type ``list α`` depends on the argument ``α``, and this dependence is what distinguishes ``list ℕ`` and ``list bool``. For another example, consider the type ``vec α n``, the type of vectors of elements of ``α`` of length ``n``. This type depends on *two* parameters: the type ``α : Type`` of the elements in the vector and the length ``n : ℕ``.

Suppose we wish to write a function ``cons`` which inserts a new element at the head of a list. What type should ``cons`` have? Such a function is *polymorphic*: we expect the ``cons`` function for ``ℕ``, ``bool``, or an arbitrary type ``α`` to behave the same way. So it makes sense to take the type to be the first argument to ``cons``, so that for any type, ``α``, ``cons α`` is the insertion function for lists of type ``α``. In other words, for every ``α``, ``cons α`` is the function that takes an element ``a : α`` and a list ``l : list α``, and returns a new list, so we have ``cons α a l : list α``.

It is clear that ``cons α`` should have type ``α → list α → list α``. But what type should ``cons`` have? A first guess might be ``Type → α → list α → list α``, but, on reflection, this does not make sense: the ``α`` in this expression does not refer to anything, whereas it should refer to the argument of type ``Type``. In other words, *assuming* ``α : Type`` is the first argument to the function, the type of the next two elements are ``α`` and ``list α``. These types vary depending on the first argument, ``α``.

This is an instance of a *Pi type*, or *dependent function type*. Given ``α : Type`` and ``β : α → Type``, think of ``β`` as a family of types over ``α``, that is, a type ``β a`` for each ``a : α``. In that case, the type ``Π x : α, β x`` denotes the type of functions ``f`` with the property that, for each ``a : α``, ``f a`` is an element of ``β a``. In other words, the type of the value returned by ``f`` depends on its input.

Notice that ``Π x : α, β`` makes sense for any expression ``β : Type``. When the value of ``β`` depends on ``x`` (as does, for example, the expression ``β x`` in the previous paragraph), ``Π x : α, β`` denotes a dependent function type. When ``β`` doesn't depend on ``x``, ``Π x : α, β`` is no different from the type ``α → β``. Indeed, in dependent type theory (and in Lean), the Pi construction is fundamental, and ``α → β`` is just notation for ``Π x : α, β`` when ``β`` does not depend on ``x``.

Returning to the example of lists, we can model some basic list operations as follows. We use ``namespace hidden`` to avoid a naming conflict with the ``list`` type defined in the standard library.

.. code-block:: lean

    namespace hidden

    universe u

    constant list   : Type u → Type u

    constant cons   : Π α : Type u, α → list α → list α
    constant nil    : Π α : Type u, list α
    constant head   : Π α : Type u, list α → α
    constant tail   : Π α : Type u, list α → list α
    constant append : Π α : Type u, list α → list α → list α

    end hidden

You can enter the symbol ``Π`` by typing ``\Pi``. Here, ``nil`` is intended to denote the empty list, ``head`` and ``tail`` return the first element of a list and the remainder, respectively. The constant ``append`` is intended to denote the function that concatenates two lists.

We emphasize that these constant declarations are only for the purposes of illustration. The ``list`` type and all these operations are, in fact, *defined* in Lean's standard library, and are proved to have the expected properties. Moreover, as the next example shows, the types indicated above are essentially the types of the objects that are defined in the library. (We will explain the ``@`` symbol and the difference between the round and curly brackets momentarily.)

.. code-block:: lean

    open list

    #check list     -- Type u_1 → Type u_1

    #check @cons    -- Π {α : Type u_1}, α → list α → list α
    #check @nil     -- Π {α : Type u_1}, list α
    #check @head    -- Π {α : Type u_1} [_inst_1 : inhabited α], list α → α
    #check @tail    -- Π {α : Type u_1}, list α → list α
    #check @append  -- Π {α : Type u_1}, list α → list α → list α

There is a subtlety in the definition of ``head``: the type ``α`` is required to have at least one element, and when passed the empty list, the function must determine a default element of the relevant type. We will explain how this is done in :numref:`Chapter %s <type_classes>`.

Vector operations are handled similarly:

.. code-block:: lean

    universe u
    constant vec : Type u → ℕ → Type u

    namespace vec
      constant empty : Π α : Type u, vec α 0
      constant cons :
        Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
      constant append :
        Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
    end vec

In the coming chapters, you will come across many instances of dependent types. Here we will mention just one more important and illustrative example, the *Sigma types*, ``Σ x : α, β x``, sometimes also known as *dependent products*. These are, in a sense, companions to the Pi types. The type ``Σ x : α, β x`` denotes the type of pairs ``sigma.mk a b`` where ``a : α`` and ``b : β a``.

Just as Pi types ``Π x : α, β x`` generalize the notion of a function type ``α → β`` by allowing ``β`` to depend on ``α``, Sigma types ``Σ x : α, β x`` generalize the cartesian product ``α × β`` in the same way: in the expression ``sigma.mk a b``, the type of the second element of the pair, ``b : β a``, depends on the first element of the pair, ``a : α``.

.. code-block:: lean

    variable α : Type
    variable β : α → Type
    variable a : α
    variable b : β a

    #check sigma.mk a b      -- Σ (a : α), β a
    #check (sigma.mk a b).1  -- α
    #check (sigma.mk a b).2  -- β (sigma.snd (sigma.mk a b))

    #reduce  (sigma.mk a b).1  -- a
    #reduce  (sigma.mk a b).2  -- b

Notice that the expressions ``(sigma.mk a b).1`` and ``(sigma.mk a b).2`` are short for ``sigma.fst (sigma.mk a b)`` and ``sigma.snd (sigma.mk a b)``, respectively, and that these reduce to ``a`` and ``b``, respectively.

.. _implicit_arguments:

Implicit Arguments
------------------

Suppose we have an implementation of lists as described above.

.. code-block:: lean

    namespace hidden
    universe u
    constant list : Type u → Type u

    namespace list
      constant cons   : Π α : Type u, α → list α → list α
      constant nil    : Π α : Type u, list α
      constant append : Π α : Type u, list α → list α → list α
    end list
    end hidden

Then, given a type ``α``, some elements of ``α``, and some lists of elements of ``α``, we can construct new lists using the constructors.

.. code-block:: lean

    namespace hidden
    universe u
    constant list : Type u → Type u

    namespace list
      constant cons   : Π α : Type u, α → list α → list α
      constant nil    : Π α : Type u, list α
      constant append : Π α : Type u, list α → list α → list α
    end list

    -- BEGIN
    open hidden.list

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    #check cons α a (nil α)
    #check append α (cons α a (nil α)) l1
    #check append α (append α (cons α a (nil α)) l1) l2
    -- END
    end hidden

Because the constructors are polymorphic over types, we have to insert the type ``α`` as an argument repeatedly. But this information is redundant: one can infer the argument ``α`` in ``cons α a (nil α)`` from the fact that the second argument, ``a``, has type ``α``. One can similarly infer the argument in ``nil α``, not from anything else in that expression, but from the fact that it is sent as an argument to the function ``cons``, which expects an element of type ``list α`` in that position.

This is a central feature of dependent type theory: terms carry a lot of information, and often some of that information can be inferred from the context. In Lean, one uses an underscore, ``_``, to specify that the system should fill in the information automatically. This is known as an "implicit argument."

.. code-block:: lean

    namespace hidden
    universe u
    constant list : Type u → Type u

    namespace list
      constant cons   : Π α : Type u, α → list α → list α
      constant nil    : Π α : Type u, list α
      constant append : Π α : Type u, list α → list α → list α
    end list

    open hidden.list

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    -- BEGIN
    #check cons _ a (nil _)
    #check append _ (cons _ a (nil _)) l1
    #check append _ (append _ (cons _ a (nil _)) l1) l2
    -- END
    end hidden

It is still tedious, however, to type all these underscores. When a function takes an argument that can generally be inferred from context, Lean allows us to specify that this argument should, by default, be left implicit. This is done by putting the arguments in curly braces, as follows:

.. code-block:: lean

    namespace hidden
    universe u
    constant list : Type u → Type u

    -- BEGIN
    namespace list
      constant cons   : Π {α : Type u}, α → list α → list α
      constant nil    : Π {α : Type u}, list α
      constant append : Π {α : Type u}, list α → list α → list α
    end list

    open hidden.list

    variable  α : Type
    variable  a : α
    variables l1 l2 : list α

    #check cons a nil
    #check append (cons a nil) l1
    #check append (append (cons a nil) l1) l2
    -- END
    end hidden

All that has changed are the braces around ``α : Type u`` in the declaration of the variables. We can also use this device in function definitions:

.. code-block:: lean

    universe u
    def ident {α : Type u} (x : α) := x

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident      -- ?M_1 → ?M_1
    #check ident a    -- α
    #check ident b    -- β

This makes the first argument to ``ident`` implicit. Notationally, this hides the specification of the type, making it look as though ``ident`` simply takes an argument of any type. In fact, the function ``id`` is defined in the standard library in exactly this way. We have chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the ``variables`` command:

.. code-block:: lean

    universe u

    section
      variable {α : Type u}
      variable x : α
      def ident := x
    end

    variables α β : Type u
    variables (a : α) (b : β)

    #check ident
    #check ident a
    #check ident b

This definition of ``ident`` here has the same effect as the one above.

Lean has very complex mechanisms for instantiating implicit arguments, and we will see that they can be used to infer function types, predicates, and even proofs. The process of instantiating these "holes," or "placeholders," in a term is often known as *elaboration*. The presence of implicit arguments means that at times there may be insufficient information to fix the meaning of an expression precisely. An expression like ``id`` or ``list.nil`` is said to be *polymorphic*, because it can take on different meanings in different contexts.

One can always specify the type ``T`` of an expression ``e`` by writing ``(e : T)``. This instructs Lean's elaborator to use the value ``T`` as the type of ``e`` when trying to resolve implicit arguments. In the second pair of examples below, this mechanism is used to specify the desired types of the expressions ``id`` and ``list.nil``:

.. code-block:: lean

    #check list.nil             -- list ?M1
    #check id                   -- ?M1 → ?M1

    #check (list.nil : list ℕ)  -- list ℕ
    #check (id : ℕ → ℕ)         -- ℕ → ℕ

Numerals are overloaded in Lean, but when the type of a numeral cannot be inferred, Lean assumes, by default, that it is a natural number. So the expressions in the first two ``#check`` commands below are elaborated in the same way, whereas the third ``#check`` command interprets ``2`` as an integer.

.. code-block:: lean

    #check 2            -- ℕ
    #check (2 : ℕ)      -- ℕ
    #check (2 : ℤ)      -- ℤ

Sometimes, however, we may find ourselves in a situation where we have declared an argument to a function to be implicit, but now want to provide the argument explicitly. If ``foo`` is such a function, the notation ``@foo`` denotes the same function with all the arguments made explicit.

.. code-block:: lean

    variables α β : Type
    variables (a : α) (b : β)

    -- BEGIN
    #check @id        -- Π {α : Type u_1}, α → α
    #check @id α      -- α → α
    #check @id β      -- β → β
    #check @id α a    -- α
    #check @id β b    -- β
    -- END

Notice that now the first ``#check`` command gives the type of the identifier, ``id``, without inserting any placeholders. Moreover, the output indicates that the first argument is implicit.

Exercises
---------

#. Define the function ``Do_Twice``, as described in :numref:`introducing_definitions`.

#. Define the functions ``curry`` and ``uncurry``, as described in :numref:`introducing_definitions`.

#. Above, we used the example ``vec α n`` for vectors of elements of type ``α`` of length ``n``. Declare a constant ``vec_add`` that could represent a function that adds two vectors of natural numbers of the same length, and a constant ``vec_reverse`` that can represent a function that reverses its argument. Use implicit arguments for parameters that can be inferred. Declare some variables and check some expressions involving the constants that you have declared.

#. Similarly, declare a constant ``matrix`` so that ``matrix α m n`` could represent the type of ``m`` by ``n`` matrices. Declare some constants to represent functions on this type, such as matrix addition and multiplication, and (using ``vec``) multiplication of a matrix by a vector. Once again, declare some variables and check some expressions involving the constants that you have declared.
