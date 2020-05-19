.. _propositions_and_proofs:

Propositions and Proofs
=======================

By now, you have seen some ways of defining objects and functions in Lean. In this chapter, we will begin to explain how to write mathematical assertions and proofs in the language of dependent type theory as well.

Propositions as Types
---------------------

One strategy for proving assertions about objects defined in the language of dependent type theory is to layer an assertion language and a proof language on top of the definition language. But there is no reason to multiply languages in this way: dependent type theory is flexible and expressive, and there is no reason we cannot represent assertions and proofs in the same general framework.

For example, we could introduce a new type, ``Prop``, to represent propositions, and introduce constructors to build new propositions from others.

.. code-block:: lean

    namespace hidden

    -- BEGIN
    constant and : Prop → Prop → Prop
    constant or : Prop → Prop → Prop
    constant not : Prop → Prop
    constant implies : Prop → Prop → Prop

    variables p q r : Prop
    #check and p q                      -- Prop
    #check or (and p q) r               -- Prop
    #check implies (and p q) (and q p)  -- Prop
    -- END

    end hidden

We could then introduce, for each element ``p : Prop``, another type ``Proof p``, for the type of proofs of ``p``. An "axiom" would be a constant of such a type.

.. code-block:: lean

    namespace hidden

    constant and : Prop → Prop → Prop
    constant or : Prop → Prop → Prop
    constant not : Prop → Prop
    constant implies : Prop → Prop → Prop

    -- BEGIN
    constant Proof : Prop → Type

    constant and_comm : Π p q : Prop,
      Proof (implies (and p q) (and q p))

    variables p q : Prop
    #check and_comm p q      -- Proof (implies (and p q) (and q p))
    -- END

    end hidden

In addition to axioms, however, we would also need rules to build new proofs from old ones. For example, in many proof systems for propositional logic, we have the rule of modus ponens:

    From a proof of ``implies p q`` and a proof of ``p``, we obtain a proof of ``q``.

We could represent this as follows:

.. code-block:: lean

    namespace hidden

    constant implies : Prop → Prop → Prop
    constant Proof : Prop → Type

    -- BEGIN
    constant modus_ponens :
      Π p q : Prop, Proof (implies p q) →  Proof p → Proof q
    -- END

    end hidden

Systems of natural deduction for propositional logic also typically rely on the following rule:

    Suppose that, assuming ``p`` as a hypothesis, we have a proof of ``q``. Then we can "cancel" the hypothesis and obtain a proof of ``implies p q``.

We could render this as follows:

.. code-block:: lean

    namespace hidden

    constant implies : Prop → Prop → Prop
    constant Proof : Prop → Type

    -- BEGIN
    constant implies_intro :
      Π p q : Prop, (Proof p → Proof q) → Proof (implies p q).
    -- END

    end hidden

This approach would provide us with a reasonable way of building assertions and proofs. Determining that an expression ``t`` is a correct proof of assertion ``p`` would then simply be a matter of checking that ``t`` has type ``Proof p``.

Some simplifications are possible, however. To start with, we can avoid writing the term ``Proof`` repeatedly by conflating ``Proof p`` with ``p`` itself. In other words, whenever we have ``p : Prop``, we can interpret ``p`` as a type, namely, the type of its proofs. We can then read ``t : p`` as the assertion that ``t`` is a proof of ``p``.

Moreover, once we make this identification, the rules for implication show that we can pass back and forth between ``implies p q`` and ``p → q``. In other words, implication between propositions ``p`` and ``q`` corresponds to having a function that takes any element of ``p`` to an element of ``q``. As a result, the introduction of the connective ``implies`` is entirely redundant: we can use the usual function space constructor ``p → q`` from dependent type theory as our notion of implication.

This is the approach followed in the Calculus of Constructions, and hence in Lean as well. The fact that the rules for implication in a proof system for natural deduction correspond exactly to the rules governing abstraction and application for functions is an instance of the *Curry-Howard isomorphism*, sometimes known as the *propositions-as-types* paradigm. In fact, the type ``Prop`` is syntactic sugar for ``Sort 0``, the very bottom of the type hierarchy described in the last chapter. Moreover, ``Type u`` is also just syntactic sugar for ``Sort (u+1)``. ``Prop`` has some special features, but like the other type universes, it is closed under the arrow constructor: if we have ``p q : Prop``, then ``p → q : Prop``.

There are at least two ways of thinking about propositions as types. To some who take a constructive view of logic and mathematics, this is a faithful rendering of what it means to be a proposition: a proposition ``p`` represents a sort of data type, namely, a specification of the type of data that constitutes a proof. A proof of ``p`` is then simply an object ``t : p`` of the right type.

Those not inclined to this ideology can view it, rather, as a simple coding trick. To each proposition ``p`` we associate a type that is empty if ``p`` is false and has a single element, say ``*``, if ``p`` is true. In the latter case, let us say that (the type associated with) ``p`` is *inhabited*. It just so happens that the rules for function application and abstraction can conveniently help us keep track of which elements of ``Prop`` are inhabited. So constructing an element ``t : p`` tells us that ``p`` is indeed true. You can think of the inhabitant of ``p`` as being the "fact that ``p`` is true." A proof of ``p → q`` uses "the fact that ``p`` is true" to obtain "the fact that ``q`` is true."

Indeed, if ``p : Prop`` is any proposition, Lean's kernel treats any two elements ``t1 t2 : p`` as being definitionally equal, much the same way as it treats ``(λ x, t)s`` and ``t[s/x]`` as definitionally equal. This is known as *proof irrelevance,* and is consistent with the interpretation in the last paragraph. It means that even though we can treat proofs ``t : p`` as ordinary objects in the language of dependent type theory, they carry no information beyond the fact that ``p`` is true.

The two ways we have suggested thinking about the propositions-as-types paradigm differ in a fundamental way. From the constructive point of view, proofs are abstract mathematical objects that are *denoted* by suitable expressions in dependent type theory. In contrast, if we think in terms of the coding trick described above, then the expressions themselves do not denote anything interesting. Rather, it is the fact that we can write them down and check that they are well-typed that ensures that the proposition in question is true. In other words, the expressions *themselves* are the proofs.

In the exposition below, we will slip back and forth between these two ways of talking, at times saying that an expression "constructs" or "produces" or "returns" a proof of a proposition, and at other times simply saying that it "is" such a proof. This is similar to the way that computer scientists occasionally blur the distinction between syntax and semantics by saying, at times, that a program "computes" a certain function, and at other times speaking as though the program "is" the function in question.

In any case, all that really matters is the bottom line. To formally express a mathematical assertion in the language of dependent type theory, we need to exhibit a term ``p : Prop``. To *prove* that assertion, we need to exhibit a term ``t : p``. Lean's task, as a proof assistant, is to help us to construct such a term, ``t``, and to verify that it is well-formed and has the correct type.

Working with Propositions as Types
----------------------------------

In the propositions-as-types paradigm, theorems involving only ``→`` can be proved using lambda abstraction and application. In Lean, the ``theorem`` command introduces a new theorem:

.. code-block:: lean

    constants p q : Prop

    theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

This looks exactly like the definition of the constant function in the last chapter, the only difference being that the arguments are elements of ``Prop`` rather than ``Type``. Intuitively, our proof of ``p → q → p`` assumes ``p`` and ``q`` are true, and uses the first hypothesis (trivially) to establish that the conclusion, ``p``, is true.

Note that the ``theorem`` command is really a version of the ``definition`` command: under the propositions and types correspondence, proving the theorem ``p → q → p`` is really the same as defining an element of the associated type. To the kernel type checker, there is no difference between the two.

There are a few pragmatic differences between definitions and theorems, however. In normal circumstances, it is never necessary to unfold the "definition" of a theorem; by proof irrelevance, any two proofs of that theorem are definitionally equal. Once the proof of a theorem is complete, typically we only need to know that the proof exists; it doesn't matter what the proof is. In light of that fact, Lean tags proofs as *irreducible*, which serves as a hint to the parser (more precisely, the *elaborator*) that there is generally no need to unfold it when processing a file. In fact, Lean is generally able to process and check proofs in parallel, since assessing the correctness of one proof does not require knowing the details of another.

As with definitions, the ``#print`` command will show you the proof of a theorem.

.. code-block:: lean

    constants p q : Prop

    -- BEGIN
    theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

    #print t1
    -- END

Notice that the lambda abstractions ``hp : p`` and ``hq : q`` can be viewed as temporary assumptions in the proof of ``t1``. Lean provides the alternative syntax ``assume`` for such a lambda abstraction:

.. code-block:: lean

    constants p q : Prop

    -- BEGIN
    theorem t1 : p → q → p :=
    assume hp : p,
    assume hq : q,
    hp
    -- END

Lean also allows us to specify the type of the final term ``hp``, explicitly, with a ``show`` statement.

.. code-block:: lean

    constants p q : Prop

    -- BEGIN
    theorem t1 : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp
    -- END

Adding such extra information can improve the clarity of a proof and help detect errors when writing a proof. The ``show`` command does nothing more than annotate the type, and, internally, all the presentations of ``t1`` that we have seen produce the same term. Lean also allows you to use the alternative syntax ``lemma`` instead of theorem:

.. code-block:: lean

    constants p q : Prop

    -- BEGIN
    lemma t1 : p → q → p :=
    assume hp : p,
    assume hq : q,
    show p, from hp
    -- END

As with ordinary definitions, we can move the lambda-abstracted variables to the left of the colon:

.. code-block:: lean

    constants p q : Prop

    -- BEGIN
    theorem t1 (hp : p) (hq : q) : p := hp

    #check t1    -- p → q → p
    -- END

Now we can apply the theorem ``t1`` just as a function application.

.. code-block:: lean

    constants p q : Prop

    theorem t1 (hp : p) (hq : q) : p := hp

    -- BEGIN
    axiom hp : p

    theorem t2 : q → p := t1 hp
    -- END

Here, the ``axiom`` command is alternative syntax for ``constant``. Declaring a "constant" ``hp : p`` is tantamount to declaring that ``p`` is true, as witnessed by ``hp``. Applying the theorem ``t1 : p → q → p`` to the fact ``hp : p`` that ``p`` is true yields the theorem ``t2 : q → p``.

Notice, by the way, that the original theorem ``t1`` is true for *any* propositions ``p`` and ``q``, not just the particular constants declared. So it would be more natural to define the theorem so that it quantifies over those, too:

.. code-block:: lean

    theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

    #check t1

The type of ``t1`` is now ``∀ p q : Prop, p → q → p``. We can read this as the assertion "for every pair of propositions ``p q``, we have ``p → q → p``." The symbol ``∀`` is alternate syntax for ``Π``, and later we will see how Pi types let us model universal quantifiers more generally. For example, we can move all parameters to the right of the colon:

.. code-block:: lean

    theorem t1 : ∀ (p q : Prop), p → q → p :=
    λ (p q : Prop) (hp : p) (hq : q), hp

If ``p`` and ``q`` have been declared as variables, Lean will generalize them for us automatically:

.. code-block:: lean

    variables p q : Prop

    theorem t1 : p → q → p := λ (hp : p) (hq : q), hp

In fact, by the propositions-as-types correspondence, we can declare the assumption ``hp`` that ``p`` holds, as another variable:

.. code-block:: lean

    variables p q : Prop
    variable  hp : p

    theorem t1 : q → p := λ (hq : q), hp

Lean detects that the proof uses ``hp`` and automatically adds ``hp : p`` as a premise. In all cases, the command ``#check t1`` still yields ``∀ p q : Prop, p → q → p``. Remember that this type can just as well be written ``∀ (p q : Prop) (hp : p) (hq :q), p``, since the arrow denotes nothing more than a Pi type in which the target does not depend on the bound variable.

When we generalize ``t1`` in such a way, we can then apply it to different pairs of propositions, to obtain different instances of the general theorem.

.. code-block:: lean

    theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

    variables p q r s : Prop

    #check t1 p q                -- p → q → p
    #check t1 r s                -- r → s → r
    #check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

    variable h : r → s
    #check t1 (r → s) (s → r) h  -- (s → r) → r → s

Once again, using the propositions-as-types correspondence, the variable ``h`` of type ``r → s`` can be viewed as the hypothesis, or premise, that ``r → s`` holds.

As another example, let us consider the composition function discussed in the last chapter, now with propositions instead of types.

.. code-block:: lean

    variables p q r s : Prop

    theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
    assume h₃ : p,
    show r, from h₁ (h₂ h₃)

As a theorem of propositional logic, what does ``t2`` say?

Note that it is often useful to use numeric unicode subscripts, entered as ``\0``, ``\1``, ``\2``, ..., for hypotheses, as we did in this example.

.. _propositional_logic:

Propositional Logic
-------------------

Lean defines all the standard logical connectives and notation. The propositional connectives come with the following notation:

+-------------------+-----------+------------------------------+--------------+
| Ascii             | Unicode   | Editor shortcut              | Definition   |
+-------------------+-----------+------------------------------+--------------+
| true              |           |                              | true         |
+-------------------+-----------+------------------------------+--------------+
| false             |           |                              | false        |
+-------------------+-----------+------------------------------+--------------+
| not               | ¬         | ``\not``, ``\neg``           | not          |
+-------------------+-----------+------------------------------+--------------+
| /\\               | ∧         | ``\and``                     | and          |
+-------------------+-----------+------------------------------+--------------+
| \\/               | ∨         | ``\or``                      | or           |
+-------------------+-----------+------------------------------+--------------+
| ->                | →         | ``\to``, ``\r``, ``\imp``    |              |
+-------------------+-----------+------------------------------+--------------+
| <->               | ↔         | ``\iff``, ``\lr``            | iff          |
+-------------------+-----------+------------------------------+--------------+

They all take values in ``Prop``.

.. code-block:: lean

    variables p q : Prop

    #check p → q → p ∧ q
    #check ¬p → p ↔ false
    #check p ∨ q → q ∨ p

The order of operations is as follows: unary negation ``¬`` binds most strongly, then ``∧``, then ``∨``, then ``→``, and finally ``↔``. For example, ``a ∧ b → c ∨ d ∧ e`` means ``(a ∧ b) → (c ∨ (d ∧ e))``. Remember that ``→`` associates to the right (nothing changes now that the arguments are elements of ``Prop``, instead of some other ``Type``), as do the other binary connectives. So if we have ``p q r : Prop``, the expression ``p → q → r`` reads "if ``p``, then if ``q``, then ``r``." This is just the "curried" form of ``p ∧ q → r``.

In the last chapter we observed that lambda abstraction can be viewed as an "introduction rule" for ``→``. In the current setting, it shows how to "introduce" or establish an implication. Application can be viewed as an "elimination rule," showing how to "eliminate" or use an implication in a proof. The other propositional connectives are defined in Lean's library in the file ``init.core`` (see :numref:`importing_files` for more information on the library hierarchy), and each connective comes with its canonical introduction and elimination rules.

.. _conjunction:

Conjunction
~~~~~~~~~~~

The expression ``and.intro h1 h2`` builds a proof of ``p ∧ q`` using proofs ``h1 : p`` and ``h2 : q``. It is common to describe ``and.intro`` as the *and-introduction* rule. In the next example we use ``and.intro`` to create a proof of ``p → q → p ∧ q``.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN

    example (hp : p) (hq : q) : p ∧ q := and.intro hp hq

    #check assume (hp : p) (hq : q), and.intro hp hq
    -- END

The ``example`` command states a theorem without naming it or storing it in the permanent context. Essentially, it just checks that the given term has the indicated type. It is convenient for illustration, and we will use it often.

The expression ``and.elim_left h`` creates a proof of ``p`` from a proof ``h : p ∧ q``. Similarly, ``and.elim_right h`` is a proof of ``q``. They are commonly known as the right and left *and-elimination* rules.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (h : p ∧ q) : p := and.elim_left h
    example (h : p ∧ q) : q := and.elim_right h
    -- END

Because they are so commonly used, the standard library provides the abbreviations ``and.left`` and ``and.right`` for ``and.elim_left`` and ``and.elim_right``, respectively.

We can now prove ``p ∧ q → q ∧ p`` with the following proof term.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (h : p ∧ q) : q ∧ p :=
    and.intro (and.right h) (and.left h)
    -- END

Notice that and-introduction and and-elimination are similar to the pairing and projection operations for the cartesian product. The difference is that given ``hp : p`` and ``hq : q``, ``and.intro hp hq`` has type ``p ∧ q : Prop``, while ``pair hp hq`` has type ``p × q : Type``. The similarity between ``∧`` and ``×`` is another instance of the Curry-Howard isomorphism, but in contrast to implication and the function space constructor, ``∧`` and ``×`` are treated separately in Lean. With the analogy, however, the proof we have just constructed is similar to a function that swaps the elements of a pair.

We will see in :numref:`Chapter %s <structures_and_records>` that certain types in Lean are *structures*, which is to say, the type is defined with a single canonical *constructor* which builds an element of the type from a sequence of suitable arguments. For every ``p q : Prop``, ``p ∧ q`` is an example: the canonical way to construct an element is to apply ``and.intro`` to suitable arguments ``hp : p`` and ``hq : q``. Lean allows us to use *anonymous constructor* notation ``⟨arg1, arg2, ...⟩`` in situations like these, when the relevant type is an inductive type and can be inferred from the context. In particular, we can often write ``⟨hp, hq⟩`` instead of ``and.intro hp hq``:

.. code-block:: lean

    variables p q : Prop
    variables  (hp : p) (hq : q)

    #check (⟨hp, hq⟩ : p ∧ q)

These angle brackets are obtained by typing ``\<`` and ``\>``, respectively. Alternatively, you can use ASCII equivalents ``(|`` and ``|)``:

.. code-block:: lean

    variables p q : Prop
    variables  (hp : p) (hq : q)

    example : p ∧ q := (|hp, hq|)

Lean provides another useful syntactic gadget. Given an expression ``e`` of an inductive type ``foo`` (possibly applied to some arguments), the notation ``e.bar`` is shorthand for ``foo.bar e``. This provides a convenient way of accessing functions without opening a namespace. For example, the following two expressions mean the same thing:

.. code-block:: lean

    variable l : list ℕ

    #check list.head l
    #check l.head

As a result, given ``h : p ∧ q``, we can write ``h.left`` for ``and.left h`` and ``h.right`` for ``and.right h``. We can therefore rewrite the sample proof above conveniently as follows:

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
    -- END

There is a fine line between brevity and obfuscation, and omitting information in this way can sometimes make a proof harder to read. But for straightforward constructions like the one above, when the type of ``h`` and the goal of the construction are salient, the notation is clean and effective.

It is common to iterate constructions like "and." Lean also allows you to flatten nested constructors that associate to the right, so that these two proofs are equivalent:

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (h : p ∧ q) : q ∧ p ∧ q:=
    ⟨h.right, ⟨h.left, h.right⟩⟩

    example (h : p ∧ q) : q ∧ p ∧ q:=
    ⟨h.right, h.left, h.right⟩
    -- END

This is often useful as well.

Disjunction
~~~~~~~~~~~

The expression ``or.intro_left q hp`` creates a proof of ``p ∨ q`` from a proof ``hp : p``. Similarly, ``or.intro_right p hq`` creates a proof for ``p ∨ q`` using a proof ``hq : q``. These are the left and right *or-introduction* rules.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (hp : p) : p ∨ q := or.intro_left q hp
    example (hq : q) : p ∨ q := or.intro_right p hq
    -- END

The *or-elimination* rule is slightly more complicated. The idea is that we can prove ``r`` from ``p ∨ q``, by showing that ``r`` follows from ``p`` and that ``r`` follows from ``q``. In other words, it is a proof by cases. In the expression ``or.elim hpq hpr hqr``, ``or.elim`` takes three arguments, ``hpq : p ∨ q``, ``hpr : p → r`` and ``hqr : q → r``, and produces a proof of ``r``. In the following example, we use ``or.elim`` to prove ``p ∨ q → q ∨ p``.

.. code-block:: lean

    variables p q r: Prop
    -- BEGIN
    example (h : p ∨ q) : q ∨ p :=
    or.elim h
      (assume hp : p,
        show q ∨ p, from or.intro_right q hp)
      (assume hq : q,
        show q ∨ p, from or.intro_left p hq)
    -- END

In most cases, the first argument of ``or.intro_right`` and ``or.intro_left`` can be inferred automatically by Lean. Lean therefore provides ``or.inr`` and ``or.inl`` as shorthand for ``or.intro_right _`` and ``or.intro_left _``. Thus the proof term above could be written more concisely:

.. code-block:: lean

    variables p q r: Prop
    -- BEGIN
    example (h : p ∨ q) : q ∨ p :=
    or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)
    -- END

Notice that there is enough information in the full expression for Lean to infer the types of ``hp`` and ``hq`` as well. But using the type annotations in the longer version makes the proof more readable, and can help catch and debug errors.

Because ``or`` has two constructors, we cannot use anonymous constructor notation. But we can still write ``h.elim`` instead of ``or.elim h``:

.. code-block:: lean

    variables p q r: Prop
    -- BEGIN
    example (h : p ∨ q) : q ∨ p :=
    h.elim
      (assume hp : p, or.inr hp)
      (assume hq : q, or.inl hq)
    -- END

Once again, you should exercise judgment as to whether such abbreviations enhance or diminish readability.

Negation and Falsity
~~~~~~~~~~~~~~~~~~~~

Negation, ``¬p``, is actually defined to be ``p → false``, so we obtain ``¬p`` by deriving a contradiction from ``p``. Similarly, the expression ``hnp hp`` produces a proof of ``false`` from ``hp : p`` and ``hnp : ¬p``. The next example uses both these rules to produce a proof of ``(p → q) → ¬q → ¬p``. (The symbol ``¬`` is produced by typing ``\not`` or ``\neg``.)

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (hpq : p → q) (hnq : ¬q) : ¬p :=
    assume hp : p,
    show false, from hnq (hpq hp)
    -- END

The connective ``false`` has a single elimination rule, ``false.elim``, which expresses the fact that anything follows from a contradiction. This rule is sometimes called *ex falso* (short for *ex falso sequitur quodlibet*), or the *principle of explosion*.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
    -- END

The arbitrary fact, ``q``, that follows from falsity is an implicit argument in ``false.elim`` and is inferred automatically. This pattern, deriving an arbitrary fact from contradictory hypotheses, is quite common, and is represented by ``absurd``.

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    example (hp : p) (hnp : ¬p) : q := absurd hp hnp
    -- END

Here, for example, is a proof of ``¬p → q → (q → p) → r``:

.. code-block:: lean

    variables p q r : Prop
    -- BEGIN
    example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp
    -- END

Incidentally, just as ``false`` has only an elimination rule, ``true`` has only an introduction rule, ``true.intro : true``, sometimes abbreviated ``trivial : true``. In other words, ``true`` is simply true, and has a canonical proof, ``trivial``.

Logical Equivalence
~~~~~~~~~~~~~~~~~~~

The expression ``iff.intro h1 h2`` produces a proof of ``p ↔ q`` from ``h1 : p → q`` and ``h2 : q → p``. The expression ``iff.elim_left h`` produces a proof of ``p → q`` from ``h : p ↔ q``. Similarly, ``iff.elim_right h`` produces a proof of ``q → p`` from ``h : p ↔ q``. Here is a proof of ``p ∧ q ↔ q ∧ p``:

.. code-block:: lean

    variables p q : Prop
    -- BEGIN
    theorem and_swap : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h : p ∧ q,
        show q ∧ p, from and.intro (and.right h) (and.left h))
      (assume h : q ∧ p,
        show p ∧ q, from and.intro (and.right h) (and.left h))

    #check and_swap p q    -- p ∧ q ↔ q ∧ p
    -- END

Because they represent a form of *modus ponens*, ``iff.elim_left`` and ``iff.elim_right`` can be abbreviated ``iff.mp`` and ``iff.mpr``, respectively. In the next example, we use that theorem to derive ``q ∧ p`` from ``p ∧ q``:

.. code-block:: lean

    variables p q : Prop

    theorem and_swap : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h : p ∧ q,
        show q ∧ p, from and.intro (and.right h) (and.left h))
      (assume h : q ∧ p,
        show p ∧ q, from and.intro (and.right h) (and.left h))

    -- BEGIN
    variable h : p ∧ q
    example : q ∧ p := iff.mp (and_swap p q) h
    -- END

We can use the anonymous constructor notation to construct a proof of ``p ↔ q`` from proofs of the forward and backward directions, and we can also use ``.`` notation with ``mp`` and ``mpr``. The previous examples can therefore be written concisely as follows:

.. code-block:: lean

    variables p q : Prop

    -- BEGIN
    theorem and_swap : p ∧ q ↔ q ∧ p :=
    ⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩

    example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
    -- END

Introducing Auxiliary Subgoals
------------------------------

This is a good place to introduce another device Lean offers to help structure long proofs, namely, the ``have`` construct, which introduces an auxiliary subgoal in a proof. Here is a small example, adapted from the last section:

.. code-block:: lean

    variables p q : Prop

    example (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.left h,
    have hq : q, from and.right h,
    show q ∧ p, from and.intro hq hp

Internally, the expression ``have h : p, from s, t`` produces the term ``(λ (h : p), t) s``. In other words, ``s`` is a proof of ``p``, ``t`` is a proof of the desired conclusion assuming ``h : p``, and the two are combined by a lambda abstraction and application. This simple device is extremely useful when it comes to structuring long proofs, since we can use intermediate ``have``'s as stepping stones leading to the final goal.

Lean also supports a structured way of reasoning backwards from a goal, which models the "suffices to show" construction in ordinary mathematics. The next example simply permutes the last two lines in the previous proof.

.. code-block:: lean

    variables p q : Prop

    example (h : p ∧ q) : q ∧ p :=
    have hp : p, from and.left h,
    suffices hq : q, from and.intro hq hp,
    show q, from and.right h

Writing ``suffices hq : q`` leaves us with two goals. First, we have to show that it indeed suffices to show ``q``, by proving the original goal of ``q ∧ p`` with the additional hypothesis ``hq : q``. Finally, we have to show ``q``.

.. _classical_logic:

Classical Logic
---------------

The introduction and elimination rules we have seen so far are all constructive, which is to say, they reflect a computational understanding of the logical connectives based on the propositions-as-types correspondence. Ordinary classical logic adds to this the law of the excluded middle, ``p ∨ ¬p``. To use this principle, you have to open the classical namespace.

.. code-block:: lean

    open classical

    variable p : Prop
    #check em p

Intuitively, the constructive "or" is very strong: asserting ``p ∨ q`` amounts to knowing which is the case. If ``RH`` represents the Riemann hypothesis, a classical mathematician is willing to assert ``RH ∨ ¬RH``, even though we cannot yet assert either disjunct.

One consequence of the law of the excluded middle is the principle of double-negation elimination:

.. code-block:: lean

    open classical

    -- BEGIN
    theorem dne {p : Prop} (h : ¬¬p) : p :=
    or.elim (em p)
      (assume hp : p, hp)
      (assume hnp : ¬p, absurd hnp h)
    -- END

Double-negation elimination allows one to prove any proposition, ``p``, by assuming ``¬p`` and deriving ``false``, because that amounts to proving ``¬¬p``. In other words, double-negation elimination allows one to carry out a proof by contradiction, something which is not generally possible in constructive logic. As an exercise, you might try proving the converse, that is, showing that ``em`` can be proved from ``dne``.

The classical axioms also give you access to additional patterns of proof that can be justified by appeal to ``em``. For example, one can carry out a proof by cases:

.. code-block:: lean

    open classical

    variable p : Prop

    -- BEGIN
    example (h : ¬¬p) : p :=
    by_cases
      (assume h1 : p, h1)
      (assume h1 : ¬p, absurd h1 h)
    -- END

Or you can carry out a proof by contradiction:

.. code-block:: lean

    open classical

    variable p : Prop

    -- BEGIN
    example (h : ¬¬p) : p :=
    by_contradiction
      (assume h1 : ¬p,
        show false, from h h1)
    -- END

If you are not used to thinking constructively, it may take some time for you to get a sense of where classical reasoning is used. It is needed in the following example because, from a constructive standpoint, knowing that ``p`` and ``q`` are not both true does not necessarily tell you which one is false:

.. code-block:: lean

    open classical

    variables p q : Prop

    -- BEGIN
    example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    or.elim (em p)
      (assume hp : p,
        or.inr
          (show ¬q, from
            assume hq : q,
            h ⟨hp, hq⟩))
      (assume hp : ¬p,
        or.inl hp)
    -- END

We will see later that there *are* situations in constructive logic where principles like excluded middle and double-negation elimination are permissible, and Lean supports the use of classical reasoning in such contexts without relying on excluded middle.

The full list of axioms that are used in Lean to support classical reasoning are discussed in :numref:`Chapter %s <axioms_and_computation>`.

.. _examples_of_propositional_validities:

Examples of Propositional Validities
------------------------------------

Lean's standard library contains proofs of many valid statements of propositional logic, all of which you are free to use in proofs of your own. The following list includes a number of common identities.

Commutativity:

#. ``p ∧ q ↔ q ∧ p``
#. ``p ∨ q ↔ q ∨ p``

Associativity:

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
#. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

Distributivity:

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
#. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

Other properties:

7. ``(p → (q → r)) ↔ (p ∧ q → r)``
#. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
#. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
#. ``¬p ∨ ¬q → ¬(p ∧ q)``
#. ``¬(p ∧ ¬p)``
#. ``p ∧ ¬q → ¬(p → q)``
#. ``¬p → (p → q)``
#. ``(¬p ∨ q) → (p → q)``
#. ``p ∨ false ↔ p``
#. ``p ∧ false ↔ false``
#. ``¬(p ↔ ¬p)``
#. ``(p → q) → (¬q → ¬p)``

These require classical reasoning:

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
#. ``¬(p ∧ q) → ¬p ∨ ¬q``
#. ``¬(p → q) → p ∧ ¬q``
#. ``(p → q) → (¬p ∨ q)``
#. ``(¬q → ¬p) → (p → q)``
#. ``p ∨ ¬p``
#. ``(((p → q) → p) → p)``

The ``sorry`` identifier magically produces a proof of anything, or provides an object of any data type at all. Of course, it is unsound as a proof method -- for example, you can use it to prove ``false`` -- and Lean produces severe warnings when files use or import theorems which depend on it. But it is very useful for building long proofs incrementally. Start writing the proof from the top down, using ``sorry`` to fill in subproofs. Make sure Lean accepts the term with all the ``sorry``'s; if not, there are errors that you need to correct. Then go back and replace each ``sorry`` with an actual proof, until no more remain.

Here is another useful trick. Instead of using ``sorry``, you can use an underscore ``_`` as a placeholder. Recall that this tells Lean that the argument is implicit, and should be filled in automatically. If Lean tries to do so and fails, it returns with an error message "don't know how to synthesize placeholder." This is followed by the type of the term it is expecting, and all the objects and hypothesis available in the context. In other words, for each unresolved placeholder, Lean reports the subgoal that needs to be filled at that point. You can then construct a proof by incrementally filling in these placeholders.

For reference, here are two sample proofs of validities taken from the list above.

.. code-block:: lean

    open classical

    variables p q r : Prop

    -- distributivity
    example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    iff.intro
      (assume h : p ∧ (q ∨ r),
        have hp : p, from h.left,
        or.elim (h.right)
          (assume hq : q,
            show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
          (assume hr : r,
            show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
      (assume h : (p ∧ q) ∨ (p ∧ r),
        or.elim h
          (assume hpq : p ∧ q,
            have hp : p, from hpq.left,
            have hq : q, from hpq.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
          (assume hpr : p ∧ r,
            have hp : p, from hpr.left,
            have hr : r, from hpr.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))

    -- an example that requires classical reasoning
    example : ¬(p ∧ ¬q) → (p → q) :=
    assume h : ¬(p ∧ ¬q),
    assume hp : p,
    show q, from
      or.elim (em q)
        (assume hq : q, hq)
        (assume hnq : ¬q, absurd (and.intro hp hnq) h)

Exercises
---------

#. Prove the following identities, replacing the "sorry" placeholders with actual proofs.

    .. code-block:: lean

        variables p q r : Prop

        -- commutativity of ∧ and ∨
        example : p ∧ q ↔ q ∧ p := sorry
        example : p ∨ q ↔ q ∨ p := sorry

        -- associativity of ∧ and ∨
        example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
        example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

        -- distributivity
        example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
        example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

        -- other properties
        example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
        example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
        example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
        example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
        example : ¬(p ∧ ¬p) := sorry
        example : p ∧ ¬q → ¬(p → q) := sorry
        example : ¬p → (p → q) := sorry
        example : (¬p ∨ q) → (p → q) := sorry
        example : p ∨ false ↔ p := sorry
        example : p ∧ false ↔ false := sorry
        example : (p → q) → (¬q → ¬p) := sorry

#. Prove the following identities, replacing the "sorry" placeholders with actual proofs. These require classical reasoning.

    .. code-block:: lean

        open classical

        variables p q r s : Prop

        example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
        example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
        example : ¬(p → q) → p ∧ ¬q := sorry
        example : (p → q) → (¬p ∨ q) := sorry
        example : (¬q → ¬p) → (p → q) := sorry
        example : p ∨ ¬p := sorry
        example : (((p → q) → p) → p) := sorry

#. Prove ``¬(p ↔ ¬p)`` without using classical logic.
