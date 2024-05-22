Propositions and Proofs
=======================

By now, you have seen some ways of defining objects and functions in
Lean. In this chapter, we will begin to explain how to write
mathematical assertions and proofs in the language of dependent type
theory as well.

Propositions as Types
---------------------

One strategy for proving assertions about objects defined in the
language of dependent type theory is to layer an assertion language
and a proof language on top of the definition language. But there is
no reason to multiply languages in this way: dependent type theory is
flexible and expressive, and there is no reason we cannot represent
assertions and proofs in the same general framework.

For example, we could introduce a new type, ``Prop``, to represent
propositions, and introduce constructors to build new propositions
from others.

```lean
# def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

We could then introduce, for each element ``p : Prop``, another type
``Proof p``, for the type of proofs of ``p``.  An "axiom" would be a
constant of such a type.

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
```

In addition to axioms, however, we would also need rules to build new
proofs from old ones. For example, in many proof systems for
propositional logic, we have the rule of *modus ponens*:

> From a proof of ``Implies p q`` and a proof of ``p``, we obtain a proof of ``q``.

We could represent this as follows:

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
```

Systems of natural deduction for propositional logic also typically rely on the following rule:

> Suppose that, assuming ``p`` as a hypothesis, we have a proof of ``q``. Then we can "cancel" the hypothesis and obtain a proof of ``Implies p q``.

We could render this as follows:

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

This approach would provide us with a reasonable way of building assertions and proofs.
Determining that an expression ``t`` is a correct proof of assertion ``p`` would then
simply be a matter of checking that ``t`` has type ``Proof p``.

Some simplifications are possible, however. To start with, we can
avoid writing the term ``Proof`` repeatedly by conflating ``Proof p``
with ``p`` itself. In other words, whenever we have ``p : Prop``, we
can interpret ``p`` as a type, namely, the type of its proofs. We can
then read ``t : p`` as the assertion that ``t`` is a proof of ``p``.

Moreover, once we make this identification, the rules for implication
show that we can pass back and forth between ``Implies p q`` and
``p → q``. In other words, implication between propositions ``p`` and ``q``
corresponds to having a function that takes any element of ``p`` to an
element of ``q``. As a result, the introduction of the connective
``Implies`` is entirely redundant: we can use the usual function space
constructor ``p → q`` from dependent type theory as our notion of
implication.

This is the approach followed in the Calculus of Constructions, and
hence in Lean as well. The fact that the rules for implication in a
proof system for natural deduction correspond exactly to the rules
governing abstraction and application for functions is an instance of
the *Curry-Howard isomorphism*, sometimes known as the
*propositions-as-types* paradigm. In fact, the type ``Prop`` is
syntactic sugar for ``Sort 0``, the very bottom of the type hierarchy
described in the last chapter. Moreover, ``Type u`` is also just
syntactic sugar for ``Sort (u+1)``. ``Prop`` has some special
features, but like the other type universes, it is closed under the
arrow constructor: if we have ``p q : Prop``, then ``p → q : Prop``.

There are at least two ways of thinking about propositions as
types. To some who take a constructive view of logic and mathematics,
this is a faithful rendering of what it means to be a proposition: a
proposition ``p`` represents a sort of data type, namely, a
specification of the type of data that constitutes a proof. A proof of
``p`` is then simply an object ``t : p`` of the right type.

Those not inclined to this ideology can view it, rather, as a simple
coding trick. To each proposition ``p`` we associate a type that is
empty if ``p`` is false and has a single element, say ``*``, if ``p``
is true. In the latter case, let us say that (the type associated
with) ``p`` is *inhabited*. It just so happens that the rules for
function application and abstraction can conveniently help us keep
track of which elements of ``Prop`` are inhabited. So constructing an
element ``t : p`` tells us that ``p`` is indeed true. You can think of
the inhabitant of ``p`` as being the "fact that ``p`` is true." A
proof of ``p → q`` uses "the fact that ``p`` is true" to obtain "the
fact that ``q`` is true."

Indeed, if ``p : Prop`` is any proposition, Lean's kernel treats any
two elements ``t1 t2 : p`` as being definitionally equal, much the
same way as it treats ``(fun x => t) s`` and ``t[s/x]`` as
definitionally equal. This is known as *proof irrelevance,* and is
consistent with the interpretation in the last paragraph. It means
that even though we can treat proofs ``t : p`` as ordinary objects in
the language of dependent type theory, they carry no information
beyond the fact that ``p`` is true.

The two ways we have suggested thinking about the
propositions-as-types paradigm differ in a fundamental way. From the
constructive point of view, proofs are abstract mathematical objects
that are *denoted* by suitable expressions in dependent type
theory. In contrast, if we think in terms of the coding trick
described above, then the expressions themselves do not denote
anything interesting. Rather, it is the fact that we can write them
down and check that they are well-typed that ensures that the
proposition in question is true. In other words, the expressions
*themselves* are the proofs.

In the exposition below, we will slip back and forth between these two
ways of talking, at times saying that an expression "constructs" or
"produces" or "returns" a proof of a proposition, and at other times
simply saying that it "is" such a proof. This is similar to the way
that computer scientists occasionally blur the distinction between
syntax and semantics by saying, at times, that a program "computes" a
certain function, and at other times speaking as though the program
"is" the function in question.

In any case, all that really matters is the bottom line. To formally
express a mathematical assertion in the language of dependent type
theory, we need to exhibit a term ``p : Prop``. To *prove* that
assertion, we need to exhibit a term ``t : p``. Lean's task, as a
proof assistant, is to help us to construct such a term, ``t``, and to
verify that it is well-formed and has the correct type.

Working with Propositions as Types
----------------------------------

In the propositions-as-types paradigm, theorems involving only ``→``
can be proved using lambda abstraction and application. In Lean, the
``theorem`` command introduces a new theorem:

```lean
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

Compare this proof to the expression ``fun x : α => fun y : β => x``
of type ``α → β → α``, where ``α`` and ``β`` are data types.
This describes the function that takes arguments ``x`` and ``y``
of type ``α`` and ``β``, respectively, and returns ``x``.
The proof of ``t1`` has the same form, the only difference being that
``p`` and ``q`` are elements of ``Prop`` rather than ``Type``.
Intuitively, our proof of
``p → q → p`` assumes ``p`` and ``q`` are true, and uses the first
hypothesis (trivially) to establish that the conclusion, ``p``, is
true.

Note that the ``theorem`` command is really a version of the
``def`` command: under the propositions and types
correspondence, proving the theorem ``p → q → p`` is really the same
as defining an element of the associated type. To the kernel type
checker, there is no difference between the two.

There are a few pragmatic differences between definitions and
theorems, however. In normal circumstances, it is never necessary to
unfold the "definition" of a theorem; by proof irrelevance, any two
proofs of that theorem are definitionally equal. Once the proof of a
theorem is complete, typically we only need to know that the proof
exists; it doesn't matter what the proof is. In light of that fact,
Lean tags proofs as *irreducible*, which serves as a hint to the
parser (more precisely, the *elaborator*) that there is generally no
need to unfold them when processing a file. In fact, Lean is generally
able to process and check proofs in parallel, since assessing the
correctness of one proof does not require knowing the details of
another.

As with definitions, the ``#print`` command will show you the proof of
a theorem:

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1
```

Notice that the lambda abstractions ``hp : p`` and ``hq : q`` can be
viewed as temporary assumptions in the proof of ``t1``.  Lean also
allows us to specify the type of the final term ``hp``, explicitly,
with a ``show`` statement:

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

Adding such extra information can improve the clarity of a proof and
help detect errors when writing a proof. The ``show`` command does
nothing more than annotate the type, and, internally, all the
presentations of ``t1`` that we have seen produce the same term.

As with ordinary definitions, we can move the lambda-abstracted
variables to the left of the colon:

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p
```

We can use the theorem ``t1`` just as a function application:

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

The ``axiom`` declaration postulates the existence of an
element of the given type and may compromise logical consistency. For
example, we can use it to postulate that the empty type `False` has an
element:

```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound
```

Declaring an "axiom" ``hp : p`` is tantamount to declaring that ``p``
is true, as witnessed by ``hp``. Applying the theorem
``t1 : p → q → p`` to the fact ``hp : p`` that ``p`` is true yields the theorem
``t1 hp : q → p``.

Recall that we can also write theorem ``t1`` as follows:

```lean
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

The type of ``t1`` is now ``∀ {p q : Prop}, p → q → p``. We can read
this as the assertion "for every pair of propositions ``p q``, we have
``p → q → p``." For example, we can move all parameters to the right
of the colon:

```lean
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

If ``p`` and ``q`` have been declared as variables, Lean will
generalize them for us automatically:

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

In fact, by the propositions-as-types correspondence, we can declare
the assumption ``hp`` that ``p`` holds, as another variable:

```lean
variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp
```

Lean detects that the proof uses ``hp`` and automatically adds
``hp : p`` as a premise. In all cases, the command ``#print t1`` still yields
``∀ p q : Prop, p → q → p``. Remember that this type can just as well
be written ``∀ (p q : Prop) (hp : p) (hq : q), p``, since the arrow
denotes nothing more than an arrow type in which the target does not
depend on the bound variable.

When we generalize ``t1`` in such a way, we can then apply it to
different pairs of propositions, to obtain different instances of the
general theorem.

```lean
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
```

Once again, using the propositions-as-types correspondence, the
variable ``h`` of type ``r → s`` can be viewed as the hypothesis, or
premise, that ``r → s`` holds.

As another example, let us consider the composition function discussed
in the last chapter, now with propositions instead of types.

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```

As a theorem of propositional logic, what does ``t2`` say?

Note that it is often useful to use numeric unicode subscripts,
entered as ``\0``, ``\1``, ``\2``, ..., for hypotheses, as we did in
this example.

Propositional Logic
-------------------

Lean defines all the standard logical connectives and notation. The propositional connectives come with the following notation:

| Ascii             | Unicode   | Editor shortcut              | Definition   |
|-------------------|-----------|------------------------------|--------------|
| True              |           |                              | True         |
| False             |           |                              | False        |
| Not               | ¬         | ``\not``, ``\neg``           | Not          |
| /\\               | ∧         | ``\and``                     | And          |
| \\/               | ∨         | ``\or``                      | Or           |
| ->                | →         | ``\to``, ``\r``, ``\imp``    |              |
| <->               | ↔         | ``\iff``, ``\lr``            | Iff          |

They all take values in ``Prop``.

```lean
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
```

The order of operations is as follows: unary negation ``¬`` binds most
strongly, then ``∧``, then ``∨``, then ``→``, and finally ``↔``. For
example, ``a ∧ b → c ∨ d ∧ e`` means ``(a ∧ b) → (c ∨ (d ∧
e))``. Remember that ``→`` associates to the right (nothing changes
now that the arguments are elements of ``Prop``, instead of some other
``Type``), as do the other binary connectives. So if we have
``p q r : Prop``, the expression ``p → q → r`` reads "if ``p``, then if ``q``,
then ``r``." This is just the "curried" form of ``p ∧ q → r``.

In the last chapter we observed that lambda abstraction can be viewed
as an "introduction rule" for ``→``. In the current setting, it shows
how to "introduce" or establish an implication. Application can be
viewed as an "elimination rule," showing how to "eliminate" or use an
implication in a proof. The other propositional connectives are
defined in Lean's library in the file ``Prelude.core`` (see
[importing files](./interacting_with_lean.md#importing-files) for more information on the library
hierarchy), and each connective comes with its canonical introduction
and elimination rules.

### Conjunction

The expression ``And.intro h1 h2`` builds a proof of ``p ∧ q`` using
proofs ``h1 : p`` and ``h2 : q``. It is common to describe
``And.intro`` as the *and-introduction* rule. In the next example we
use ``And.intro`` to create a proof of ``p → q → p ∧ q``.

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

The ``example`` command states a theorem without naming it or storing
it in the permanent context. Essentially, it just checks that the
given term has the indicated type. It is convenient for illustration,
and we will use it often.

The expression ``And.left h`` creates a proof of ``p`` from a proof
``h : p ∧ q``. Similarly, ``And.right h`` is a proof of ``q``. They
are commonly known as the left and right *and-elimination* rules.

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

We can now prove ``p ∧ q → q ∧ p`` with the following proof term.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```

Notice that and-introduction and and-elimination are similar to the
pairing and projection operations for the Cartesian product. The
difference is that given ``hp : p`` and ``hq : q``, ``And.intro hp
hq`` has type ``p ∧ q : Prop``, while ``Prod hp hq`` has type
``p × q : Type``. The similarity between ``∧`` and ``×`` is another instance
of the Curry-Howard isomorphism, but in contrast to implication and
the function space constructor, ``∧`` and ``×`` are treated separately
in Lean. With the analogy, however, the proof we have just constructed
is similar to a function that swaps the elements of a pair.

We will see in [Chapter Structures and Records](./structures_and_records.md) that certain
types in Lean are *structures*, which is to say, the type is defined
with a single canonical *constructor* which builds an element of the
type from a sequence of suitable arguments. For every ``p q : Prop``,
``p ∧ q`` is an example: the canonical way to construct an element is
to apply ``And.intro`` to suitable arguments ``hp : p`` and
``hq : q``. Lean allows us to use *anonymous constructor* notation
``⟨arg1, arg2, ...⟩`` in situations like these, when the relevant type is an
inductive type and can be inferred from the context. In particular, we
can often write ``⟨hp, hq⟩`` instead of ``And.intro hp hq``:

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

These angle brackets are obtained by typing ``\<`` and ``\>``, respectively.

Lean provides another useful syntactic gadget. Given an expression
``e`` of an inductive type ``Foo`` (possibly applied to some
arguments), the notation ``e.bar`` is shorthand for ``Foo.bar e``.
This provides a convenient way of accessing functions without opening
a namespace.  For example, the following two expressions mean the same
thing:

```lean
variable (xs : List Nat)

#check List.length xs
#check xs.length
```

As a result, given ``h : p ∧ q``, we can write ``h.left`` for
``And.left h`` and ``h.right`` for ``And.right h``. We can therefore
rewrite the sample proof above conveniently as follows:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

There is a fine line between brevity and obfuscation, and omitting
information in this way can sometimes make a proof harder to read. But
for straightforward constructions like the one above, when the type of
``h`` and the goal of the construction are salient, the notation is
clean and effective.

It is common to iterate constructions like "And." Lean also allows you
to flatten nested constructors that associate to the right, so that
these two proofs are equivalent:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
```

This is often useful as well.

### Disjunction

The expression ``Or.intro_left q hp`` creates a proof of ``p ∨ q``
from a proof ``hp : p``. Similarly, ``Or.intro_right p hq`` creates a
proof for ``p ∨ q`` using a proof ``hq : q``. These are the left and
right *or-introduction* rules.

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

The *or-elimination* rule is slightly more complicated. The idea is
that we can prove ``r`` from ``p ∨ q``, by showing that ``r`` follows
from ``p`` and that ``r`` follows from ``q``.  In other words, it is a
proof by cases. In the expression ``Or.elim hpq hpr hqr``, ``Or.elim``
takes three arguments, ``hpq : p ∨ q``, ``hpr : p → r`` and
``hqr : q → r``, and produces a proof of ``r``. In the following example, we use
``Or.elim`` to prove ``p ∨ q → q ∨ p``.

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```

In most cases, the first argument of ``Or.intro_right`` and
``Or.intro_left`` can be inferred automatically by Lean. Lean
therefore provides ``Or.inr`` and ``Or.inl`` which can be viewed as
shorthand for ``Or.intro_right _`` and ``Or.intro_left _``. Thus the
proof term above could be written more concisely:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

Notice that there is enough information in the full expression for
Lean to infer the types of ``hp`` and ``hq`` as well.  But using the
type annotations in the longer version makes the proof more readable,
and can help catch and debug errors.

Because ``Or`` has two constructors, we cannot use anonymous
constructor notation. But we can still write ``h.elim`` instead of
``Or.elim h``:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

Once again, you should exercise judgment as to whether such
abbreviations enhance or diminish readability.

### Negation and Falsity

Negation, ``¬p``, is actually defined to be ``p → False``, so we
obtain ``¬p`` by deriving a contradiction from ``p``. Similarly, the
expression ``hnp hp`` produces a proof of ``False`` from ``hp : p``
and ``hnp : ¬p``. The next example uses both these rules to produce a
proof of ``(p → q) → ¬q → ¬p``. (The symbol ``¬`` is produced by
typing ``\not`` or ``\neg``.)

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

The connective ``False`` has a single elimination rule,
``False.elim``, which expresses the fact that anything follows from a
contradiction. This rule is sometimes called *ex falso* (short for *ex
falso sequitur quodlibet*), or the *principle of explosion*.

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

The arbitrary fact, ``q``, that follows from falsity is an implicit
argument in ``False.elim`` and is inferred automatically. This
pattern, deriving an arbitrary fact from contradictory hypotheses, is
quite common, and is represented by ``absurd``.

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

Here, for example, is a proof of ``¬p → q → (q → p) → r``:

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

Incidentally, just as ``False`` has only an elimination rule, ``True``
has only an introduction rule, ``True.intro : true``.  In other words,
``True`` is simply true, and has a canonical proof, ``True.intro``.

### Logical Equivalence

The expression ``Iff.intro h1 h2`` produces a proof of ``p ↔ q`` from
``h1 : p → q`` and ``h2 : q → p``.  The expression ``Iff.mp h``
produces a proof of ``p → q`` from ``h : p ↔ q``. Similarly,
``Iff.mpr h`` produces a proof of ``q → p`` from ``h : p ↔ q``. Here is a proof
of ``p ∧ q ↔ q ∧ p``:

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

We can use the anonymous constructor notation to construct a proof of
``p ↔ q`` from proofs of the forward and backward directions, and we
can also use ``.`` notation with ``mp`` and ``mpr``. The previous
examples can therefore be written concisely as follows:

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

Introducing Auxiliary Subgoals
--------

This is a good place to introduce another device Lean offers to help
structure long proofs, namely, the ``have`` construct, which
introduces an auxiliary subgoal in a proof. Here is a small example,
adapted from the last section:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

Internally, the expression ``have h : p := s; t`` produces the term
``(fun (h : p) => t) s``. In other words, ``s`` is a proof of ``p``,
``t`` is a proof of the desired conclusion assuming ``h : p``, and the
two are combined by a lambda abstraction and application. This simple
device is extremely useful when it comes to structuring long proofs,
since we can use intermediate ``have``'s as stepping stones leading to
the final goal.

Lean also supports a structured way of reasoning backwards from a
goal, which models the "suffices to show" construction in ordinary
mathematics. The next example simply permutes the last two lines in
the previous proof.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

Writing ``suffices hq : q`` leaves us with two goals. First, we have
to show that it indeed suffices to show ``q``, by proving the original
goal of ``q ∧ p`` with the additional hypothesis ``hq : q``. Finally,
we have to show ``q``.

Classical Logic
---------------

The introduction and elimination rules we have seen so far are all
constructive, which is to say, they reflect a computational
understanding of the logical connectives based on the
propositions-as-types correspondence. Ordinary classical logic adds to
this the law of the excluded middle, ``p ∨ ¬p``. To use this
principle, you have to open the classical namespace.

```lean
open Classical

variable (p : Prop)
#check em p
```

Intuitively, the constructive "Or" is very strong: asserting ``p ∨ q``
amounts to knowing which is the case. If ``RH`` represents the Riemann
hypothesis, a classical mathematician is willing to assert
``RH ∨ ¬RH``, even though we cannot yet assert either disjunct.

One consequence of the law of the excluded middle is the principle of
double-negation elimination:

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

Double-negation elimination allows one to prove any proposition,
``p``, by assuming ``¬p`` and deriving ``false``, because that amounts
to proving ``¬¬p``. In other words, double-negation elimination allows
one to carry out a proof by contradiction, something which is not
generally possible in constructive logic. As an exercise, you might
try proving the converse, that is, showing that ``em`` can be proved
from ``dne``.

The classical axioms also give you access to additional patterns of
proof that can be justified by appeal to ``em``.  For example, one can
carry out a proof by cases:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

Or you can carry out a proof by contradiction:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

If you are not used to thinking constructively, it may take some time
for you to get a sense of where classical reasoning is used.  It is
needed in the following example because, from a constructive
standpoint, knowing that ``p`` and ``q`` are not both true does not
necessarily tell you which one is false:

```lean
# open Classical
# variable (p q : Prop)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```

We will see later that there *are* situations in constructive logic
where principles like excluded middle and double-negation elimination
are permissible, and Lean supports the use of classical reasoning in
such contexts without relying on excluded middle.

The full list of axioms that are used in Lean to support classical
reasoning are discussed in [Axioms and Computation](./axioms_and_computation.md).

Examples of Propositional Validities
------------------------------------

Lean's standard library contains proofs of many valid statements of
propositional logic, all of which you are free to use in proofs of
your own. The following list includes a number of common identities.

Commutativity:

1. ``p ∧ q ↔ q ∧ p``
2. ``p ∨ q ↔ q ∨ p``

Associativity:

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
4. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

Distributivity:

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
6. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

Other properties:

7. ``(p → (q → r)) ↔ (p ∧ q → r)``
8. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
9. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
10. ``¬p ∨ ¬q → ¬(p ∧ q)``
11. ``¬(p ∧ ¬p)``
12. ``p ∧ ¬q → ¬(p → q)``
13. ``¬p → (p → q)``
14. ``(¬p ∨ q) → (p → q)``
15. ``p ∨ False ↔ p``
16. ``p ∧ False ↔ False``
17. ``¬(p ↔ ¬p)``
18. ``(p → q) → (¬q → ¬p)``

These require classical reasoning:

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
20. ``¬(p ∧ q) → ¬p ∨ ¬q``
21. ``¬(p → q) → p ∧ ¬q``
22. ``(p → q) → (¬p ∨ q)``
23. ``(¬q → ¬p) → (p → q)``
24. ``p ∨ ¬p``
25. ``(((p → q) → p) → p)``

The ``sorry`` identifier magically produces a proof of anything, or
provides an object of any data type at all. Of course, it is unsound
as a proof method -- for example, you can use it to prove ``False`` --
and Lean produces severe warnings when files use or import theorems
which depend on it. But it is very useful for building long proofs
incrementally. Start writing the proof from the top down, using
``sorry`` to fill in subproofs. Make sure Lean accepts the term with
all the ``sorry``'s; if not, there are errors that you need to
correct. Then go back and replace each ``sorry`` with an actual proof,
until no more remain.

Here is another useful trick. Instead of using ``sorry``, you can use
an underscore ``_`` as a placeholder. Recall this tells Lean that
the argument is implicit, and should be filled in automatically. If
Lean tries to do so and fails, it returns with an error message "don't
know how to synthesize placeholder," followed by the type of
the term it is expecting, and all the objects and hypotheses available
in the context. In other words, for each unresolved placeholder, Lean
reports the subgoal that needs to be filled at that point. You can
then construct a proof by incrementally filling in these placeholders.

For reference, here are two sample proofs of validities taken from the
list above.

```lean
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

Exercises
---------

Prove the following identities, replacing the "sorry" placeholders with actual proofs.

```lean
variable (p q r : Prop)

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
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

Prove the following identities, replacing the "sorry" placeholders
with actual proofs. These require classical reasoning.

```lean
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

Prove ``¬(p ↔ ¬p)`` without using classical logic.
