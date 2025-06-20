import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL



set_option pp.rawOnError true

#doc (Manual) "Propositions and Proofs" =>
%%%
tag := "propositions-and-proofs"
htmlSplit := .never
%%%

By now, you have seen some ways of defining objects and functions in
Lean. In this chapter, we will begin to explain how to write
mathematical assertions and proofs in the language of dependent type
theory as well.

# Propositions as Types

One strategy for proving assertions about objects defined in the
language of dependent type theory is to layer an assertion language
and a proof language on top of the definition language. But there is
no reason to multiply languages in this way: dependent type theory is
flexible and expressive, and there is no reason we cannot represent
assertions and proofs in the same general framework.

For example, we could introduce a new type, {lean}`Prop`, to represent
propositions, and introduce constructors to build new propositions
from others.

```lean
def Implies (p q : Prop) : Prop := p → q
------
#check And     -- And (a b : Prop) : Prop

#check Or      -- Or (a b : Prop) : Prop

#check Not     -- Not (a : Prop) : Prop

#check Implies -- Implies (p q : Prop) : Prop

variable (p q r : Prop)

#check And p q                      -- p ∧ q : Prop

#check Or (And p q) r               -- p ∧ q ∨ r : Prop

#check Implies (And p q) (And q p)  -- Implies (p ∧ q) (q ∧ p) : Prop
```


```setup
variable (p : Prop)
structure Proof (p : Prop) : Type where
  proof : p
variable (t : p) (q r : Prop)
def Implies (p q : Prop) : Prop := p → q
universe u
variable (t1 t2 : p) {α : Type u} {β : Type v}
```

We could then introduce, for each element {lean}`p : Prop`, another type
{lean}`Proof p`, for the type of proofs of {lean}`p`.  An “axiom” would be a
constant of such a type.


```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
#check Proof   -- Proof (p : Prop) : Type

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q     -- and_commut p q : Proof (Implies (p ∧ q) (q ∧ p))
```



In addition to axioms, however, we would also need rules to build new
proofs from old ones. For example, in many proof systems for
propositional logic, we have the rule of _modus ponens_:

> From a proof of {lean}`Implies p q` and a proof of {lean}`p`, we obtain a proof of {lean}`q`.

We could represent this as follows:

```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q
```

Systems of natural deduction for propositional logic also typically rely on the following rule:

> Suppose that, assuming {lean}`p` as a hypothesis, we have a proof of {lean}`q`. Then we can “cancel” the hypothesis and obtain a proof of {lean}`Implies p q`.

We could render this as follows:

```lean
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
------
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)
```

This approach would provide us with a reasonable way of building assertions and proofs.
Determining that an expression {lean}`t` is a correct proof of assertion {lean}`p` would then
simply be a matter of checking that {lean}`t` has type {lean}`Proof p`.

Some simplifications are possible, however. To start with, we can
avoid writing the term {lean}`Proof` repeatedly by conflating {lean}`Proof p`
with {lean}`p` itself. In other words, whenever we have {lean}`p : Prop`, we
can interpret {lean}`p` as a type, namely, the type of its proofs. We can
then read {lean}`t : p` as the assertion that {lean}`t` is a proof of {lean}`p`.

Moreover, once we make this identification, the rules for implication
show that we can pass back and forth between {lean}`Implies p q` and
{lean}`p → q`. In other words, implication between propositions {lean}`p` and {lean}`q`
corresponds to having a function that takes any element of {lean}`p` to an
element of {lean}`q`. As a result, the introduction of the connective
{lean}`Implies` is entirely redundant: we can use the usual function space
constructor {lean}`p → q` from dependent type theory as our notion of
implication.

This is the approach followed in the Calculus of Constructions, and
hence in Lean as well. The fact that the rules for implication in a
proof system for natural deduction correspond exactly to the rules
governing abstraction and application for functions is an instance of
the {deftech}_Curry-Howard isomorphism_, sometimes known as the
{deftech}_propositions-as-types_ paradigm. In fact, the type {lean}`Prop` is
syntactic sugar for {lean}`Sort 0`, the very bottom of the type hierarchy
described in the last chapter. Moreover, {lean}`Type u` is also just
syntactic sugar for {lean}`Sort (u+1)`. {lean}`Prop` has some special
features, but like the other type universes, it is closed under the
arrow constructor: if we have {lean}`p q : Prop`, then {lean}`p → q : Prop`.

There are at least two ways of thinking about propositions as
types. To some who take a constructive view of logic and mathematics,
this is a faithful rendering of what it means to be a proposition: a
proposition {lean}`p` represents a sort of data type, namely, a
specification of the type of data that constitutes a proof. A proof of
{lean}`p` is then simply an object {lean}`t : p` of the right type.

Those not inclined to this ideology can view it, rather, as a simple
coding trick. To each proposition {lean}`p` we associate a type that is
empty if {lean}`p` is false and has a single element, say {lit}`*`, if {lean}`p`
is true. In the latter case, let us say that (the type associated
with) {lean}`p` is _inhabited_. It just so happens that the rules for
function application and abstraction can conveniently help us keep
track of which elements of {lean}`Prop` are inhabited. So constructing an
element {lean}`t : p` tells us that {lean}`p` is indeed true. You can think of
the inhabitant of {lean}`p` as being the “fact that {lean}`p` is true.” A
proof of {lean}`p → q` uses “the fact that {lean}`p` is true” to obtain “the
fact that {lean}`q` is true.”

Indeed, if {lean}`p : Prop` is any proposition, Lean's kernel treats any
two elements {lean}`t1 t2 : p` as being definitionally equal, much the
same way as it treats {lit}`(fun x => t) s` and {lit}`t[s/x]` as
definitionally equal. This is known as {deftech}_proof irrelevance_, and is
consistent with the interpretation in the last paragraph. It means
that even though we can treat proofs {lean}`t : p` as ordinary objects in
the language of dependent type theory, they carry no information
beyond the fact that {lean}`p` is true.

The two ways we have suggested thinking about the
{tech}[propositions-as-types] paradigm differ in a fundamental way. From the
constructive point of view, proofs are abstract mathematical objects
that are _denoted_ by suitable expressions in dependent type
theory. In contrast, if we think in terms of the coding trick
described above, then the expressions themselves do not denote
anything interesting. Rather, it is the fact that we can write them
down and check that they are well-typed that ensures that the
proposition in question is true. In other words, the expressions
_themselves_ are the proofs.

In the exposition below, we will slip back and forth between these two
ways of talking, at times saying that an expression “constructs” or
“produces” or “returns” a proof of a proposition, and at other times
simply saying that it “is” such a proof. This is similar to the way
that computer scientists occasionally blur the distinction between
syntax and semantics by saying, at times, that a program “computes” a
certain function, and at other times speaking as though the program
“is” the function in question.

In any case, all that really matters is the bottom line. To formally
express a mathematical assertion in the language of dependent type
theory, we need to exhibit a term {lean}`p : Prop`. To _prove_ that
assertion, we need to exhibit a term {lean}`t : p`. Lean's task, as a
proof assistant, is to help us to construct such a term, {lean}`t`, and to
verify that it is well-formed and has the correct type.

# Working with Propositions as Types

In the {tech}[propositions-as-types] paradigm, theorems involving only {lit}`→`
can be proved using lambda abstraction and application. In Lean, the
{kw}`theorem` command introduces a new theorem:

```lean
set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

Compare this proof to the expression {lean}`fun x : α => fun y : β => x`
of type {lean}`α → β → α`, where {lean}`α` and {lean}`β` are data types.
This describes the function that takes arguments {leanRef}`x` and {leanRef}`y`
of type {lean}`α` and {lean}`β`, respectively, and returns {leanRef}`x`.
The proof of {lean}`t1` has the same form, the only difference being that
{lean}`p` and {lean}`q` are elements of {lean}`Prop` rather than {lean}`Type`.
Intuitively, our proof of
{lean}`p → q → p` assumes {lean}`p` and {lean}`q` are true, and uses the first
hypothesis (trivially) to establish that the conclusion, {lean}`p`, is
true.

Note that the {kw}`theorem` command is really a version of the
{kw}`def` command: under the propositions and types
correspondence, proving the theorem {lean}`p → q → p` is really the same
as defining an element of the associated type. To the kernel type
checker, there is no difference between the two.

There are a few pragmatic differences between definitions and
theorems, however. In normal circumstances, it is never necessary to
unfold the “definition” of a theorem; by {tech}[proof irrelevance], any two
proofs of that theorem are definitionally equal. Once the proof of a
theorem is complete, typically we only need to know that the proof
exists; it doesn't matter what the proof is. In light of that fact,
Lean tags proofs as _irreducible_, which serves as a hint to the
parser (more precisely, the _elaborator_) that there is generally no
need to unfold them when processing a file. In fact, Lean is generally
able to process and check proofs in parallel, since assessing the
correctness of one proof does not require knowing the details of
another. Additionally, {ref "variables-and-sections"}[section variables]
that are referred to in the body of a definition are automatically added as
parameters, but only the variables referred to in a theorem's type are added.
This is because the way in which a statement is proved should not influence
the statement that is being proved.

As with definitions, the {kw}`#print` command will show you the proof of
a theorem:

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1 -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

Notice that the lambda abstractions {leanRef}`hp : p` and {leanRef}`hq : q` can be
viewed as temporary assumptions in the proof of {lean}`t1`.  Lean also
allows us to specify the type of the final term {leanRef}`hp`, explicitly,
with a {kw}`show` statement:

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

Adding such extra information can improve the clarity of a proof and
help detect errors when writing a proof. The {kw}`show` command does
nothing more than annotate the type, and, internally, all the
presentations of {leanRef}`t1` that we have seen produce the same term.

As with ordinary definitions, we can move the lambda-abstracted
variables to the left of the colon:

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- theorem t1 : ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp
```

We can use the theorem {leanRef}`t1` just as a function application:

```lean
set_option linter.unusedVariables false
variable {p : Prop}
variable {q : Prop}
------
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

The {kw}`axiom` declaration postulates the existence of an
element of the given type and may compromise logical consistency. For
example, we can use it to postulate that the empty type {lean}`False` has an
element:

```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound
```

:::setup
```
variable {p q : Prop} (hp : p) {t1 : p → q → p}
```
Declaring an “axiom” {lean}`hp : p` is tantamount to declaring that {lean}`p`
is true, as witnessed by {lean}`hp`. Applying the theorem
{lean}`t1 : p → q → p` to the fact {lean}`hp : p` that {lean}`p` is true yields the theorem
{lean}`t1 hp : q → p`.

:::

Recall that we can also write theorem {leanRef}`t1` as follows:

```lean
set_option linter.unusedVariables false
------
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

The type of {leanRef}`t1` is now {lean}`∀ {p q : Prop}, p → q → p`. We can read
this as the assertion “for every pair of propositions {lean}`p`{lit}` `{lean}`q`, we have
{lean}`p → q → p`.” For example, we can move all parameters to the right
of the colon:

```lean
set_option linter.unusedVariables false
------
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

If {lean}`p` and {lean}`q` have been declared as {ref "variables-and-sections"}[variables], Lean will
generalize them for us automatically:

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

When we generalize {leanRef}`t1` in such a way, we can then apply it to
different pairs of propositions, to obtain different instances of the
general theorem.

```lean
set_option linter.unusedVariables false
------
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- t1 p q : p → q → p
#check t1 r s                -- t1 r s : r → s → r
#check t1 (r → s) (s → r)    -- t1 (r → s) (s → r) : (r → s) → (s → r) → r → s

variable (h : r → s)

#check t1 (r → s) (s → r) h  -- t1 (r → s) (s → r) h : (s → r) → r → s
```

Once again, using the {tech}[propositions-as-types] correspondence, the
variable {leanRef}`h` of type {leanRef}`r → s` can be viewed as the hypothesis, or
premise, that {leanRef}`r → s` holds.

As another example, let us consider the composition function discussed
in the last chapter, now with propositions instead of types.

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```

As a theorem of propositional logic, what does {leanRef}`t2` say?

Note that it is often useful to use numeric Unicode subscripts,
entered as {kbd}`\0`, {kbd}`\1`, {kbd}`\2`, ..., for hypotheses, as we did in
this example.

# Propositional Logic

Lean defines all the standard logical connectives and notation. The propositional connectives come with the following notation:

:::table (header := true)
*
 * ASCII
 * Unicode
 * Editor shortcut
 * Definition

*
 * {lean}`True`
 * {empty}[]
 * {empty}[]
 * {lean}`True`

*
 * {lean}`False`
 * {empty}[]
 * {empty}[]
 * {lean}`False`

*
 * {lean}`Not`
 * {lit}`¬`
 * {kbd}`\not`, {kbd}`\neg`
 * {lean}`Not`

*
 * {lit}`/\`
 * {lit}`∧`
 * {kbd}`\and`
 * {lean}`And`

*
 * {lit}`\/`
 * {lit}`∨`
 * {kbd}`\or`
 * {lean}`Or`

*
 * {lit}`->`
 * {lit}`→`
 * {kbd}`\to`, {kbd}`\r`, {kbd}`\imp`
 * {empty}[]

*
 * {lit}`<->`
 * {lit}`↔`
 * {kbd}`\iff`, {kbd}`\lr`
 * {lean}`Iff`

:::

They all take values in {lean}`Prop`.

```lean
variable (p q : Prop)

#check p → q → p ∧ q

#check ¬p → p ↔ False

#check p ∨ q → q ∨ p
```

:::setup
```
variable (p q r a b c d e : Prop)
```

The order of operations is as follows: unary negation {lit}`¬` binds most
strongly, then {lit}`∧`, then {lit}`∨`, then {lit}`→`, and finally {lit}`↔`. For
example, {lean}`a ∧ b → c ∨ d ∧ e` means {lean}`(a ∧ b) → (c ∨ (d ∧ e))`.
Remember that {lit}`→` associates to the right (nothing changes
now that the arguments are elements of {lean}`Prop`, instead of some other
{lean}`Type`), as do the other binary connectives. So if we have
{lean}`p q r : Prop`, the expression {lean}`p → q → r` reads “if {lean}`p`, then if {lean}`q`,
then {lean}`r`.” This is just the “curried” form of {lean}`p ∧ q → r`.

:::

In the last chapter we observed that lambda abstraction can be viewed
as an “introduction rule” for {lit}`→`. In the current setting, it shows
how to “introduce” or establish an implication. Application can be
viewed as an “elimination rule,” showing how to “eliminate” or use an
implication in a proof. The other propositional connectives are
defined in Lean's library, and are automatically imported. Each connective
comes with its canonical introduction and elimination rules.

## Conjunction
%%%
tag := "conjunction"
%%%

:::setup
```
variable (p q : Prop) (h1 : p) (h2 : q)
```

The expression {lean}`And.intro h1 h2` builds a proof of {lean}`p ∧ q` using
proofs {lean}`h1 : p` and {lean}`h2 : q`. It is common to describe
{lean}`And.intro` as the _and-introduction_ rule. In the next example we
use {lean}`And.intro` to create a proof of {lean}`p → q → p ∧ q`.

:::

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

The {kw}`example` command states a theorem without naming it or storing
it in the permanent context. Essentially, it just checks that the
given term has the indicated type. It is convenient for illustration,
and we will use it often.

:::setup
```
variable (p q : Prop) (h : p ∧ q)
```

The expression {lean}`And.left h` creates a proof of {lean}`p` from a proof
{lean}`h : p ∧ q`. Similarly, {lean}`And.right h` is a proof of {lean}`q`. They
are commonly known as the left and right _and-elimination_ rules.

:::

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

We can now prove {lean}`p ∧ q → q ∧ p` with the following proof term.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```

:::setup
```
variable (p q : Prop) (hp : p) (hq : q) (α β : Type) (a : α) (b : β)

```
Notice that and-introduction and and-elimination are similar to the
pairing and projection operations for the Cartesian product. The
difference is that given {lean}`hp : p` and {lean}`hq : q`, {lean}`And.intro hp hq` has type
{lean}`p ∧ q : Prop`, while given {lean}`a : α` and {lean}`b : β`, {lean}`Prod.mk a b` has type
{lean}`α × β : Type`. {lean}`Prod` cannot be used with {lean}`Prop`s, and {lean}`And` cannot be used with {lean}`Type`s.
The similarity between {lit}`∧` and {lit}`×` is another instance
of the {tech}[Curry-Howard isomorphism], but in contrast to implication and
the function space constructor, {lit}`∧` and {lit}`×` are treated separately
in Lean. With the analogy, however, the proof we have just constructed
is similar to a function that swaps the elements of a pair.

We will see in {ref "structures-and-records"}[Structures and Records] that certain
types in Lean are _structures_, which is to say, the type is defined
with a single canonical _constructor_ which builds an element of the
type from a sequence of suitable arguments. For every {lean}`p q : Prop`,
{lean}`p ∧ q` is an example: the canonical way to construct an element is
to apply {lean}`And.intro` to suitable arguments {lean}`hp : p` and
{lean}`hq : q`. Lean allows us to use _anonymous constructor_ notation
{lit}`⟨arg1, arg2, ...⟩` in situations like these, when the relevant type is an
inductive type and can be inferred from the context. In particular, we
can often write {lean type:="p ∧ q"}`⟨hp, hq⟩` instead of {lean}`And.intro hp hq`:

:::

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

These angle brackets are obtained by typing {kbd}`\<` and {kbd}`\>`, respectively.

:::setup
```
inductive Foo where | mk
inductive Bar where | mk : Foo → Bar
variable (e : Foo)
def Foo.bar (x : Foo) : Bar := .mk x
```

Lean provides another useful syntactic gadget. Given an expression
{lean}`e` of an inductive type {lean}`Foo` (possibly applied to some
arguments), the notation {lean}`e.bar` is shorthand for {lean}`Foo.bar e`.
This provides a convenient way of accessing functions without opening
a namespace.  For example, the following two expressions mean the same
thing:

:::

```lean
variable (xs : List Nat)

#check List.length xs

#check xs.length
```

:::setup
```
variable (p q : Prop) (h : p ∧ q)
```


As a result, given {lean}`h : p ∧ q`, we can write {lean}`h.left` for
{lean}`And.left h` and {lean}`h.right` for {lean}`And.right h`. We can therefore
rewrite the sample proof above conveniently as follows:

:::


```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

There is a fine line between brevity and obfuscation, and omitting
information in this way can sometimes make a proof harder to read. But
for straightforward constructions like the one above, when the type of
{leanRef}`h` and the goal of the construction are salient, the notation is
clean and effective.

It is common to iterate constructions like “And.” Lean also allows you
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

## Disjunction

:::setup
```
variable (p q : Prop) (hp : p) (hq : q)
```


The expression {lean}`Or.intro_left q hp` creates a proof of {lean}`p ∨ q`
from a proof {lean}`hp : p`. Similarly, {lean}`Or.intro_right p hq` creates a
proof for {lean}`p ∨ q` using a proof {lean}`hq : q`. These are the left and
right _or-introduction_ rules.
:::

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

:::setup
```
variable (p q r : Prop) (hpq : p ∨ q) (hpr : p → r) (hqr : q → r)
```

The _or-elimination_ rule is slightly more complicated. The idea is
that we can prove {lean}`r` from {lean}`p ∨ q`, by showing that {lean}`r` follows
from {lean}`p` and that {lean}`r` follows from {lean}`q`.  In other words, it is a
proof by cases. In the expression {lean}`Or.elim hpq hpr hqr`, {lean}`Or.elim`
takes three arguments, {lean}`hpq : p ∨ q`, {lean}`hpr : p → r` and
{lean}`hqr : q → r`, and produces a proof of {lean}`r`. In the following example, we use
{lean}`Or.elim` to prove {lean}`p ∨ q → q ∨ p`.
:::

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```

In most cases, the first argument of {lean}`Or.intro_right` and
{lean}`Or.intro_left` can be inferred automatically by Lean. Lean
therefore provides {lean}`Or.inr` and {lean}`Or.inl` which can be viewed as
shorthand for {lean}`Or.intro_right _` and {lean}`Or.intro_left _`. Thus the
proof term above could be written more concisely:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

Notice that there is enough information in the full expression for
Lean to infer the types of {leanRef}`hp` and {leanRef}`hq` as well.  But using the
type annotations in the longer version makes the proof more readable,
and can help catch and debug errors.

:::setup
```
variable (h : p ∨ q)
```

Because {lean}`Or` has two constructors, we cannot use anonymous
constructor notation. But we can still write {lean}`h.elim` instead of
{lean}`Or.elim h`:
:::

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

Once again, you should exercise judgment as to whether such
abbreviations enhance or diminish readability.

## Negation and Falsity

:::setup
```
variable (p q : Prop) (hnp : ¬ p) (hp : p)
```

Negation, {lean}`¬p`, is actually defined to be {lean}`p → False`, so we
obtain {lean}`¬p` by deriving a contradiction from {lean}`p`. Similarly, the
expression {lean}`hnp hp` produces a proof of {lean}`False` from {lean}`hp : p`
and {lean}`hnp : ¬p`. The next example uses both these rules to produce a
proof of {lean}`(p → q) → ¬q → ¬p`. (The symbol {lit}`¬` is produced by
typing {kbd}`\not` or {kbd}`\neg`.)

:::

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

The connective {lean}`False` has a single elimination rule,
{lean}`False.elim`, which expresses the fact that anything follows from a
contradiction. This rule is sometimes called _ex falso_ (short for _ex
falso sequitur quodlibet_), or the _principle of explosion_.

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

The arbitrary fact, {lean}`q`, that follows from falsity is an implicit
argument in {lean}`False.elim` and is inferred automatically. This
pattern, deriving an arbitrary fact from contradictory hypotheses, is
quite common, and is represented by {lean}`absurd`.

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

Here, for example, is a proof of {lean}`¬p → q → (q → p) → r`:

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

Incidentally, just as {lean}`False` has only an elimination rule, {lean}`True`
has only an introduction rule, {lean}`True.intro : True`.  In other words,
{lean}`True` is simply true, and has a canonical proof, {lean}`True.intro`.

## Logical Equivalence

:::setup

```
variable (p q : Prop) (h1 : p → q) (h2 : q → p) (h : p ↔ q)
```

The expression {lean}`Iff.intro h1 h2` produces a proof of {lean}`p ↔ q` from
{lean}`h1 : p → q` and {lean}`h2 : q → p`.  The expression {lean}`Iff.mp h`
produces a proof of {lean}`p → q` from {lean}`h : p ↔ q`. Similarly,
{lean}`Iff.mpr h` produces a proof of {lean}`q → p` from {lean}`h : p ↔ q`. Here is a proof
of {lean}`p ∧ q ↔ q ∧ p`:

:::
```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- and_swap p q : p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

We can use the anonymous constructor notation to construct a proof of
{lean}`p ↔ q` from proofs of the forward and backward directions, and we
can also use {lit}`.` notation with {lit}`mp` and {lit}`mpr`. The previous
examples can therefore be written concisely as follows:

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

# Introducing Auxiliary Subgoals

This is a good place to introduce another device Lean offers to help
structure long proofs, namely, the {kw}`have` construct, which
introduces an auxiliary subgoal in a proof. Here is a small example,
adapted from the last section:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

:::setup
```
variable (p q : Prop) (s : p) (t : q)
```

Internally, the expression {lean}`have h : p := s; t` produces the term
{lean}`(fun (h : p) => t) s`. In other words, {lean}`s` is a proof of {lean}`p`,
{lean}`t` is a proof of the desired conclusion assuming {leanRef}`h : p`, and the
two are combined by a lambda abstraction and application. This simple
device is extremely useful when it comes to structuring long proofs,
since we can use intermediate {kw}`have`'s as stepping stones leading to
the final goal.
:::

Lean also supports a structured way of reasoning backwards from a
goal, which models the “suffices to show” construction in ordinary
mathematics. The next example simply permutes the last two lines in
the previous proof.

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

Writing {leanRef}`suffices hq : q` leaves us with two goals. First, we have
to show that it indeed suffices to show {lean}`q`, by proving the original
goal of {leanRef}`q ∧ p` with the additional hypothesis {leanRef}`hq : q`. Finally,
we have to show {leanRef}`q`.

# Classical Logic
%%%
tag := "classical-logic"
%%%

The introduction and elimination rules we have seen so far are all
constructive, which is to say, they reflect a computational
understanding of the logical connectives based on the
{tech}[propositions-as-types] correspondence. Ordinary classical logic adds to
this the law of the excluded middle, {lean}`p ∨ ¬p`. To use this
principle, you have to open the classical namespace.

```lean
open Classical

variable (p : Prop)

#check em p
```

:::setup
```
variable (p q RH : Prop)
```

Intuitively, the constructive “Or” is very strong: asserting {lean}`p ∨ q`
amounts to knowing which is the case. If {lean}`RH` represents the Riemann
hypothesis, a classical mathematician is willing to assert
{lean}`RH ∨ ¬RH`, even though we cannot yet assert either disjunct.

:::

One consequence of the law of the excluded middle is the principle of
double-negation elimination:

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

:::setup
```
open Classical
variable (p : Prop)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```


Double-negation elimination allows one to prove any proposition,
{lean}`p`, by assuming {lean}`¬p` and deriving {lean}`False`, because that amounts
to proving {lean}`¬¬p`. In other words, double-negation elimination allows
one to carry out a proof by contradiction, something which is not
generally possible in constructive logic. As an exercise, you might
try proving the converse, that is, showing that {lean}`em` can be proved
from {lean}`dne`.



The classical axioms also give you access to additional patterns of
proof that can be justified by appeal to {lean}`em`.  For example, one can
carry out a proof by cases:
:::

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
standpoint, knowing that {lean}`p` and {lean}`q` are not both true does not
necessarily tell you which one is false:

```lean
open Classical
variable (p q : Prop)
------
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

We will see later that there _are_ situations in constructive logic
where principles like excluded middle and double-negation elimination
are permissible, and Lean supports the use of classical reasoning in
such contexts without relying on excluded middle.

The full list of axioms that are used in Lean to support classical
reasoning are discussed in {ref "axioms-and-computation"}[Axioms and Computation].

# Examples of Propositional Validities

:::setup
```
variable (p q r s : Prop)
```


Lean's standard library contains proofs of many valid statements of
propositional logic, all of which you are free to use in proofs of
your own. The following list includes a number of common identities.

Commutativity:

1. {lean}`p ∧ q ↔ q ∧ p`
2. {lean}`p ∨ q ↔ q ∨ p`

Associativity:

3. {lean}`(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)`
4. {lean}`(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)`

Distributivity:

5. {lean}`p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)`
6. {lean}`p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)`

Other properties:

7. {lean}`(p → (q → r)) ↔ (p ∧ q → r)`
8. {lean}`((p ∨ q) → r) ↔ (p → r) ∧ (q → r)`
9. {lean}`¬(p ∨ q) ↔ ¬p ∧ ¬q`
10. {lean}`¬p ∨ ¬q → ¬(p ∧ q)`
11. {lean}`¬(p ∧ ¬p)`
12. {lean}`p ∧ ¬q → ¬(p → q)`
13. {lean}`¬p → (p → q)`
14. {lean}`(¬p ∨ q) → (p → q)`
15. {lean}`p ∨ False ↔ p`
16. {lean}`p ∧ False ↔ False`
17. {lean}`¬(p ↔ ¬p)`
18. {lean}`(p → q) → (¬q → ¬p)`

These require classical reasoning:

19. {lean}`(p → r ∨ s) → ((p → r) ∨ (p → s))`
20. {lean}`¬(p ∧ q) → ¬p ∨ ¬q`
21. {lean}`¬(p → q) → p ∧ ¬q`
22. {lean}`(p → q) → (¬p ∨ q)`
23. {lean}`(¬q → ¬p) → (p → q)`
24. {lean}`p ∨ ¬p`
25. {lean}`(((p → q) → p) → p)`

The {lean}`sorry` identifier magically produces a proof of anything, or
provides an object of any data type at all. Of course, it is unsound
as a proof method—for example, you can use it to prove {lean}`False`—and
Lean produces severe warnings when files use or import theorems
which depend on it. But it is very useful for building long proofs
incrementally. Start writing the proof from the top down, using
{lean}`sorry` to fill in subproofs. Make sure Lean accepts the term with
all the {lean}`sorry`'s; if not, there are errors that you need to
correct. Then go back and replace each {lean}`sorry` with an actual proof,
until no more remain.

Here is another useful trick. Instead of using {lean}`sorry`, you can use
an underscore {lit}`_` as a placeholder. Recall this tells Lean that
the argument is implicit, and should be filled in automatically. If
Lean tries to do so and fails, it returns with an error message “don't
know how to synthesize placeholder,” followed by the type of
the term it is expecting, and all the objects and hypotheses available
in the context. In other words, for each unresolved placeholder, Lean
reports the subgoal that needs to be filled at that point. You can
then construct a proof by incrementally filling in these placeholders.

:::

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

# Exercises

Prove the following identities, replacing the {lean}`sorry` placeholders with actual proofs.

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

Prove the following identities, replacing the {lean}`sorry` placeholders
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

Prove {lean}`¬(p ↔ ¬p)` without using classical logic.
