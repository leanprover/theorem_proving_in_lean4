import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "Axioms and Computation" =>

We have seen that the version of the Calculus of Constructions that
has been implemented in Lean includes dependent function types,
inductive types, and a hierarchy of universes that starts with an
impredicative, proof-irrelevant {lean}`Prop` at the bottom. In this
chapter, we consider ways of extending the CIC with additional axioms
and rules. Extending a foundational system in such a way is often
convenient; it can make it possible to prove more theorems, as well as
make it easier to prove theorems that could have been proved
otherwise. But there can be negative consequences of adding additional
axioms, consequences which may go beyond concerns about their
correctness. In particular, the use of axioms bears on the
computational content of definitions and theorems, in ways we will
explore here.

Lean is designed to support both computational and classical
reasoning. Users that are so inclined can stick to a "computationally
pure" fragment, which guarantees that closed expressions in the system
evaluate to canonical normal forms. In particular, any closed
computationally pure expression of type {lean}`Nat`, for example, will
reduce to a numeral.

Lean's standard library defines an additional axiom, propositional
extensionality, and a quotient construction which in turn implies the
principle of function extensionality. These extensions are used, for
example, to develop theories of sets and finite sets. We will see
below that using these theorems can block evaluation in Lean's kernel,
so that closed terms of type {lean}`Nat` no longer evaluate to numerals. But
Lean erases types and propositional information when compiling
definitions to bytecode for its virtual machine evaluator, and since
these axioms only add new propositions, they are compatible with that
computational interpretation. Even computationally inclined users may
wish to use the classical law of the excluded middle to reason about
computation. This also blocks evaluation in the kernel, but it is
compatible with compilation to bytecode.

The standard library also defines a choice principle that is entirely
antithetical to a computational interpretation, since it magically
produces "data" from a proposition asserting its existence. Its use is
essential to some classical constructions, and users can import it
when needed. But expressions that use this construction to produce
data do not have computational content, and in Lean we are required to
mark such definitions as {kw}`noncomputable` to flag that fact.

Using a clever trick (known as Diaconescu's theorem), one can use
propositional extensionality, function extensionality, and choice to
derive the law of the excluded middle. As noted above, however, use of
the law of the excluded middle is still compatible with bytecode
compilation and code extraction, as are other classical principles, as
long as they are not used to manufacture data.

To summarize, then, on top of the underlying framework of universes,
dependent function types, and inductive types, the standard library
adds three additional components:

- the axiom of propositional extensionality
- a quotient construction, which implies function extensionality
- a choice principle, which produces data from an existential proposition.

The first two of these block normalization within Lean, but are
compatible with bytecode evaluation, whereas the third is not amenable
to computational interpretation. We will spell out the details more
precisely below.

# Historical and Philosophical Context

:::setup
````
variable (x : α) (y : β)
````

For most of its history, mathematics was essentially computational:
geometry dealt with constructions of geometric objects, algebra was
concerned with algorithmic solutions to systems of equations, and
analysis provided means to compute the future behavior of systems
evolving over time. From the proof of a theorem to the effect that
"for every {lean}`x`, there is a {lean}`y` such that ...", it was generally
straightforward to extract an algorithm to compute such a {lean}`y` given
{lean}`x`.
:::

In the nineteenth century, however, increases in the complexity of
mathematical arguments pushed mathematicians to develop new styles of
reasoning that suppress algorithmic information and invoke
descriptions of mathematical objects that abstract away the details of
how those objects are represented. The goal was to obtain a powerful
"conceptual" understanding without getting bogged down in
computational details, but this had the effect of admitting
mathematical theorems that are simply _false_ on a direct
computational reading.

There is still fairly uniform agreement today that computation is
important to mathematics. But there are different views as to how best
to address computational concerns. From a _constructive_ point of
view, it is a mistake to separate mathematics from its computational
roots; every meaningful mathematical theorem should have a direct
computational interpretation. From a _classical_ point of view, it is
more fruitful to maintain a separation of concerns: we can use one
language and body of methods to write computer programs, while
maintaining the freedom to use nonconstructive theories and methods
to reason about them. Lean is designed to support both of these
approaches. Core parts of the library are developed constructively,
but the system also provides support for carrying out classical
mathematical reasoning.

:::setup
````
open Nat
notation "... " e "..." => e
````

Computationally, the purest part of dependent type theory avoids the
use of {lean}`Prop` entirely. Inductive types and dependent function types
can be viewed as data types, and terms of these types can be
"evaluated" by applying reduction rules until no more rules can be
applied. In principle, any closed term (that is, term with no free
variables) of type {lean}`Nat` should evaluate to a numeral, {lean}`succ (... (succ zero)...)`.
:::

:::setup
````
variable (p : Prop) (s t : α) (prf : p)
notation x " = " y " : " α => @Eq α x y
````

Introducing a proof-irrelevant {lean}`Prop` and marking theorems
irreducible represents a first step towards separation of
concerns. The intention is that elements of a type {lean}`p : Prop` should
play no role in computation, and so the particular construction of a
term {lean}`prf : p` is "irrelevant" in that sense. One can still define
computational objects that incorporate elements of type {lean}`Prop`; the
point is that these elements can help us reason about the effects of
the computation, but can be ignored when we extract "code" from the
term. Elements of type {lean}`Prop` are not entirely innocuous,
however. They include equations {lean}`s = t : α` for any type {lean}`α`, and
such equations can be used as casts, to type check terms. Below, we
will see examples of how such casts can block computation in the
system. However, computation is still possible under an evaluation
scheme that erases propositional content, ignores intermediate typing
constraints, and reduces terms until they reach a normal form. This is
precisely what Lean's virtual machine does.

Having adopted a proof-irrelevant {lean}`Prop`, one might consider it
legitimate to use, for example, the law of the excluded middle,
{lean}`p ∨ ¬p`, where {lean}`p` is any proposition. Of course, this, too, can block
computation according to the rules of CIC, but it does not block
bytecode evaluation, as described above. It is only the choice
principles discussed in :numref:`choice` that completely erase the
distinction between the proof-irrelevant and data-relevant parts of
the theory.

:::

# Propositional Extensionality

Propositional extensionality is the following axiom:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
axiom propext {a b : Prop} : (a ↔ b) → a = b
------
end Hidden
```

:::setup
```
variable (a : Prop)
```
It asserts that when two propositions imply one another, they are
actually equal. This is consistent with set-theoretic interpretations
in which any element {lean}`a : Prop` is either empty or the singleton set
$`\{\ast\}`, for some distinguished element $`\ast`. The axiom has the
effect that equivalent propositions can be substituted for one another
in any context:
:::

```lean
variable (a b c d e : Prop)

theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

:::comment
````
<!--
The first example could be proved more laboriously without `propext`
using the fact that the propositional connectives respect
propositional equivalence. The second example represents a more
essential use of `propext`. In fact, it is equivalent to `propext`
itself, a fact which we encourage you to prove.

Given any definition or theorem in Lean, you can use the ``#print
axioms`` command to display the axioms it depends on.

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
    propext h ▸ h₁

    -- BEGIN
    #print axioms thm₁  -- propext
    #print axioms thm₂  -- propext
    -- END
-->
````
:::

# Function Extensionality

:::leanFirst
Similar to propositional extensionality, function extensionality
asserts that any two functions of type {leanRef}`(x : α) → β x` that agree on
all their inputs are equal:

```lean
universe u v
#check (@funext :
         {α : Type u} →
         {β : α → Type v} →
         {f g : (x : α) → β x} →
         (∀ (x : α), f x = g x) →
         f = g)
```

:::

From a classical, set-theoretic perspective, this is exactly what it
means for two functions to be equal. This is known as an "extensional"
view of functions. From a constructive perspective, however, it is
sometimes more natural to think of functions as algorithms, or
computer programs, that are presented in some explicit way. It is
certainly the case that two computer programs can compute the same
answer for every input despite the fact that they are syntactically
quite different. In much the same way, you might want to maintain a
view of functions that does not force you to identify two functions
that have the same input / output behavior. This is known as an
"intensional" view of functions.

In fact, function extensionality follows from the existence of
quotients, which we describe in the next section. In the Lean standard
library, therefore, {leanRef}`funext` is thus
[proved from the quotient construction](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean).

:::leanFirst
Suppose that for {leanRef}`α : Type u` we define the {leanRef}`Set `{leanRef in:="(α : Type u)"}`α`{leanRef}` := α → Prop` to
denote the type of subsets of {leanRef in:="(α : Type u)"}`α`, essentially identifying subsets
with predicates. By combining {leanRef}`funext` and {leanRef}`propext`, we obtain an
extensional theory of such sets:

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```
:::

We can then proceed to define the empty set and set intersection, for
example, and prove set identities:

```lean
def Set (α : Type u) := α → Prop
namespace Set
def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) "∈" => mem
theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))
------
def empty : Set α := fun _ => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun _ => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
-----
end Set
```

The following is an example of how function extensionality blocks
computation inside the Lean kernel:

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

First, we show that the two functions {leanRef}`f` and {leanRef}`g` are equal using
function extensionality, and then we cast {leanRef}`0` of type {lean}`Nat` by
replacing {leanRef}`f` by {leanRef}`g` in the type. Of course, the cast is
vacuous, because {lean}`Nat` does not depend on {leanRef}`f`. But that is enough
to do the damage: under the computational rules of the system, we now
have a closed term of {lean}`Nat` that does not reduce to a numeral. In this
case, we may be tempted to reduce the expression to {lean}`0`. But in
nontrivial examples, eliminating cast changes the type of the term,
which might make an ambient expression type incorrect. The virtual
machine, however, has no trouble evaluating the expression to
{lean}`0`. Here is a similarly contrived example that shows how
{lean}`propext` can get in the way:

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

Current research programs, including work on _observational type
theory_ and _cubical type theory_, aim to extend type theory in ways
that permit reductions for casts involving function extensionality,
quotients, and more. But the solutions are not so clear-cut, and the
rules of Lean's underlying calculus do not sanction such reductions.

In a sense, however, a cast does not change the meaning of an
expression. Rather, it is a mechanism to reason about the expression's
type. Given an appropriate semantics, it then makes sense to reduce
terms in ways that preserve their meaning, ignoring the intermediate
bookkeeping needed to make the reductions type-correct. In that case,
adding new axioms in {lean}`Prop` does not matter; by proof irrelevance,
an expression in {lean}`Prop` carries no information, and can be safely
ignored by the reduction procedures.

# Quotients

:::setup
```
variable (α : Sort u) (r : α → α → Prop) (f : α → β) (x y : α) (f' : Quot r → β)
notation α " / " r:max => Quot (α := α) r
notation "⟦" x "⟧" => Quot.mk _ x

```
Let {lean}`α` be any type, and let {lean}`r` be an equivalence relation on
{lean}`α`. It is mathematically common to form the "quotient" {lean}`α / r`,
that is, the type of elements of {lean}`α` "modulo" {lean}`r`. Set
theoretically, one can view {lean}`α / r` as the set of equivalence
classes of {lean}`α` modulo {lean}`r`. If {lean}`f : α → β` is any function that
respects the equivalence relation in the sense that for every
{lean}`x y : α`, {lean}`r x y` implies {lean}`f x = f y`, then {lean}`f` "lifts" to a function
{lean}`f' : α / r → β` defined on each equivalence class {lean type:="Quot r"}`⟦x⟧` by
{lean}`f' ⟦x⟧ = f x`. Lean's standard library extends the Calculus of
Constructions with additional constants that perform exactly these
constructions, and installs this last equation as a definitional
reduction rule.

In its most basic form, the quotient construction does not even
require {lean}`r` to be an equivalence relation. The following constants
are built into Lean:
:::

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
------
end Hidden
```
:::setup
```
variable (α : Type u) (r : α → α → Prop) (a : α) (f : α → β) (h : ∀ a b, r a b → f a = f b)
```
The first one forms a type {lean}`Quot r` given a type {lean}`α` by any binary
relation {lean}`r` on {lean}`α`. The second maps {lean}`α` to {lit}`Quot α`, so that
if {lean}`r : α → α → Prop` and {lit}`a : α`, then {lean}`Quot.mk r a` is an
element of {lean}`Quot r`. The third principle, {lean}`Quot.ind`, says that
every element of {lean}`Quot.mk r a` is of this form.  As for
{lean}`Quot.lift`, given a function {lean}`f : α → β`, if {lean}`h` is a proof
that {lean}`f` respects the relation {lean}`r`, then {lean}`Quot.lift f h` is the
corresponding function on {lean}`Quot r`. The idea is that for each
element {lean}`a` in {lean}`α`, the function {lean}`Quot.lift f h` maps
{lean}`Quot.mk r a` (the {lean}`r`-class containing {lean}`a`) to {lean}`f a`, wherein {lean}`h`
shows that this function is well defined. In fact, the computation
principle is declared as a reduction rule, as the proof below makes
clear.


```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of numbers equivalent to 4
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl
```


The four constants, {lean}`Quot`, {lean}`Quot.mk`, {lean}`Quot.ind`, and
{lean}`Quot.lift` in and of themselves are not very strong. You can check
that the {lean}`Quot.ind` is satisfied if we take {lean}`Quot r` to be simply
{lean}`α`, and take {lean}`Quot.lift` to be the identity function (ignoring
{lean}`h`). For that reason, these four constants are not viewed as
additional axioms.
:::

:::comment
````
<!--
    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl
    -- BEGIN
    #print axioms thm   -- no axioms
    -- END
-->
````
:::

They are, like inductively defined types and the associated
constructors and recursors, viewed as part of the logical framework.

What makes the {lean}`Quot` construction into a bona fide quotient is the
following additional axiom:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u v
------
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
```

This is the axiom that asserts that any two elements of {leanRef}`α` that are
related by {leanRef}`r` become identified in the quotient. If a theorem or
definition makes use of {leanRef}`Quot.sound`, it will show up in the
{kw}`#print axioms` command.

:::setup
````
variable (α : Type u) (r : α → α → Prop)  (r' r'': α → α → Prop) (a b : α)
````

Of course, the quotient construction is most commonly used in
situations when {lean}`r` is an equivalence relation. Given {lean}`r` as
above, if we define {lean}`r'` according to the rule {lean}`r' a b` iff
{lean}`Quot.mk r a = Quot.mk r b`, then it's clear that {lean}`r'` is an
equivalence relation. Indeed, {lean}`r'` is the _kernel_ of the function
{lean}`fun a => Quot.mk r a`.  The axiom {lean}`Quot.sound` says that {lean}`r a b`
implies {lean}`r' a b`. Using {lean}`Quot.lift` and {lean}`Quot.ind`, we can show
that {lean}`r'` is the smallest equivalence relation containing {lean}`r`, in
the sense that if {lean}`r''` is any equivalence relation containing
{lean}`r`, then {lean}`r' a b` implies {lean}`r'' a b`. In particular, if {lean}`r`
was an equivalence relation to start with, then for all {lean}`a` and
{lean}`b` we have {lean}`r a b` iff {lean}`r' a b`.
:::

To support this common use case, the standard library defines the
notion of a _setoid_, which is simply a type with an associated
equivalence relation:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
------
end Hidden
```

Given a type {leanRef in:= "Setoid (α"}`α`, a relation {leanRef in:="Equivalence r"}`r`
on {leanRef in:= "Setoid (α"}`α`, and a proof {leanRef}`iseqv`
that {leanRef in:="Equivalence r"}`r` is an equivalence relation, we can define an
instance of the {leanRef in:="class Setoid"}`Setoid` class.

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
------
end Hidden
```

:::setup
````
variable (α : Type u) [Setoid α] (a b : α)
````


The constants {lean}`Quotient.mk`, {lean}`Quotient.ind`, {lean}`Quotient.lift`,
and {lean}`Quotient.sound` are nothing more than the specializations of
the corresponding elements of {lean}`Quot`. The fact that type class
inference can find the setoid associated to a type {lean}`α` brings a
number of benefits. First, we can use the notation {lean}`a ≈ b` (entered
with {kbd}`\approx`) for {lean}`Setoid.r a b`, where the instance of
{lean}`Setoid` is implicit in the notation {lean}`Setoid.r`. We can use the
generic theorems {lean}`Setoid.refl`, {lean}`Setoid.symm`, {lean}`Setoid.trans` to
reason about the relation. Specifically with quotients we can use the
theorem {lean}`Quotient.exact`:



```lean
universe u
------
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)
```

Together with {lean}`Quotient.sound`, this implies that the elements of
the quotient correspond exactly to the equivalence classes of elements
in {lean}`α`.

:::

:::setup
````
variable (α : Type u) (β : Type v)
````

Recall that in the standard library, {lean}`α × β` represents the
Cartesian product of the types {lean}`α` and {lean}`β`. To illustrate the use
of quotients, let us define the type of _unordered_ pairs of elements
of a type {lean}`α` as a quotient of the type {lean}`α × α`. First, we define
the relevant equivalence relation:
:::
```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

The next step is to prove that {leanRef}`eqv` is in fact an equivalence
relation, which is to say, it is reflexive, symmetric and
transitive. We can prove these three facts in a convenient and
readable way by using dependent pattern matching to perform
case-analysis and break the hypotheses into pieces that are then
reassembled to produce the conclusion.

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
------
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

:::leanFirst
Now that we have proved that {leanRef}`eqv` is an equivalence relation, we
can construct a {leanRef}`Setoid (α × α)`, and use it to define the type
{leanRef}`UProd α` of unordered pairs.

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
------
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```
:::

:::setup
````
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)


notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd

variable (a₁ a₂ : α)
````

Notice that we locally define the notation {lean}`{a₁, a₂}` for unordered
pairs as {lean}`Quotient.mk' (a₁, a₂)`. This is useful for illustrative
purposes, but it is not a good idea in general, since the notation
will shadow other uses of curly brackets, such as for records and
sets.

We can easily prove that {lean}`{a₁, a₂} = {a₂, a₁}` using {lean}`Quot.sound`,
since we have {lean}`(a₁, a₂) ~ (a₂, a₁)`.
:::

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
------
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
end UProd
```

:::leanFirst
To complete the example, given {leanRef}`a : α` and {leanRef}`u : UProd α`, we
define the proposition {leanRef in:="mem (a : α) (u : UProd α)"}`a`{lit}` ∈ `{leanRef in:="mem (a : α) (u : UProd α)"}`u` which should hold if {leanRef in:="mem (a : α) (u : UProd α)"}`a` is one of
the elements of the unordered pair {leanRef in:="mem (a : α) (u : UProd α)"}`u`. First, we define a similar
proposition {leanRef}`mem_fn`{leanRef in:="mem (a : α) (u : UProd α)"}` a`{leanRef in:="mem (a : α) (u : UProd α)"}` u` on (ordered) pairs; then we show that
{leanRef}`mem_fn` respects the equivalence relation {leanRef}`eqv` with the lemma
{leanRef}`mem_respects`. This is an idiom that is used extensively in the
Lean standard library.

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h

private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all only; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
---------
end UProd
```
:::

For convenience, the standard library also defines {lean}`Quotient.lift₂`
for lifting binary functions, and {lit}`Quotient.ind₂` for induction on
two variables.

:::setup
````
variable (α : Sort u) (β : α → Sort v) (f₁ f₂ f : (x : α) → β x) (a : α)

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} : extfun α β → (x : α) → β x := fun f x =>
  Quot.lift (· x) (by intros; simp [*]) f

````

We close this section with some hints as to why the quotient
construction implies function extensionality. It is not hard to show
that extensional equality on the {lean}`(x : α) → β x` is an equivalence
relation, and so we can consider the type {lean}`extfun α β` of functions
"up to equivalence." Of course, application respects that equivalence
in the sense that if {lean}`f₁` is equivalent to {lean}`f₂`, then {lean}`f₁ a` is
equal to {lean}`f₂ a`. Thus application gives rise to a function
{lean}`extfun_app : extfun α β → (x : α) → β x`. But for every {lean}`f`,
{lean}`extfun_app (.mk _ f)` is definitionally equal to {lean}`fun x => f x`, which is
in turn definitionally equal to {lean}`f`. So, when {lean}`f₁` and {lean}`f₂` are
extensionally equal, we have the following chain of equalities:

```lean
variable {α : Sort u} {β : α → Sort v}

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} (f : extfun α β) (x : α) : β x :=
  Quot.lift (· x) (by intros; simp [*]) f
---
example (f₁ f₂ : (x : α) → β x) (h : ∀ x, f₁ x = f₂ x) :=
  calc f₁
    _ = extfun_app (.mk _ f₁) := rfl
    _ = extfun_app (.mk _ f₂) := by rw [Quot.sound]; trivial
    _ = f₂ := rfl

```

As a result, {leanRef}`f₁` is equal to {leanRef}`f₂`.

:::

# Choice

:::leanFirst
To state the final axiom defined in the standard library, we need the
{leanRef}`Nonempty` type, which is defined as follows:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
------
end Hidden
```
:::

:::setup
````
variable {α : Sort u}
````

Because {lean}`Nonempty α` has type {lean}`Prop` and its constructor contains data, it can only eliminate to {lean}`Prop`.
In fact, {lean}`Nonempty α` is equivalent to {lean}`∃ x : α, True`:
:::

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

Our axiom of choice is now expressed simply as follows:

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
------
axiom choice {α : Sort u} : Nonempty α → α
------
end Hidden
```

:::setup
````
variable {α : Sort u} {h : Nonempty α}
open Classical
````

Given only the assertion {lean}`h` that {lean}`α` is nonempty, {lean}`choice h`
magically produces an element of {lean}`α`. Of course, this blocks any
meaningful computation: by the interpretation of {lean}`Prop`, {lean}`h`
contains no information at all as to how to find such an element.

:::

This is found in the {lit}`Classical` namespace, so the full name of the
theorem is {lean}`Classical.choice`. The choice principle is equivalent to
the principle of *indefinite description*, which can be expressed with
subtypes as follows:

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
axiom choice {α : Sort u} : Nonempty α → α
------
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
------
end Hidden
```

:::setup
````
variable {α : Sort u} {h : Nonempty α}
open Classical
````
Because it depends on {lean}`choice`, Lean cannot generate bytecode for
{lean}`indefiniteDescription`, and so requires us to mark the definition
as {kw}`noncomputable`. Also in the {lit}`Classical` namespace, the
function {lean}`choose` and the property {lean}`choose_spec` decompose the two
parts of the output of {lean}`indefiniteDescription`:



```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
open Classical
namespace Hidden
------
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
------
end Hidden
```

The {lean}`choice` principle also erases the distinction between the
property of being {lean}`Nonempty` and the more constructive property of
being {lean}`Inhabited`:

```lean
open Classical
------
noncomputable def inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```
:::

In the next section, we will see that {lean}`propext`, {lean}`funext`, and
{leanRef}`choice`, taken together, imply the law of the excluded middle and
the decidability of all propositions. Using those, one can strengthen
the principle of indefinite description as follows:

```lean
open Classical
universe u
------
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x})
```

Assuming the ambient type {leanRef}`α` is nonempty,
{leanRef}`strongIndefiniteDescription`{lit}` `{leanRef}`p` produces an element of {leanRef}`α`
satisfying {leanRef}`p` if there is one. The data component of this
definition is conventionally known as *Hilbert's epsilon function*:

```lean
open Classical
universe u
------
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))
```

# The Law of the Excluded Middle

The law of the excluded middle is the following

```lean
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)
```

[Diaconescu's theorem](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) states
that the axiom of choice is sufficient to derive the law of excluded
middle. More precisely, it shows that the law of the excluded middle
follows from {lean}`Classical.choice`, {lean}`propext`, and {lean}`funext`. We
sketch the proof that is found in the standard library.

:::leanFirst
First, we import the necessary axioms, and define two predicates {leanRef}`U` and {leanRef}`V`:

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
-------
  sorry
end Hidden
```
:::

If {leanRef}`p` is true, then every element of {lean}`Prop` is in both {leanRef}`U` and {leanRef}`V`.
If {leanRef}`p` is false, then {leanRef}`U` is the singleton {leanRef}`True`, and {leanRef}`V` is the singleton {leanRef}`False`.

:::leanFirst
Next, we use {leanRef}`choose` to choose an element from each of {leanRef}`U` and {leanRef}`V`:

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
------
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
-------
  sorry
end Hidden
```
:::

:::leanFirst
Each of {leanRef}`U` and {leanRef}`V` is a disjunction, so {leanRef}`u_def` and {leanRef}`v_def`
represent four cases. In one of these cases, {leanRef}`u`{leanRef}`= True` and
{leanRef}`v`{leanRef}` = False`, and in all the other cases, {leanRef}`p` is true. Thus we have:

```lean
namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
------
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
------
  sorry
end Hidden
```
:::

On the other hand, if {leanRef}`p` is true, then, by function extensionality
and propositional extensionality, {leanRef}`U` and {leanRef}`V` are equal. By the
definition of {leanRef}`u` and {leanRef}`v`, this implies that they are equal as well.

```lean
namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
------
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
------
  sorry
end Hidden
```

Putting these last two facts together yields the desired conclusion:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
------
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
------
end Hidden
```

Consequences of excluded middle include double-negation elimination,
proof by cases, and proof by contradiction, all of which are described
in the [Section Classical Logic](./propositions_and_proofs.md#classical-logic).
The law of the excluded middle and propositional extensionality imply propositional completeness:

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
------
end Hidden
```

Together with choice, we also get the stronger principle that every
proposition is decidable. Recall that the class of {lean}`Decidable`
propositions is defined as follows:

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

::::setup
````
variable {p : Prop} {f : α → β} {c : Prop} [Decidable c] {t e : α}
open Classical (choose propDecidable)
````
:::leanFirst
In contrast to {lean}`p ∨ ¬ p`, which can only eliminate to {lean}`Prop`, the
type {lean}`Decidable p` is equivalent to the sum type {lit}`Sum p (¬ p)`, which
can eliminate to any type. It is this data that is needed to write an
if-then-else expression.

As an example of classical reasoning, we use {lean}`choose` to show that if
{lean}`f : α → β` is injective and {lean}`α` is inhabited, then {lean}`f` has a
left inverse. To define the left inverse {leanRef}`linv`, we use a dependent
if-then-else expression. Recall that {lean}`if h : c then t else e` is
notation for {lean}`dite c (fun h : c => t) (fun h : ¬ c => e)`. In the definition
of {leanRef}`linv`, choice is used twice: first, to show that
{leanRef}`(∃ a : α, f a = b)` is "decidable," and then to choose an {leanRef}`a` such that
{leanRef}`f a = b`. Notice that {lean}`propDecidable` is a scoped instance and is activated
by the {leanRef}`open Classical` command. We use this instance to justify
the if-then-else expression. (See also the discussion in
[Section Decidable Propositions](./type_classes.md#decidable-propositions)).


```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := rfl
      _ = a         := inj feq
```

From a classical point of view, {leanRef}`linv` is a function. From a
constructive point of view, it is unacceptable; because there is no
way to implement such a function in general, the construction is not
informative.
:::
::::
