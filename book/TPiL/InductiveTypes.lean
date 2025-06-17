import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "Inductive Types" =>
%%%
tag := "inductive-types"
%%%

:::setup
````
variable {α : Sort u} {β : Sort v}
````


We have seen that Lean's formal foundation includes basic types,
{lean}`Prop`, {lean}`Type 0`, {lean}`Type 1`, {lean}`Type 2`, ..., and allows for the formation of
dependent function types, {lean}`(x : α) → β`. In the examples, we have
also made use of additional types like {lean}`Bool`, {lean}`Nat`, and {lean}`Int`,
and type constructors, like {lean}`List`, and product, {lit}`×`. In fact, in
Lean's library, every concrete type other than the universes and every
type constructor other than dependent arrows is an instance of a general family of
type constructions known as _inductive types_. It is remarkable that
it is possible to construct a substantial edifice of mathematics based
on nothing more than the type universes, dependent arrow types, and inductive
types; everything else follows from those.
:::

Intuitively, an inductive type is built up from a specified list of
constructors. In Lean, the syntax for specifying such a type is as
follows:

:::setup
```
variable {α β ω : Type}

inductive Foo where
  | constructor₁ : α → Foo
  | constructor₂ : β → Foo
  | constructorₙ : ω → Foo

```

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

The intuition is that each constructor specifies a way of building new
objects of {lean}`Foo`, possibly from previously constructed values. The
type {lean}`Foo` consists of nothing more than the objects that are
constructed in this way.



We will see below that the arguments of the constructors can include
objects of type {lean}`Foo`, subject to a certain “positivity” constraint,
which guarantees that elements of {lean}`Foo` are built from the bottom
up. Roughly speaking, each {lit}`...` can be any arrow type constructed from
{lean}`Foo` and previously defined types, in which {lean}`Foo` appears, if at
all, only as the “target” of the dependent arrow type.
:::

We will provide a number of examples of inductive types. We will also
consider slight generalizations of the scheme above, to mutually
defined inductive types, and so-called _inductive families_.

As with the logical connectives, every inductive type comes with
introduction rules, which show how to construct an element of the
type, and elimination rules, which show how to “use” an element of the
type in another construction. The analogy to the logical connectives
should not come as a surprise; as we will see below, they, too, are
examples of inductive type constructions. You have already seen the
introduction rules for an inductive type: they are just the
constructors that are specified in the definition of the type. The
elimination rules provide for a principle of recursion on the type,
which includes, as a special case, a principle of induction as well.

In the next chapter, we will describe Lean's function definition
package, which provides even more convenient ways to define functions
on inductive types and carry out inductive proofs. But because the
notion of an inductive type is so fundamental, we feel it is important
to start with a low-level, hands-on understanding. We will start with
some basic examples of inductive types, and work our way up to more
elaborate and complex examples.

# Enumerated Types

The simplest kind of inductive type is a type with a finite, enumerated list of elements.

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

The {kw}`inductive` command creates a new type, {leanRef}`Weekday`. The
constructors all live in the {lit}`Weekday` namespace.

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
#check Weekday.sunday

#check Weekday.monday

open Weekday

#check sunday

#check monday
```

You can omit {leanRef}`: Weekday` when declaring the {leanRef}`Weekday` inductive type.

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

:::setup
````
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
````

Think of {leanRef}`sunday`, {leanRef}`monday`, ... , {leanRef}`saturday` as
being distinct elements of {leanRef}`Weekday`, with no other distinguishing
properties. The elimination principle, {name}`Weekday.rec`, is defined
along with the type {leanRef}`Weekday` and its constructors. It is also known
as a _recursor_, and it is what makes the type “inductive”: it allows
us to define a function on {leanRef}`Weekday` by assigning values
corresponding to each constructor. The intuition is that an inductive
type is exhaustively generated by the constructors, and has no
elements beyond those they construct.

```signature
Weekday.rec.{u} {motive : Weekday → Sort u}
  (sunday : motive Weekday.sunday)
  (monday : motive Weekday.monday)
  (tuesday : motive Weekday.tuesday)
  (wednesday : motive Weekday.wednesday)
  (thursday : motive Weekday.thursday)
  (friday : motive Weekday.friday)
  (saturday : motive Weekday.saturday)
  (t : Weekday) :
  motive t
```

:::

:::leanFirst
We will use the {kw}`match` expression to define a function from {leanRef}`Weekday`
to the natural numbers:

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1

#eval numberOfDay Weekday.monday  -- 2

#eval numberOfDay Weekday.tuesday -- 3
```

When using Lean's logic, the {kw}`match` expression is compiled using the _recursor_ {leanRef}`Weekday.rec` generated when
you declare the inductive type. This ensures that the resulting term is well-defined in the type theory. For compiled code,
{kw}`match` is compiled as in other functional programming languages.
:::

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay

#print numberOfDay.match_1

#print Weekday.casesOn

#check @Weekday.rec
```

:::leanFirst
When declaring an inductive datatype, you can use {leanRef}`deriving Repr` to instruct
Lean to generate a function that converts {leanRef}`Weekday` objects into text.
This function is used by the {kw}`#eval` command to display {leanRef}`Weekday` objects.
If no {lean}`Repr` exists, {kw}`#eval` attempts to derive one on the spot.

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```
:::

It is often useful to group definitions and theorems related to a
structure in a namespace with the same name. For example, we can put
the {leanRef}`numberOfDay` function in the {lit}`Weekday` namespace. We are
then allowed to use the shorter name when we open the namespace.

:::leanFirst
We can define functions from {leanRef}`Weekday` to {leanRef}`Weekday`:

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
------
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday

#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```
:::

:::leanFirst
How can we prove the general theorem that {leanRef}`next (previous d) = d`
for any Weekday {leanRef}`d`? You can use {kw}`match` to provide a proof of the claim for each
constructor:

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```
:::

Using a tactic proof, we can be even more concise:

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

{ref "tactics-for-inductive-types"}[Tactics for Inductive Types] below will introduce additional
tactics that are specifically designed to make use of inductive types.

Notice that, under the {tech}[propositions-as-types] correspondence, we can
use {kw}`match` to prove theorems as well as define functions.  In other
words, under the {tech}[propositions-as-types] correspondence, the proof by
cases is a kind of definition by cases, where what is being “defined”
is a proof instead of a piece of data.

The {lean}`Bool` type in the Lean library is an instance of
enumerated type.

```lean
namespace Hidden
------
inductive Bool where
  | false : Bool
  | true  : Bool
------
end Hidden
```

(To run these examples, we put them in a namespace called {lit}`Hidden`,
so that a name like {leanRef}`Bool` does not conflict with the {lean}`Bool` in
the standard library. This is necessary because these types are part
of the Lean “prelude” that is automatically imported when the system
is started.)


As an exercise, you should think about what the introduction and
elimination rules for these types do. As a further exercise, we
suggest defining boolean operations {lean}`and`, {lean}`or`, {lean}`not` on the
{leanRef}`Bool` type, and verifying common identities. Note that you can define a
binary operation like {leanRef}`and` using {kw}`match`:

```lean
namespace Hidden
------
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
-------
end Hidden
```

Similarly, most identities can be proved by introducing suitable {kw}`match`, and then using {lean}`rfl`.

# Constructors with Arguments

:::setup
````
variable (α : Type u) (β : Type v) (a : α) (b : β)
````


Enumerated types are a very special case of inductive types, in which
the constructors take no arguments at all. In general, a
“construction” can depend on data, which is then represented in the
constructed argument. Consider the definitions of the product type and
sum type in the library:

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
-------
end Hidden
```

Consider what is going on in these examples.
The product type has one constructor, {lean}`Prod.mk`,
which takes two arguments. To define a function on {leanRef}`Prod α β`, we
can assume the input is of the form {lean}`Prod.mk a b`, and we have to
specify the output, in terms of {leanRef}`a` and {leanRef}`b`. We can use this to
define the two projections for {leanRef}`Prod`. Remember that the standard
library defines notation {lean}`α × β` for {leanRef}`Prod α β` and {lean}`(a, b)` for
{lean}`Prod.mk a b`.

```lean
namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
------
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
--------
end Hidden
```

The function {leanRef}`fst` takes a pair, {leanRef}`p`. The {kw}`match` interprets
{leanRef}`p` as a pair, {leanRef}`Prod.mk a b`. Recall also from {ref "dependent-type-theory"}[Dependent Type Theory]
that to give these definitions the greatest generality possible, we allow
the types {leanRef}`α` and {leanRef}`β` to belong to any universe.

:::
:::setup
```
universe u_2 u_3 u_1
variable (b : Bool) {α : Type u} {t1 t2 : α}
```

Here is another example where we use the recursor {lean type:="{α : Type u_2} → {β : Type u_3} → {motive : α × β → Sort u_1} → (t : α × β) → ((fst : α) → (snd : β) → motive (fst, snd)) → motive t"}`Prod.casesOn` instead
of {kw}`match`.

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)

#eval prod_example (false, 3)
```

The argument {leanRef}`motive` is used to specify the type of the object you want to
construct, and it is a function because it may depend on the pair.
The {leanRef}`cond` function is a boolean conditional: {lean}`cond b t1 t2`
returns {lean}`t1` if {lean}`b` is true, and {lean}`t2` otherwise.
The function {leanRef}`prod_example` takes a pair consisting of a boolean,
{leanRef}`b`, and a number, {leanRef}`n`, and returns either {leanRef}`2 * n` or {leanRef}`2 * n + 1`
according to whether {leanRef}`b` is true or false.
:::

:::setup
````
open Sum
variable {α : Type u} {β : Type v} (a : α) (b : β)
````

In contrast, the sum type has _two_ constructors, {lean}`inl` and {lean}`inr`
(for “insert left” and “insert right”), each of which takes _one_
(explicit) argument. To define a function on {lean}`Sum α β`, we have to
handle two cases: either the input is of the form {lean}`inl a`, in which
case we have to specify an output value in terms of {leanRef}`a`, or the
input is of the form {lean}`inr b`, in which case we have to specify an
output value in terms of {leanRef}`b`.

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)

#eval sum_example (Sum.inr 3)
```

:::

:::setup
````
open Sum
variable (n : Nat)
````

This example is similar to the previous one, but now an input to
{leanRef}`sum_example` is implicitly either of the form {lean}`inl n` or {lean}`inr n`.
In the first case, the function returns {lean}`2 * n`, and the second
case, it returns {lean}`2 * n + 1`.

:::

:::setup
````
variable {α β : Type} {a : α} {b : β}
open Sum
````


Notice that the product type depends on parameters {lean}`α β : Type`
which are arguments to the constructors as well as {lean}`Prod`. Lean
detects when these arguments can be inferred from later arguments to a
constructor or the return type, and makes them implicit in that case.

In {ref "defining-the-natural-numbers"}[Defining the Natural Numbers]
we will see what happens when the
constructor of an inductive type takes arguments from the inductive
type itself. What characterizes the examples we consider in this
section is that each constructor relies only on previously specified types.

Notice that a type with multiple constructors is disjunctive: an
element of {lean}`Sum α β` is either of the form {lean}`inl a` _or_ of the
form {lean}`inl b`. A constructor with multiple arguments introduces
conjunctive information: from an element {lean}`Prod.mk a b` of
{lean}`Prod α β` we can extract {leanRef}`a` _and_ {leanRef}`b`. An arbitrary inductive type can
include both features, by having any number of constructors, each of
which takes any number of arguments.

:::

As with function definitions, Lean's inductive definition syntax will
let you put named arguments to the constructors before the colon:

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
-------
end Hidden
```

The results of these definitions are essentially the same as the ones given earlier in this section.

A type, like {leanRef}`Prod`, that has only one constructor is purely
conjunctive: the constructor simply packs the list of arguments into a
single piece of data, essentially a tuple where the type of subsequent
arguments can depend on the type of the initial argument. We can also
think of such a type as a “record” or a “structure”. In Lean, the
keyword {kw}`structure` can be used to define such an inductive type as
well as its projections, at the same time.

```lean
namespace Hidden
------
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
-------
end Hidden
```

This example simultaneously introduces the inductive type, {leanRef}`Prod`,
its constructor, {leanRef}`mk`, the usual eliminators ({lit}`rec` and
{lit}`recOn`), as well as the projections, {leanRef}`fst` and {leanRef}`snd`, as
defined above.

If you do not name the constructor, Lean uses {lit}`mk` as a default. For
example, the following defines a record to store a color as a triple
of RGB values:

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

The definition of {leanRef}`yellow` forms the record with the three values
shown, and the projection {leanRef}`Color.red` returns the red component.

The {kw}`structure` command is especially useful for defining algebraic
structures, and Lean provides substantial infrastructure to support
working with them. Here, for example, is the definition of a
semigroup:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

We will see more examples in the chapter on {ref "structures-and-records"}[structures and records].

:::leanFirst
We have already discussed the dependent product type {leanRef}`Sigma`:

```lean
namespace Hidden
------
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
-------
end Hidden
```
:::

Two more examples of inductive types in the library are the following:

```lean
namespace Hidden
------
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
-------
end Hidden
```

:::setup
````
variable {α : Type u} {β : Type v} {γ : Type u'} (b : β) (f : α → Option β) (a : α)
````

In the semantics of dependent type theory, there is no built-in notion
of a partial function. Every element of a function type {lean}`α → β` or a
dependent function type {lean}`(a : α) → β` is assumed to have a value
at every input. The {lean}`Option` type provides a way of representing partial functions. An
element of {lean}`Option β` is either {lean}`none` or of the form {lean}`some b`,
for some value {lean}`b : β`. Thus we can think of an element {lean}`f` of the
type {lean}`α → Option β` as being a partial function from {lean}`α` to {lean}`β`:
for every {lean}`a : α`, {lean}`f a` either returns {lean type:="Option β"}`none`, indicating
{lean}`f a` is “undefined”, or {lean}`some b`.

An element of {lean}`Inhabited α` is simply a witness to the fact that
there is an element of {lean}`α`. Later, we will see that {lean}`Inhabited` is
an example of a _type class_ in Lean: Lean can be instructed that
suitable base types are inhabited, and can automatically infer that
other constructed types are inhabited on that basis.

As exercises, we encourage you to develop a notion of composition for
partial functions from {lean}`α` to {lean}`β` and {lean}`β` to {lean}`γ`, and show
that it behaves as expected. We also encourage you to show that
{lean}`Bool` and {lean}`Nat` are inhabited, that the product of two inhabited
types is inhabited, and that the type of functions to an inhabited
type is inhabited.

:::

# Inductively Defined Propositions

Inductively defined types can live in any type universe, including the
bottom-most one, {lean}`Prop`. In fact, this is exactly how the logical
connectives are defined.

```lean
namespace Hidden
------
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
-------
end Hidden
```

:::setup
````
variable (p : Prop) (hp : p) (α : Type u) (β : Type v)
````

You should think about how these give rise to the introduction and
elimination rules that you have already seen. There are rules that
govern what the eliminator of an inductive type can eliminate _to_,
that is, what kinds of types can be the target of a recursor. Roughly
speaking, what characterizes inductive types in {lean}`Prop` is that one
can only eliminate to other types in {lean}`Prop`. This is consistent with
the understanding that if {lean}`p : Prop`, an element {lean}`hp : p` carries
no data. There is a small exception to this rule, however, which we
will discuss below, in {ref "inductive-families"}[Inductive Families].


Even the existential quantifier is inductively defined:

```lean
namespace Hidden
------
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
-------
end Hidden
```

Keep in mind that the notation {lean}`∃ x : α, p` is syntactic sugar for {lean}`Exists (fun x : α => p)`.


The definitions of {lean}`False`, {lean}`True`, {lean}`And`, and {lean}`Or` are
perfectly analogous to the definitions of {lean}`Empty`, {lean}`Unit`,
{lean}`Prod`, and {lean}`Sum`. The difference is that the first group yields
elements of {lean}`Prop`, and the second yields elements of {lean}`Type u` for
some {leanRef}`u`. In a similar way, {leanRef}`∃ x : α, p` is a {lean}`Prop`-valued
variant of {lean}`Σ x : α, β`.

:::

::::setup
````
variable (α : Type u) (β : Type v) (p : Prop)
````

This is a good place to mention another inductive type, denoted
{lean}`{x : α // p}`, which is sort of a hybrid between
{lean}`∃ x : α, p` and {lean}`Σ x : α, β`.

```lean
namespace Hidden
------
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
-------
end Hidden
```
::::
::::setup
````
variable {α : Type u} {p : α → Prop}
````

:::leanFirst
In fact, in Lean, {leanRef}`Subtype` is defined using the structure command:

```lean
namespace Hidden
------
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
-------
end Hidden
```


The notation {lean}`{x : α // p x}` is syntactic sugar for {lean}`Subtype (fun x : α => p x)`.
It is modeled after subset notation in set theory: the idea is that {leanRef}`{x : α // p x}`
denotes the collection of elements of {leanRef}`α` that have property {leanRef}`p`.
:::

::::

# Defining the Natural Numbers
%%%
tag := "defining-the-natural-numbers"
%%%

The inductively defined types we have seen so far are “flat”:
constructors wrap data and insert it into a type, and the
corresponding recursor unpacks the data and acts on it. Things get
much more interesting when the constructors act on elements of the
very type being defined. A canonical example is the type {lean}`Nat` of
natural numbers:

```lean
namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
-------
end Hidden
```

:::setup
````
open Nat
variable {motive : Nat → Sort u} {f : (n : Nat) → motive n} {n : Nat}
````

There are two constructors. We start with {lean}`zero : Nat`; it takes
no arguments, so we have it from the start. In contrast, the
constructor {lean}`succ` can only be applied to a previously constructed
{lean}`Nat`. Applying it to {lean}`zero` yields {lean}`succ zero : Nat`. Applying
it again yields {lean}`succ (succ zero) : Nat`, and so on. Intuitively,
{lean}`Nat` is the “smallest” type with these constructors, meaning that
it is exhaustively (and freely) generated by starting with {lean}`zero`
and applying {lean}`succ` repeatedly.


As before, the recursor for {lean}`Nat` is designed to define a dependent
function {lean}`f` from {lean}`Nat` to any domain, that is, an element {lean}`f`
of {lean}`(n : Nat) → motive n` for some {lean}`motive : Nat → Sort u`.
It has to handle two cases: the case where the input is {lean}`zero`, and the case where
the input is of the form {lean}`succ n` for some {lean}`n : Nat`. In the first
case, we simply specify a target value with the appropriate type, as
before. In the second case, however, the recursor can assume that a
value of {lean}`f` at {lean}`n` has already been computed. As a result, the
next argument to the recursor specifies a value for {lean}`f (succ n)` in
terms of {lean}`n` and {lean}`f n`. If we check the type of the recursor,
you find the following:
:::

```signature
Nat.rec.{u} :
  {motive : Nat → Sort u} →
  (zero : motive Nat.zero) →
  (succ : (n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) → motive t
```

The implicit argument, {leanRef}`motive`, is the codomain of the function being defined.
In type theory it is common to say {leanRef}`motive` is the _motive_ for the elimination/recursion,
since it describes the kind of object we wish to construct.
The next two arguments specify how to compute the zero and successor cases, as described above.
They are also known as the _minor premises_.
Finally, the {leanRef}`t : Nat`, is the input to the function. It is also known as the _major premise_.

The {name}`Nat.recOn` is similar to {name}`Nat.rec` but the major premise occurs before the minor premises.

```signature
Nat.recOn.{u} :
  {motive : Nat → Sort u} →
  (t : Nat) →
  (zero : motive Nat.zero) →
  (succ : ((n : Nat) → motive n → motive (Nat.succ n))) →
  motive t
```

:::setup
````
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
variable {n m : Nat}
open Nat
````

Consider, for example, the addition function {lean}`add m n` on the
natural numbers. Fixing {lean}`m`, we can define addition by recursion on
{lean}`n`. In the base case, we set {lean}`add m zero` to {lean}`m`. In the
successor step, assuming the value {lean}`add m n` is already determined,
we define {lean}`add m (succ n)` to be {lean}`succ (add m n)`.
:::

```lean
namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
-------
end Hidden
```


It is useful to put such definitions into a namespace, {lean}`Nat`. We can
then go on to define familiar notation in that namespace. The two
defining equations for addition now hold definitionally:

```lean
namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr
------
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
-------
end Hidden
```

We will explain how the {kw}`instance` command works in
the {ref "type-classes"}[Type Classes] chapter. In the examples below, we will use
Lean's version of the natural numbers.

::::leanFirst

:::setup
````
variable {n : Nat} {motive : Nat → Sort u} {ih : motive n}
````

Proving a fact like {lean}`0 + n = n`, however, requires a proof by induction.
As observed above, the induction principle is just a special case of the recursion principle,
when the codomain {lean}`motive n` is an element of {lean}`Prop`. It represents the familiar
pattern of an inductive proof: to prove {lean}`∀ n, motive n`, first prove {lean}`motive 0`,
and then, for arbitrary {lean}`n`, assume {lean}`ih : motive n` and prove {lean}`motive (n + 1)`.
:::

```lean
namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + (n + 1) = n + 1 from
    calc 0 + (n + 1)
      _ = (0 + n) + 1 := rfl
      _ = n + 1       := by rw [ih])
-------
end Hidden
```

::::

Notice that, once again, when {name}`Nat.recOn` is used in the context of
a proof, it is really the induction principle in disguise. The
{tactic}`rw` and {tactic}`simp` tactics tend to be very effective in proofs
like these. In this case, each can be used to reduce the proof to:


```lean
namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [ih])
-------
end Hidden
```

:::setup
````
variable (m n k : Nat)
````

As another example, let us prove the associativity of addition,
{lean}`∀ m n k, m + n + k = m + (n + k)`.
(The notation {leanRef}`+`, as we have defined it, associates to the left, so {leanRef}`m + n + k` is really {lean}`(m + n) + k`.)
The hardest part is figuring out which variable to do the induction on. Since addition is defined by recursion on the second argument,
{leanRef in:="n k,"}`k` is a good guess, and once we make that choice the proof almost writes itself:
:::

```lean
namespace Hidden
------
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + (k + 1) = m + (n + (k + 1)) from
      calc m + n + (k + 1)
        _ = (m + n + k) + 1   := rfl
        _ = (m + (n + k)) + 1 := by rw [ih]
        _ = m + ((n + k) + 1) := rfl
        _ = m + (n + (k + 1)) := rfl)
-------
end Hidden
```

Once again, you can reduce the proof to:

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [add_succ (m + n) k, ih]; rfl)
```

Suppose we try to prove the commutativity of addition. Choosing induction on the second argument, we might begin as follows:

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)
```

At this point, we see that we need another supporting fact, namely, that {leanRef}`succ (n + m)`{lit}`  =  `{leanRef}`succ n + m`.
You can prove this by induction on {leanRef}`m`:

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)
```

You can then replace the {leanRef}`sorry` in the previous proof with {leanRef}`succ_add`. Yet again, the proofs can be compressed:

```lean
namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

namespace Nat
theorem add_zero (m : Nat) : m + zero = m := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun n ih => by simpa [add_zero, add_succ])

end Nat
------
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simpa [add_succ (succ n)])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp [add_zero, zero_add])
    (fun m ih => by simp_all [succ_add, add_succ])
-------
end Hidden
```

# Other Recursive Data Types

:::leanFirst
Let us consider some more examples of inductively defined types. For
any type, {leanRef}`α`, the type {leanRef}`List α` of lists of elements of {leanRef}`α` is
defined in the library.

```lean
namespace Hidden
------
inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
-------
end Hidden
```

A list of elements of type {leanRef}`α` is either the empty list, {leanRef}`nil`, or
an element {leanRef}`h : α` followed by a list {leanRef}`t : List α`.
The first element, {leanRef}`h`, is commonly known as the “head” of the list,
and the remainder, {leanRef}`t`, is known as the “tail.”
:::

As an exercise, prove the following:

```lean
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
------
theorem append_nil (as : List α) :
    append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  sorry
-------
end List
end Hidden
```

:::setup
````
universe u
def length : {α : Type u} → List α → Nat := List.length
def append : {α : Type u} → List α → List α → List α := List.append
variable (as bs : List α)
````

Try also defining the function {lean}`length : {α : Type u} → List α → Nat` that returns the length of a list,
and prove that it behaves as expected (for example, {lean}`length (append as bs) = length as + length bs`).
:::

For another example, we can define the type of binary trees:

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

In fact, we can even define the type of countably branching trees:

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

# Tactics for Inductive Types
%%%
tag := "tactics-for-inductive-types"
%%%

Given the fundamental importance of inductive types in Lean, it should
not be surprising that there are a number of tactics designed to work
with them effectively. We describe some of them here.

:::setup
````
variable {x : InductiveType}
````

The {tactic}`cases` tactic works on elements of an inductively defined type,
and does what the name suggests: it decomposes the element according
to each of the possible constructors. In its most basic form, it is
applied to an element {lean}`x` in the local context. It then reduces the
goal to cases in which {lean}`x` is replaced by each of the constructions.
:::

```lean
example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
--^ PROOF_STATE: A
  . apply hs
--^ PROOF_STATE: B
```

In the first branch, the proof state is:
```proofState A
case zero =>
  p: Nat → Prop
  hz: p 0
  hs: ∀ (n : Nat), p n.succ
⊢ p 0
```
In the second branch, it is:
```proofState B
case succ =>
  p: Nat → Prop
  hz: p 0
  hs: ∀ (n : Nat), p n.succ
  n✝: Nat
⊢ p (n✝ + 1)
```

:::leanFirst
There are extra bells and whistles. For one thing, {leanRef}`cases` allows
you to choose the names for each alternative using a
{leanRef}`with` clause. In the next example, for example, we choose the name
{leanRef}`m` for the argument to {leanRef}`succ`, so that the second case refers to
{leanRef}`succ m`. More importantly, the cases tactic will detect any items
in the local context that depend on the target variable. It reverts
these elements, does the split, and reintroduces them. In the example
below, notice that the hypothesis {leanRef}`h : n ≠ 0` becomes {leanRef}`h : 0 ≠ 0`
in the first branch, and {leanRef}`h : m + 1 ≠ 0` in the second.

```lean (showProofStates := "C D")
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
  --     ^ PROOF_STATE: C
    apply absurd rfl h
  | succ m =>
  --       ^ PROOF_STATE: D
    rfl
```
:::

Notice that {leanRef}`cases` can be used to produce data as well as prove propositions.

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

Once again, cases will revert, split, and then reintroduce dependencies in the context.

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

Here is an example of multiple constructors with arguments.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

The alternatives for each constructor don't need to be solved
in the order the constructors were declared.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

:::leanFirst
The syntax of the {leanRef}`with` is convenient for writing structured proofs.
Lean also provides a complementary {leanRef}`case` tactic, which allows you to focus on goal
assign variable names.

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```
:::

The {leanRef}`case` tactic is clever, in that it will match the constructor to the appropriate goal. For example, we can fill the goals above in the opposite order:

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

You can also use {leanRef}`cases` with an arbitrary expression. Assuming that
expression occurs in the goal, the cases tactic will generalize over
the expression, introduce the resulting universally quantified
variable, and case on that.

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)
```

Think of this as saying “split on cases as to whether {leanRef}`m + 3 * k` is
zero or the successor of some number.” The result is functionally
equivalent to the following:

```lean (showProofStates := "Z S")
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  -- ^ PROOF_STATE: Z
  exact hz
  -- ^ PROOF_STATE: S
  apply hs
```

Notice that the expression {leanRef}`m + 3 * k` is erased by {leanRef}`generalize`; all
that matters is whether it is of the form {leanRef}`0` or {leanRef}`n✝ + 1`. This
form of {leanRef}`cases` will _not_ revert any hypotheses that also mention
the expression in the equation (in this case, {leanRef}`m + 3 * k`). If such a
term appears in a hypothesis and you want to generalize over that as
well, you need to {tactic}`revert` it explicitly.

If the expression you case on does not appear in the goal, the
{tactic}`cases` tactic uses {tactic}`have` to put the type of the expression into
the context. Here is an example:

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  --           ^ PROOF_STATE: one
  case inr hge => exact h₂ hge
  --           ^ PROOF_STATE: two
```

The theorem {leanRef}`Nat.lt_or_ge m n` says {leanRef}`m < n`{lit}`  ∨  `{leanRef}`m ≥ n`, and it is
natural to think of the proof above as splitting on these two
cases. In the first branch, we have the hypothesis {leanRef}`hlt : m < n`, and
in the second we have the hypothesis {leanRef}`hge : m ≥ n`. The proof above
is functionally equivalent to the following:

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

After the first two lines, we have {leanRef}`h : m < n ∨ m ≥ n` as a
hypothesis, and we simply do cases on that.

:::leanFirst
Here is another example, where we use the decidability of equality on
the natural numbers to split on the cases {leanRef}`m = n` and {leanRef}`m ≠ n`.

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```
:::

Remember that if you {kw}`open `{lit}`Classical`, you can use the law of the
excluded middle for any proposition at all. But using type class
inference (see {ref "type-classes"}[Type Classes]), Lean can actually
find the relevant decision procedure, which means that you can use the
case split in a computable function.

:::leanFirst
Just as the {leanRef}`cases` tactic can be used to carry out proof by cases,
the {leanRef}`induction` tactic can be used to carry out proofs by
induction. The syntax is similar to that of {leanRef}`cases`, except that the
argument can only be a term in the local context. Here is an example:

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

:::leanFirst
As with {leanRef}`cases`, we can use the {leanRef}`case` tactic instead of {leanRef}`with`.

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

Here are some additional examples:
:::TODO
FIXME
:::
```lean
namespace Hidden
inductive Nat where
  | zero
  | succ : Nat → Nat

def Nat.toNat : Nat → _root_.Nat
  | .zero => .zero
  | .succ n => .succ n.toNat

def Nat.ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (.ofNat n)

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

instance : OfNat Nat n where
  ofNat := .ofNat n

@[simp]
theorem zero_zero : (.zero : Nat) = 0 := rfl
theorem add_zero (n : Nat) : n + 0 = n := rfl
theorem add_succ (n k : Nat) : n + k.succ = (n + k).succ := rfl
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
-------
end Hidden
```

The {leanRef}`induction` tactic also supports user-defined induction principles with
multiple targets (aka major premises). This example uses {name}`Nat.mod.inductionOn`, which has the following signature:
````signature
Nat.mod.inductionOn
  {motive : Nat → Nat → Sort u}
  (x y  : Nat)
  (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
  (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y) :
  motive x y
````


```lean
example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
```

You can use the {kw}`match` notation in tactics too:

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

:::leanFirst
As a convenience, pattern-matching has been integrated into tactics such as {leanRef}`intro` and {leanRef}`funext`.

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```
:::

:::leanFirst
We close this section with one last tactic that is designed to
facilitate working with inductive types, namely, the {leanRef}`injection`
tactic. By design, the elements of an inductive type are freely
generated, which is to say, the constructors are injective and have
disjoint ranges. The {leanRef}`injection` tactic is designed to make use of
this fact:

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```
:::

The first instance of the tactic adds {leanRef}`h' : m + 1 = n + 1` to the
context, and the second adds {leanRef}`h'' : m = n`.

The {leanRef}`injection` tactic also detects contradictions that arise when different constructors
are set equal to one another, and uses them to close the goal.

```lean
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

As the second example shows, the {leanRef}`contradiction` tactic also detects contradictions of this form.

# Inductive Families
%%%
tag := "inductive-families"
%%%

We are almost done describing the full range of inductive definitions
accepted by Lean. So far, you have seen that Lean allows you to
introduce inductive types with any number of recursive
constructors. In fact, a single inductive definition can introduce an
indexed _family_ of inductive types, in a manner we now describe.

An inductive family is an indexed family of types defined by a
simultaneous induction of the following form:

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```
::::setup
````
universe u
````

:::leanFirst
In contrast to an ordinary inductive definition, which constructs an
element of some {leanRef}`Sort u`, the more general version constructs a
function {lit}`... → `{lean}`Sort u`, where “{lit}`...`” denotes a sequence of
argument types, also known as _indices_. Each constructor then
constructs an element of some member of the family. One example is the
definition of {leanRef}`Vect α n`, the type of vectors of elements of {leanRef}`α`
of length {leanRef}`n`:

```lean
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::
::::

Notice that the {leanRef}`cons` constructor takes an element of
{leanRef}`Vect α n` and returns an element of {leanRef}`Vect α (n + 1)`, thereby using an
element of one member of the family to build an element of another.

A more exotic example is given by the definition of the equality type in Lean:

```lean
namespace Hidden
------
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
-------
end Hidden
```

:::setup
````
variable (α : Sort u) (a : α) (x : α)
````

For each fixed {leanRef}`α : Sort u` and {leanRef}`a : α`, this definition
constructs a family of types {lean}`Eq a x`, indexed by {lean}`x : α`.
Notably, however, there is only one constructor, {leanRef}`refl`, which
is an element of {leanRef}`Eq a a`.
Intuitively, the only way to construct a proof of {lean}`Eq a x`
is to use reflexivity, in the case where {lean}`x` is {lean}`a`.
Note that {lean}`Eq a a` is the only inhabited type in the family of types
{lean}`Eq a x`. The elimination principle generated by Lean is as follows:
:::

```lean
set_option pp.proofs true
--------
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} →
                  {motive : (x : α) → a = x → Sort v} →
                  motive a rfl →
                  {b : α} → (h : a = b) → motive b h)
```

It is a remarkable fact that all the basic axioms for equality follow
from the constructor, {leanRef}`refl`, and the eliminator, {leanRef}`Eq.rec`. The
definition of equality is atypical, however; see the discussion in {ref "axiomatic-details"}[Axiomatic Details].

The recursor {leanRef}`Eq.rec` is also used to define substitution:

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
-------
end Hidden
```

You can also define {leanRef}`subst` using {kw}`match`.

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
-------
end Hidden
```

Actually, Lean compiles the {kw}`match` expressions using a definition based on generated helpers
such as {name}`Eq.casesOn` and {name}`Eq.ndrec`, which are themselves defined using {leanRef}`Eq.rec`.

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : a = b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst

#print subst.match_1_1

#print Eq.casesOn

#print Eq.ndrec
-------
end Hidden
```

Using the recursor or {kw}`match` with {leanRef}`h₁ : a = b`, we may assume {leanRef}`a` and {leanRef}`b` are the same,
in which case, {leanRef}`p b` and {leanRef}`p a` are the same.

:::leanFirst
It is not hard to prove that {leanRef}`Eq` is symmetric and transitive.
In the following example, we prove {leanRef}`symm` and leave as exercises the theorems {leanRef}`trans` and {leanRef}`congr` (congruence).

```lean
namespace Hidden
------
variable {α β : Type u} {a b c : α}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
-------
end Hidden
```
:::

In the type theory literature, there are further generalizations of
inductive definitions, for example, the principles of
_induction-recursion_ and _induction-induction_. These are not
supported by Lean.

# Axiomatic Details
%%%
tag := "axiomatic-details"
%%%

We have described inductive types and their syntax through
examples. This section provides additional information for those
interested in the axiomatic foundations.

We have seen that the constructor to an inductive type takes
_parameters_—intuitively, the arguments that remain fixed
throughout the inductive construction—and _indices_, the arguments
parameterizing the family of types that is simultaneously under
construction. Each constructor should have a type, where the
argument types are built up from previously defined types, the
parameter and index types, and the inductive family currently being
defined. The requirement is that if the latter is present at all, it
occurs only _strictly positively_. This means simply that any argument
to the constructor in which it occurs is a dependent arrow type in which the
inductive type under definition occurs only as the resulting type,
where the indices are given in terms of constants and previous
arguments.

Since an inductive type lives in {leanRef}`Sort u` for some {leanRef}`u`, it is
reasonable to ask _which_ universe levels {leanRef}`u` can be instantiated
to. Each constructor {lit}`c` in the definition of a family {lit}`C` of
inductive types is of the form

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

where {lit}`a` is a sequence of data type parameters, {lit}`b` is the
sequence of arguments to the constructors, and {lit}`p[a, b]` are the
indices, which determine which element of the inductive family the
construction inhabits. (Note that this description is somewhat
misleading, in that the arguments to the constructor can appear in any
order as long as the dependencies make sense.) The constraints on the
universe level of {lit}`C` fall into two cases, depending on whether or
not the inductive type is specified to land in {lean}`Prop` (that is,
{lean}`Sort 0`).

Let us first consider the case where the inductive type is _not_
specified to land in {lean}`Prop`. Then the universe level {leanRef}`u` is
constrained to satisfy the following:

> For each constructor {lit}`c` as above, and each {lit}`βk[a]` in the sequence {lit}`β[a]`, if {lit}`βk[a] : Sort v`, we have {leanRef}`u` ≥ {leanRef}`v`.

In other words, the universe level {leanRef}`u` is required to be at least as
large as the universe level of each type that represents an argument
to a constructor.

When the inductive type is specified to land in {lean}`Prop`, there are no
constraints on the universe levels of the constructor arguments. But
these universe levels do have a bearing on the elimination
rule. Generally speaking, for an inductive type in {lean}`Prop`, the
motive of the elimination rule is required to be in {lean}`Prop`.

There is an exception to this last rule: we are allowed to eliminate
from an inductively defined {lean}`Prop` to an arbitrary {leanRef}`Sort` when
there is only one constructor and each constructor argument is either
in {lean}`Prop` or an index. The intuition is that in this case the
elimination does not make use of any information that is not already
given by the mere fact that the type of argument is inhabited. This
special case is known as _singleton elimination_.

We have already seen singleton elimination at play in applications of
{name}`Eq.rec`, the eliminator for the inductively defined equality
type. We can use an element {leanRef}`h : Eq a b` to cast an element
{leanRef}`h₂ : p a` to {leanRef}`p b` even when {leanRef}`p a` and {leanRef}`p b` are arbitrary types,
because the cast does not produce new data; it only reinterprets the
data we already have. Singleton elimination is also used with
heterogeneous equality and well-founded recursion, which will be
discussed in a the chapter on {ref "well-founded-recursion-and-induction"}[induction and recursion].

# Mutual and Nested Inductive Types

We now consider two generalizations of inductive types that are often
useful, which Lean supports by “compiling” them down to the more
primitive kinds of inductive types described above. In other words,
Lean parses the more general definitions, defines auxiliary inductive
types based on them, and then uses the auxiliary types to define the
ones we really want. Lean's equation compiler, described in the next
chapter, is needed to make use of these types
effectively. Nonetheless, it makes sense to describe the declarations
here, because they are straightforward variations on ordinary
inductive definitions.

First, Lean supports _mutually defined_ inductive types. The idea is
that we can define two (or more) inductive types at the same time,
where each one refers to the other(s).

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

In this example, two types are defined simultaneously: a natural
number {leanRef}`n` is {leanRef}`Even` if it is {lean}`0` or one more than an {leanRef}`Odd`
number, and {leanRef}`Odd` if it is one more than an {leanRef}`Even` number.
In the exercises below, you are asked to spell out the details.

:::leanFirst
A mutual inductive definition can also be used to define the notation
of a finite tree with nodes labelled by elements of {leanRef (in:="Tree (α")}`α`:

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```
:::

With this definition, one can construct an element of {leanRef}`Tree α` by
giving an element of {leanRef}`α` together with a list of subtrees, possibly
empty. The list of subtrees is represented by the type {leanRef}`TreeList α`,
which is defined to be either the empty list, {leanRef}`nil`, or the
{leanRef}`cons` of a tree and an element of {leanRef}`TreeList α`.

:::leanFirst
This definition is inconvenient to work with, however. It would be
much nicer if the list of subtrees were given by the type
{leanRef}`List (Tree α)`, especially since Lean's library contains a number of functions
and theorems for working with lists. One can show that the type
{leanRef}`TreeList α` is _isomorphic_ to {leanRef}`List (Tree α)`, but translating
results back and forth along this isomorphism is tedious.

In fact, Lean allows us to define the inductive type we really want:

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```
:::

This is known as a _nested_ inductive type. It falls outside the
strict specification of an inductive type given in the last section
because {leanRef}`Tree` does not occur strictly positively among the
arguments to {leanRef}`mk`, but, rather, nested inside the {leanRef}`List` type
constructor. Lean then automatically builds the
isomorphism between {leanRef}`TreeList α` and {leanRef}`List (Tree α)` in its kernel,
and defines the constructors for {leanRef}`Tree` in terms of the isomorphism.

# Exercises

```setup
open Nat
variable {n m : Nat}
def length : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1
def reverse : List α → List α := go []
where
  go (acc : List α) : List α → List α
    | [] => acc
    | x :: xs => go (x :: acc) xs
variable {xs ys : List α}

inductive Term where
  | const (n : Nat)
  | var (n : Nat)
  | plus (s t : Term)
  | times (s t : Term)
open Term
variable {s t : Term}

```

1. Try defining other operations on the natural numbers, such as
   multiplication, the predecessor function (with {lean}`pred 0 = 0`),
   truncated subtraction (with {lean}`n - m = 0` when {lean}`m` is greater
   than or equal to {lean}`n`), and exponentiation. Then try proving some
   of their basic properties, building on the theorems we have already
   proved.

   Since many of these are already defined in Lean's core library, you
   should work within a namespace named {lit}`Hidden`, or something like
   that, in order to avoid name clashes.

2. Define some operations on lists, like a {lean}`length` function or the
   {lean}`reverse` function. Prove some properties, such as the following:

   a. {lean}`length (xs ++ ys) = length xs + length ys`

   b. {lean}`length (reverse xs) = length xs`

   c. {lean}`reverse (reverse xs) = xs`

3. Define an inductive data type consisting of terms built up from the following constructors:

   - {lean}`const n`, a constant denoting the natural number {lean}`n`
   - {lean}`var n`, a variable, numbered {lean}`n`
   - {lean}`plus s t`, denoting the sum of {leanRef}`s` and {leanRef}`t`
   - {lean}`times s t`, denoting the product of {leanRef}`s` and {leanRef}`t`

   Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

4. Similarly, define the type of propositional formulas, as well as
   functions on the type of such formulas: an evaluation function,
   functions that measure the complexity of a formula, and a function
   that substitutes another formula for a given variable.
