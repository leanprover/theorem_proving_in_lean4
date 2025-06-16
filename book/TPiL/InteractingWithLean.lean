import VersoManual
import TPiL.Examples

open Verso.Genre Manual
open TPiL

#doc (Manual) "Interacting with Lean" =>

You are now familiar with the fundamentals of dependent type theory,
both as a language for defining mathematical objects and a language
for constructing proofs. The one thing you are missing is a mechanism
for defining new data types. We will fill this gap in the next
chapter, which introduces the notion of an _inductive data type_. But
first, in this chapter, we take a break from the mechanics of type
theory to explore some pragmatic aspects of interacting with Lean.

Not all of the information found here will be useful to you right
away. We recommend skimming this section to get a sense of Lean's
features, and then returning to it as necessary.

# Messages

Lean produces three kinds of messages:

: Errors

  Errors are produced when an inconsistency in the code means that it can't
  be processed. Examples include syntax errors (e.g. a missing {lit}`)`) and type
  errors such as attempting to add a natural number to a function.

: Warnings

  Warnings describe potential problems with the code, such as the presence of {lean}`sorry`.
  Unlike with errors, the code is not meaningless; however, warnings deserve careful attention.

: Information

  Information doesn't indicate any problem with the code, and includes output from commands such as {kw}`#check` and {kw}`#eval`.

Lean can check that a command produces the expected messages. If the messages match,
then any errors are disregarded; this can be used to ensure that the right errors occur.
If they don't, an error is produced. You can use the {kw}`#guard_msgs` command to indicate
which messages are expected.

Here is an example:
````lean
/--
error: type mismatch
  "Not a number"
has type
  String : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
def x : Nat := "Not a number"
````

:::leanFirst
Including a message category in parentheses after {leanRef}`#guard_msgs` causes it to check only
the specified category, letting others through. In this example, {leanRef}`#eval` issues an error
due to the presence of {lean}`sorry`, but the warning that is always issued for {lean}`sorry` is displayed
as usual:
````lean
/--
error: aborting evaluation since the expression depends on the
'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
-/
#guard_msgs(error) in
#eval (sorry : Nat)
````
:::

Without the configuration, both messages are captured:
````lean
/--
error: aborting evaluation since the expression depends on the
'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval (sorry : Nat)
````

Some examples in this book use {leanRef}`#guard_msgs` to indicate expected errors.

# Importing Files

The goal of Lean's front end is to interpret user input, construct
formal expressions, and check that they are well-formed and type-correct.
Lean also supports the use of various editors, which provide
continuous checking and feedback. More information can be found on the
Lean [documentation pages](https://lean-lang.org/documentation/).

The definitions and theorems in Lean's standard library are spread
across multiple files. Users may also wish to make use of additional
libraries, or develop their own projects across multiple files. When
Lean starts, it automatically imports the contents of the library
{lit}`Init` folder, which includes a number of fundamental definitions
and constructions. As a result, most of the examples we present here
work “out of the box.”

If you want to use additional files, however, they need to be imported
manually, via an {kw}`import` statement at the beginning of a file. The
command

> {kw}`import`{lit}` Bar.Baz.Blah`


imports the file {lit}`Bar/Baz/Blah.olean`, where the descriptions are
interpreted relative to the Lean _search path_. Information as to how
the search path is determined can be found on the
[documentation pages](https://lean-lang.org/documentation/).
By default, it includes the standard library directory, and (in some contexts)
the root of the user's local project.

Importing is transitive. In other words, if you import {lit}`Foo` and {lit}`Foo` imports {lit}`Bar`,
then you also have access to the contents of {lit}`Bar`, and do not need to import it explicitly.

# More on Sections

Lean provides various sectioning mechanisms to help structure a
theory. You saw in {ref "variables-and-sections"}[Variables and Sections] that the
{kw}`section` command makes it possible not only to group together
elements of a theory that go together, but also to declare variables
that are inserted as arguments to theorems and definitions, as
necessary. Remember that the point of the {kw}`variable` command is to
declare variables for use in theorems, as in the following example:

```lean
section
variable (x y : Nat)

def double := x + x

#check double y

#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y

#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

The definition of {leanRef}`double` does not have to declare {leanRef}`x` as an
argument; Lean detects the dependence and inserts it
automatically. Similarly, Lean detects the occurrence of {leanRef}`x` in
{leanRef}`t1` and {leanRef}`t2`, and inserts it automatically there, too.
Note that {leanRef}`double` does _not_ have {leanRef}`y` as argument. Variables are only
included in declarations where they are actually used.

# More on Namespaces

In Lean, identifiers are given by hierarchical _names_ like
{lit}`Foo.Bar.baz`. We saw in {ref "namespaces"}[Namespaces] that Lean provides
mechanisms for working with hierarchical names. The command
{kw}`namespace`{lit}` Foo` causes {lit}`Foo` to be prepended to the name of each
definition and theorem until {kw}`end`{lit}` Foo` is encountered. The command
{kw}`open`{lit}` Foo` then creates temporary _aliases_ to definitions and
theorems that begin with prefix {lit}`Foo`.

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar

#check Foo.bar
```

The following definition

```lean
def Foo.bar : Nat := 1
```

is treated as a macro, and expands to

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

Although the names of theorems and definitions have to be unique, the
aliases that identify them do not. When we open a namespace, an
identifier may be ambiguous. Lean tries to use type information to
disambiguate the meaning in context, but you can always disambiguate
by giving the full name. To that end, the string {lit}`_root_` is an
explicit description of the empty prefix.

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String

-- This reference is ambiguous:
-- #check add

#check String.add           -- String.add (a b : String) : String

#check Bool.add             -- Bool.add (a b : Bool) : Bool

#check _root_.add           -- add (α β : Type) : Type

#check add "hello" "world"  -- "hello".add "world" : String

#check add true false       -- true.add false : Bool

#check add Nat Nat          -- _root_.add Nat Nat : Type
```

We can prevent the shorter alias from being created by using the {kw}`protected` keyword:

```lean
protected def Foo.bar : Nat := 1

open Foo

/-- error: unknown identifier 'bar' -/
#guard_msgs in
#check bar -- error

#check Foo.bar
```

This is often used for names like {name}`Nat.rec` and {name}`Nat.recOn`, to prevent
overloading of common names.

The {leanRef}`open` command admits variations. The command

```lean
open Nat (succ zero gcd)

#check zero     -- Nat.zero : Nat

#eval gcd 15 6  -- 3
```

creates aliases for only the identifiers listed. The command

```lean
open Nat hiding succ gcd

#check zero     -- Nat.zero : Nat

/-- error: unknown identifier 'gcd' -/
#guard_msgs in
#eval gcd 15 6  -- error

#eval Nat.gcd 15 6  -- 3
```

creates aliases for everything in the {lit}`Nat` namespace _except_ the identifiers listed.

```lean
open Nat renaming mul → times, add → plus

#eval plus (times 2 2) 3  -- 7
```

creates aliases renaming {lean}`Nat.mul` to {leanRef}`times` and {lean}`Nat.add` to {leanRef}`plus`.

It is sometimes useful to {kw}`export` aliases from one namespace to another, or to the top level. The command

```lean
export Nat (succ add sub)
```

creates aliases for {leanRef}`succ`, {leanRef}`add`, and {leanRef}`sub` in the current
namespace, so that whenever the namespace is open, these aliases are
available. If this command is used outside a namespace, the aliases
are exported to the top level.

# Attributes
%%%
tag := "attributes"
%%%

The main function of Lean is to translate user input to formal
expressions that are checked by the kernel for correctness and then
stored in the environment for later use. But some commands have other
effects on the environment, either assigning attributes to objects in
the environment, defining notation, or declaring instances of type
classes, as described in {ref "type-classes"}[Chapter Type Classes]. Most of
these commands have global effects, which is to say, they remain
in effect not only in the current file, but also in any file that
imports it. However, such commands often support the {kw}`local` modifier,
which indicates that they only have effect until
the current {kw}`section` or {leanRef}`namespace` is closed, or until the end
of the current file.

In {ref "using-the-simplifier"}[Section Using the Simplifier],
we saw that theorems can be annotated with the {attr}`[simp]` attribute,
which makes them available for use by the simplifier.
The following example defines the prefix relation on lists,
proves that this relation is reflexive, and assigns the {attr}`[simp]` attribute to that theorem.

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

The simplifier then proves {leanRef}`isPrefix [1, 2, 3] [1, 2, 3]` by rewriting it to {lean}`True`.

One can also assign the attribute any time after the definition takes place:

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

In all these cases, the attribute remains in effect in any file that
imports the one in which the declaration occurs. Adding the {kw}`local`
modifier restricts the scope:

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

/-- error: simp made no progress -/
#guard_msgs in
example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

:::leanFirst
For another example, we can use the {kw}`instance` command to assign the
notation {lit}`≤` to the {leanRef}`isPrefix` relation. That command, which will
be explained in {ref "type-classes"}[Chapter Type Classes], works by
assigning an {attr}`[instance]` attribute to the associated definition.

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

:::

That assignment can also be made local:

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
------
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

/--
error: failed to synthesize
  LE (List α)

Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs in
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

In {ref "notation"}[Section Notation] below, we will discuss Lean's
mechanisms for defining notation, and see that they also support the
{kw}`local` modifier. However, in {ref "setting-options"}[Section Setting Options], we will
discuss Lean's mechanisms for setting options, which does _not_ follow
this pattern: options can _only_ be set locally, which is to say,
their scope is always restricted to the current section or current
file.

# More on Implicit Arguments

:::setup

````
variable (α : Type u) (β : α → Type v) (t : {x : α} → β x)
````


In {ref "implicit-arguments"}[Section Implicit Arguments],
we saw that if Lean displays the type
of a term {lean}`t` as {lean}`{x : α} → β x`, then the curly brackets
indicate that {leanRef}`x` has been marked as an _implicit argument_ to
{lean}`t`. This means that whenever you write {lean}`t`, a placeholder, or
“hole,” is inserted, so that {lean}`t` is replaced by {lean}`@t _`. If you
don't want that to happen, you have to write {lean}`@t` instead.
:::


:::setup
````
def f (x : Nat) {y : Nat} (z : Nat) : Nat := x + y + z
-- Equivalent:
example := f 7
example := @f 7 _
````

Notice that implicit arguments are inserted eagerly. Suppose we define
a function {lean}`f : (x : Nat) → {y : Nat} → (z : Nat) → Nat`.
Then, when we write the expression {lean}`f 7` without further
arguments, it is parsed as {lean}`@f 7 _`.
:::

:::setup
````
def f (x : Nat) {{y : Nat}} (z : Nat) : Nat := x + y + z
-- Just f 7
example := f 7
-- These are equivalent:
example := @f 7 _ 3
example := f 7 3
-- Alternative syntax:
def f' (x : Nat) ⦃y : Nat⦄ (z : Nat) : Nat := x + y + z
````

Lean offers a weaker annotation which specifies that a placeholder should only be added
_before_ a subsequent explicit argument. It can be written with double braces, so the type of {lean}`f` would be
{lean}`f : (x : Nat) → {{y : Nat}} → (z : Nat) → Nat`.
With this annotation, the expression {lean}`f 7` would be parsed as is, whereas {lean}`f 7 3` would be
parsed as {lean}`@f 7 _ 3`, just as it would be with the strong annotation.
This annotation can also be written as {lit}`⦃y : Nat⦄`, where the Unicode brackets are entered
as {kbd}`\{{` and {kbd}`\}}`, respectively.
:::


To illustrate the difference, consider the following example, which
shows that a reflexive euclidean relation is both symmetric and
transitive.

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr
```

The results are broken down into small steps: {leanRef}`th1` shows that a
relation that is reflexive and euclidean is symmetric, and {leanRef}`th2`
shows that a relation that is symmetric and euclidean is
transitive. Then {leanRef}`th3` combines the two results. But notice that we
have to manually disable the implicit arguments in {leanRef}`euclr`, because
otherwise too many implicit arguments are inserted. The problem goes
away if we use weak implicit arguments:

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr  -- euclr : Euclidean r
```

There is a third kind of implicit argument that is denoted with square
brackets, {lit}`[` and {lit}`]`. These are used for type classes, as
explained in {ref "type-classes"}[Chapter Type Classes].

# Notation
%%%
tag := "notation"
%%%

Identifiers in Lean can include any alphanumeric characters, including
Greek characters (other than ∀ , Σ , and λ , which, as we have seen,
have a special meaning in the dependent type theory). They can also
include subscripts, which can be entered by typing {kbd}`\_` followed by
the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

Lean's syntax can be extended and customized by users at every level,
ranging from basic “mixfix” notations to custom elaborators.  In fact,
all builtin syntax is parsed and processed using the same mechanisms
and APIs open to users.  In this section, we will describe and explain
the various extension points.

While introducing new notations is a relatively rare feature in
programming languages and sometimes even frowned upon because of its
potential to obscure code, it is an invaluable tool in formalization
for expressing established conventions and notations of the respective
field succinctly in code.  Going beyond basic notations, Lean's
ability to factor out common boilerplate code into (well-behaved)
macros and to embed entire custom domain specific languages (DSLs) to
textually encode subproblems efficiently and readably can be of great
benefit to both programmers and proof engineers alike.

## Notations and Precedence

The most basic syntax extension commands allow introducing new (or
overloading existing) prefix, infix, and postfix operators.

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => Inv.inv
```

After the initial command name describing the operator kind (its
“{deftech}[fixity]”), we give the _parsing precedence_ of the operator preceded
by a colon {lit}`:`, then a new or existing token surrounded by double
quotes (the whitespace is used for pretty printing), then the function
this operator should be translated to after the arrow {lit}`=>`.

The precedence is a natural number describing how “tightly” an
operator binds to its arguments, encoding the order of operations.  We
can make this more precise by looking at the commands the above unfold to:

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
 -- `max` is a shorthand for precedence 1024:
notation:1024 arg:1024 "⁻¹" => Inv.inv arg
```

:::setup
```
variable {p : Nat} {a b c : α} [Add α] [Pow α α]
```
It turns out that all commands from the first code block are in fact
command _macros_ translating to the more general {leanRef}`notation` command.
We will learn about writing such macros below.  Instead of a single
token, the {leanRef}`notation` command accepts a mixed sequence of tokens and
named term placeholders with precedences, which can be referenced on
the right-hand side of {lit}`=>` and will be replaced by the respective
term parsed at that position. A placeholder with precedence {lean}`p`
accepts only notations with precedence at least {lean}`p` in that place.
Thus the string {lean}`a + b + c` cannot be parsed as the equivalent of
{lean}`a + (b + c)` because the right-hand side operand of an {leanRef}`infixl` notation
has precedence one greater than the notation itself.  In contrast,
{leanRef}`infixr` reuses the notation's precedence for the right-hand side
operand, so {lean}`a ^ b ^ c` _can_ be parsed as {lean}`a ^ (b ^ c)`.  Note that
if we used {leanRef}`notation` directly to introduce an infix notation like
:::

```lean
def wobble : α → β → γ := sorry
------
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

:::setup
```
variable (a : α) (b : β) (c : γ)
def wobble : α → β → γ := sorry
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs

```

where the precedences do not sufficiently determine associativity,
Lean's parser will default to right associativity.  More precisely,
Lean's parser follows a local _longest parse_ rule in the presence of
ambiguous grammars: when parsing the right-hand side of {lit}`a ~` in
{lean}`a ~ b ~ c`, it will continue parsing as long as possible (as the current
precedence allows), not stopping after {leanRef}`b` but parsing {leanRef}`~ c` as well.
Thus the term is equivalent to {lean}`a ~ (b ~ c)`.
:::

As mentioned above, the {leanRef}`notation` command allows us to define
arbitrary _mixfix_ syntax freely mixing tokens and placeholders.

```lean
set_option quotPrecheck false
------
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

Placeholders without precedence default to {lit}`0`, i.e. they accept notations of any precedence in their place.
If two notations overlap, we again apply the longest parse rule:

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

The new notation is preferred to the binary notation since the latter,
before chaining, would stop parsing after {leanRef}`1 + 2`.  If there are
multiple notations accepting the same longest parse, the choice will
be delayed until elaboration, which will fail unless exactly one
overload is type-correct.

# Coercions

In Lean, the type of natural numbers, {lean}`Nat`, is different from the
type of integers, {lean}`Int`. But there is a function {lean}`Int.ofNat` that
embeds the natural numbers in the integers, meaning that we can view
any natural number as an integer, when needed. Lean has mechanisms to
detect and insert _coercions_ of this sort. Coercions can be explicitly
requested using the overloaded {lit}`↑` operator.

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + ↑m : Int

#check i + m + j  -- i + ↑m + j : Int

#check i + m + n  -- i + ↑m + ↑n : Int
```

# Displaying Information

There are a number of ways in which you can query Lean for information
about its current state and the objects and theorems that are
available in the current context. You have already seen two of the
most common ones, {kw}`#check` and {kw}`#eval`. Remember that {kw}`#check`
is often used in conjunction with the {lit}`@` operator, which makes all
of the arguments to a theorem or definition explicit. In addition, you
can use the {kw}`#print` command to get information about any
identifier. If the identifier denotes a definition or theorem, Lean
prints the type of the symbol, and its definition. If it is a constant
or an axiom, Lean indicates that fact, and shows the type.

```lean
-- examples with equality
#check Eq

#check @Eq

#check Eq.symm

#check @Eq.symm

#print Eq.symm

-- examples with And
#check And

#check And.intro

#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo

#check @foo

#print foo
```

# Setting Options
%%%
tag := "setting-options"
%%%

Lean maintains a number of internal variables that can be set by users
to control its behavior. The syntax for doing so is as follows:


{kw}`set_option`{lit}` <name> <value>`


One very useful family of options controls the way Lean's _pretty printer_ displays terms. The following options take an input of true or false:

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

As an example, the following settings yield much longer output:

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4

#reduce (fun x => x + 2) = (fun x => x + 3)

#check (fun x => x + 1) 1
```

The command {leanCommand}`set_option pp.all true` carries out these settings all
at once, whereas {leanCommand}`set_option pp.all false` reverts to the previous
values. Pretty printing additional information is often very useful
when you are debugging a proof, or trying to understand a cryptic
error message. Too much information can be overwhelming, though, and
Lean's defaults are generally sufficient for ordinary interactions.

:::comment
```````
<!--
# Elaboration Hints

When you ask Lean to process an expression like `λ x y z, f (x + y) z`, you are leaving information implicit. For example, the types of `x`, `y`, and `z` have to be inferred from the context, the notation `+` may be overloaded, and there may be implicit arguments to `f` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as _type class resolution_. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function `f` has type `Π {α : Type*}, α → α → α` and Lean is trying to parse the expression `f n`, where `n` can be inferred to have type `nat`. Then it is clear that the implicit argument `α` has to be `nat`. However, some inference problems are _higher order_. For example, the substitution operation for equality, `eq.subst`, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

Now suppose we are given `a b : ℕ` and `h₁ : a = b` and `h₂ : a * b > a`. Then, in the expression `eq.subst h₁ h₂`, `P` could be any of the following:

-  `λ x, x * b > x`
-  `λ x, x * b > a`
-  `λ x, a * b > x`
-  `λ x, a * b > a`

In other words, our intent may be to replace either the first or second `a` in `h₂`, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute `[reducible]`, `[semireducible]`, or `[irreducible]`. Definitions are marked `[semireducible]` by default. A definition with the `[reducible]` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the `[irreducible]` attribute. Theorems are marked `[irreducible]` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the `local` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked `[elab_with_expected_type]`, `[elab_simple]`. or `[elab_as_eliminator]`. When applied to a definition `f`, these bear on elaboration of an expression `f a b c ...` in which `f` is applied to arguments. With the default attribute, `[elab_with_expected_type]`, the arguments `a`, `b`, `c`, ... are elaborating using information about their expected type, inferred from `f` and the previous arguments. In contrast, with `[elab_simple]`, the arguments are elaborated from left to right without propagating information about their types. The last attribute, `[elab_as_eliminator]`, is commonly used for eliminators like recursors, induction principles, and `eq.subst`. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the `local` modifier to limit their scope. Moreover, using the `@` symbol in front of an identifier in an expression instructs the elaborator to use the `[elab_simple]` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, `@@`, which leaves parameters before the first higher-order parameter implicit. For example, `@@eq.subst` leaves the type of the equation implicit, but makes the context of the substitution explicit.

-->
```````
:::

# Using the Library

To use Lean effectively you will inevitably need to make use of
definitions and theorems in the library. Recall that the {kw}`import`
command at the beginning of a file imports previously compiled results
from other files, and that importing is transitive; if you import
{lit}`Foo` and {lit}`Foo` imports {lit}`Bar`, then the definitions and theorems
from {lit}`Bar` are available to you as well. But the act of opening a
namespace, which provides shorter names, does not carry over. In each
file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library
and its contents, so you know what theorems, definitions, notations,
and resources are available to you. Below we will see that Lean's
editor modes can also help you find things you need, but studying the
contents of the library directly is often unavoidable. Lean's standard
library can be found online, on GitHub:

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)


You can see the contents of these directories and files using GitHub's
browser interface. If you have installed Lean on your own computer,
you can find the library in the {lit}`lean` folder, and explore it with
your file manager. Comment headers at the top of each file provide
additional information.

Lean's library developers follow general naming guidelines to make it
easier to guess the name of a theorem you need, or to find it using
tab completion in editors with a Lean mode that supports this, which
is discussed in the next section. Identifiers are generally
{lit}`camelCase`, and types are {lit}`CamelCase`. For theorem names,
we rely on descriptive names where the different components are separated
by {lit}`_`s. Often the name of theorem simply describes the conclusion:

```lean
#check Nat.succ_ne_zero

#check Nat.zero_add

#check Nat.mul_one

#check Nat.le_of_succ_le_succ
```

:::setup
````
open Nat
````

Remember that identifiers in Lean can be organized into hierarchical
namespaces. For example, the theorem named {lean}`le_of_succ_le_succ` in the
namespace {lit}`Nat` has full name {lean}`Nat.le_of_succ_le_succ`, but the shorter
name is made available by the command {kw}`open`{lit}` Nat` (for names not marked as
{kw}`protected`). We will see in {ref "inductive-types"}[Chapter Inductive Types]
and {ref "structures-and-records"}[Chapter Structures and Records]
that defining structures and inductive data types in Lean generates
associated operations, and these are stored in
a namespace with the same name as the type under definition. For
example, the product type comes with the following operations:
:::

```lean
#check @Prod.mk

#check @Prod.fst

#check @Prod.snd

#check @Prod.rec
```

The first is used to construct a pair, whereas the next two,
{leanRef}`Prod.fst` and {leanRef}`Prod.snd`, project the two elements. The last,
{leanRef}`Prod.rec`, provides another mechanism for defining functions on a
product in terms of a function on the two components. Names like
{leanRef}`Prod.rec` are _protected_, which means that one has to use the full
name even when the {lit}`Prod` namespace is open.

With the propositions as types correspondence, logical connectives are
also instances of inductive types, and so we tend to use dot notation
for them as well:

```lean
#check @And.intro

#check @And.casesOn

#check @And.left

#check @And.right

#check @Or.inl

#check @Or.inr

#check @Or.elim

#check @Exists.intro

#check @Exists.elim

#check @Eq.refl

#check @Eq.subst
```

# Auto Bound Implicit Arguments

:::leanFirst
In the previous section, we have shown how implicit arguments make functions more convenient to use.
However, functions such as {leanRef}`compose` are still quite verbose to define. Note that the universe
polymorphic {leanRef}`compose` is even more verbose than the one previously defined.

```lean
universe u v w

def compose {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

:::leanFirst
You can avoid the {kw}`universe` command by providing the universe parameters when defining {leanRef}`compose`.

```lean
def compose.{u, v, w}
    {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

::::leanFirst
Lean 4 supports a new feature called _auto bound implicit arguments_. It makes functions such as
{leanRef}`compose` much more convenient to write. When Lean processes the header of a declaration,
any unbound identifier is automatically added as an implicit argument. With this feature we can write {leanRef}`compose` as

:::TODO

Update and check details

:::

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose -- @compose : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

Note that Lean inferred a more general type using {lean}`Sort` instead of {leanRef}`Type`.
::::

Although we love this feature and use it extensively when implementing Lean,
we realize some users may feel uncomfortable with it. Thus, you can disable it using
the command {leanCommand}`set_option autoImplicit false`.

```lean
set_option autoImplicit false

/--
error: unknown identifier 'β'
---
error: unknown identifier 'γ'
---
error: unknown identifier 'α'
---
error: unknown identifier 'β'
---
error: unknown identifier 'α'
---
error: unknown identifier 'γ'
-/
#guard_msgs in
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

# Implicit Lambdas

:::TODO
Update this text after archaeology
:::

:::leanFirst
When the expected type of an expression is a function that is awaiting implicit
arguments, the elaborator automatically introduces the corresponding lambdas.
For example, {leanRef}`pure`'s type states that the first argument is an implicit type
{leanRef}`α`, but {leanRef}`ReaderT.pure`'s first agument is the reader monad's context type {leanRef}`ρ`.
It is automatically surrounded with a {kw}`fun`{lit}` {α} => ...`, which allows the elaborator to
correctly fill in the implicit arguments in the body.

```lean
variable (ρ : Type) (m : Type → Type) [Monad m]
------
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```
:::

Users can disable the implicit lambda feature by using {lit}`@` or writing
a lambda expression with {lit}`{}` or {lit}`[]` binder annotations.  Here are
few examples

```lean
set_option linter.unusedVariables false
namespace Ex2
------
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before {kw}`fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
------
end Ex2
```

# Sugar for Simple Functions

Lean includes a notation for describing simple functions using anonymous
placeholders rather than {kw}`fun`. When {lit}`·` occurs as part of a term,
the nearest enclosing parentheses become a function with the {lit}`·` as its argument.
If the parentheses include multiple placeholders without other intervening parentheses,
then they are made into arguments from left to right. Here are a few examples:

```lean
namespace Ex3
------
#check (· + 1) -- fun x => x + 1 : Nat → Nat

#check (2 - ·) -- fun x => 2 - x : Nat → Nat

#eval [1, 2, 3, 4, 5].foldl (· * ·) 1 -- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·) -- fun x1 x2 => f x1 1 x2 : Nat → Nat → Nat

#eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- [1, 3, 5]
------
end Ex3
```

Nested parentheses introduce new functions. In the following example, two different lambda expressions are created:

```lean
#check (Prod.mk · (· + 1)) -- fun x => (x, fun x => x + 1) : ?m.2 → ?m.2 × (Nat → Nat)
```

# Named Arguments

Named arguments enable you to specify an argument for a parameter by
matching the argument with its name rather than with its position in
the parameter list.  If you don't remember the order of the parameters
but know their names, you can send the arguments in any order. You may
also provide the value for an implicit parameter when Lean failed to
infer it. Named arguments also improve the readability of your code by
identifying what each argument represents.

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop}
    (h₁ : p a b b) (h₂ : b = a) :
    p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

In the following examples, we illustrate the interaction between named
and default arguments.

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

You can use {lit}`..` to provide missing explicit arguments as {lit}`_`.
This feature combined with named arguments is useful for writing patterns. Here is an example:

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

Ellipses are also useful when explicit arguments can be automatically
inferred by Lean, and we want to avoid a sequence of {lit}`_`s.

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
