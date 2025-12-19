import VersoManual
import TPiL.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiL

#doc (Manual) "Type Classes" =>
%%%
tag := "type-classes"
%%%

Type classes were introduced as a principled way of enabling
ad-hoc polymorphism in functional programming languages. We first observe that it
would be easy to implement an ad-hoc polymorphic function (such as addition) if the
function simply took the type-specific implementation of addition as an argument
and then called that implementation on the remaining arguments. For example,
suppose we declare a structure in Lean to hold implementations of addition.

```lean
namespace Ex
------
structure Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → Add α → α → α → α
------
end Ex
```


::::setup
```
namespace Ex
structure Add (α : Type) where
  add : α → α → α
def double (s : Add α) (x : α) : α :=
  s.add x x
variable {n : Nat}
```
:::leanFirst
In the above Lean code, the field {leanRef}`add` has type
{lean}`Add.add : {α : Type} → Add α → α → α → α`
where the curly braces around the type {leanRef}`α` mean that it is an implicit argument.
We could implement {leanRef}`double` by:


```lean
namespace Ex
structure Add (α : Type) where
  add : α → α → α
------
def double (s : Add α) (x : α) : α :=
  s.add x x

#eval double { add := Nat.add } 10 -- 20

#eval double { add := Nat.mul } 10 -- 100

#eval double { add := Int.add } 10 -- 20
------
end Ex
```
:::

Note that you can double a natural number {lean}`n` by {lean}`double { add := Nat.add } n`.
Of course, it would be highly cumbersome for users to manually pass the
implementations around in this way.
Indeed, it would defeat most of the potential benefits of ad-hoc
polymorphism.
::::

:::leanFirst
The main idea behind type classes is to make arguments such as {leanRef}`Add α` implicit,
and to use a database of user-defined instances to synthesize the desired instances
automatically through a process known as typeclass resolution. In Lean, by changing
{kw}`structure` to {kw}`class` in the example above, the type of {leanRef}`Add.add` becomes:

```lean
namespace Ex
------
class Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → [self : Add α] → α → α → α
------
end Ex
```
:::

where the square brackets indicate that the argument of type {leanRef}`Add α` is _instance implicit_,
i.e. that it should be synthesized using typeclass resolution. This version of
{leanRef}`add` is the Lean analogue of the Haskell term {lit}`add :: Add a => a -> a -> a`.
Similarly, we can register instances by:

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
------
end Ex
```

::::leanFirst
:::setup
```
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

variable (n m : Nat)
```
Then for {lean}`n : Nat` and {lean}`m : Nat`, the term {lean}`Add.add n m` triggers typeclass resolution with
the goal of {lean}`Add Nat`, and typeclass resolution will synthesize the instance for {lean}`Nat` above.
We can now reimplement {leanRef}`double` using an instance implicit by:
:::

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
instance : Add Nat where
 add := Nat.add
instance : Add Int where
 add := Int.add
instance : Add Float where
 add := Float.add
------
def double [Add α] (x : α) : α :=
  Add.add x x

#check @double -- @double : {α : Type} → [Add α] → α → α

#eval double 10 -- 20

#eval double (10 : Int) -- 20

#eval double (7 : Float) -- 14.000000

#eval double (239.0 + 2) -- 482.000000

------
end Ex
```
::::

:::leanFirst
In general, instances may depend on other instances in complicated ways. For example,
you can declare an instance stating that if {leanRef}`α` has addition, then {leanRef}`Array α`
has addition:

```lean
instance [Add α] : Add (Array α) where
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4] -- #[4, 6]

#eval #[1, 2] + #[3, 4] -- #[4, 6]
```
:::

Note that {leanRef}`(· + ·)` is notation for {lean}`fun x y => x + y` in Lean.


:::setup
```
def head [Inhabited α] (xs : List α) : α := default
variable {α : Type u} {x : α} {xs : List α} [Inhabited α]
```

The example above demonstrates how type classes are used to overload notation.
Now, we explore another application. We often need an arbitrary element of a given type.
Recall that types may not have any elements in Lean.
It often happens that we would like a definition to return an arbitrary element in a “corner case.”
For example, we may like the expression {lean}`head xs` to be of type {lean}`α` when {lean}`xs` is of type {lean}`List α`.
Similarly, many theorems hold under the additional assumption that a type is not empty.
For example, if {lean}`α` is a type, {lean}`∃ x : α, x = x` is true only if {lean}`α` is not empty.
The standard library defines a type class {lean}`Inhabited` to enable type class inference to infer a
“default” element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:



```lean
namespace Ex
------
class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default -- @Inhabited.default : {α : Type u_1} → [self : Inhabited α] → α
------
end Ex
```

Note {leanRef}`Inhabited.default` doesn't have any explicit arguments.

An element of the class {lean}`Inhabited α` is simply an expression of the form {lean}`Inhabited.mk x`, for some element {lean}`x : α`.
The projection {lean}`Inhabited.default` will allow us to “extract” such an element of {lean}`α` from an element of {lean}`Inhabited α`.
Now we populate the class with some instances:
:::

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
------
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat) -- 0

#eval (Inhabited.default : Bool) -- true
--------
end Ex
```

You can use the command {kw}`export` to create the alias {lean}`default` for {lean}`Inhabited.default`.

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
instance : Inhabited Unit where
 default := ()
instance : Inhabited Prop where
 default := True
------
export Inhabited (default)

#eval (default : Nat) -- 0

#eval (default : Bool) -- true
------
end Ex
```

# Chaining Instances
%%%
tag := "chaining-instances"
%%%

If that were the extent of type class inference, it would not be all that impressive;
it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
What makes type class inference powerful is that one can _chain_ instances. That is,
an instance declaration can in turn depend on an implicit instance of a type class.
This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

:::leanFirst
For example, the following definition shows that if two types {leanRef}`α` and {leanRef}`β` are inhabited, then so is their product:

```lean
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)
```
:::

With this added to the earlier instance declarations, type class instance can infer, for example, a default element of {lean}`Nat × Bool`:

```lean
namespace Ex
class Inhabited (α : Type u) where
 default : α
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
opaque default [Inhabited α] : α :=
 Inhabited.default
------
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool) -- (0, true)
------
end Ex
```

Similarly, we can inhabit type function with suitable constant functions:

```lean
instance [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default
```

As an exercise, try defining default instances for other types, such as {lean}`List` and {lean}`Sum` types.

:::setup
```
universe u
set_option checkBinderAnnotations false
```
The Lean standard library contains the definition {name}`inferInstance`. It has type {lean}`{α : Sort u} → [i : α] → α`,
and is useful for triggering the type class resolution procedure when the expected type is an instance.
:::

```lean
#check (inferInstance : Inhabited Nat) -- inferInstance : Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```

:::leanFirst
You can use the command {leanRef}`#print` to inspect how simple {leanRef}`inferInstance` is.

```lean
#print inferInstance
```
:::

# ToString
%%%
tag := "ToString"
%%%
```setup
universe u
```

:::leanFirst
The polymorphic method {leanRef}`toString` has type {lean}`{α : Type u} → [ToString α] → α → String`. You implement the instance
for your own types and use chaining to convert complex values into strings. Lean comes with {lean}`ToString` instances
for most builtin types.

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person } -- "Leo@542"

#eval toString ({ name := "Daniel", age := 18 : Person }, "hello") -- "(Daniel@18, hello)"
```
:::

# Numerals
%%%
tag := "numerals"
%%%

Numerals are polymorphic in Lean. You can use a numeral (e.g., {lit}`2`) to denote an element of any type that implements
the type class {name}`OfNat`.

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- 2 : Rational

#check (2 : Nat)      -- 2 : Nat
```

:::setup
```
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"
```
Lean elaborates the terms {lean}`(2 : Nat)` and {lean}`(2 : Rational)` as
{lean (type := "Nat")}`@OfNat.ofNat Nat 2 (@instOfNatNat 2)` and
{lean}`@OfNat.ofNat Rational 2 (@instOfNatRational 2)` respectively.
We say the numerals {lit}`2` occurring in the elaborated terms are _raw_ natural numbers.
You can input the raw natural number {lit}`2` using the macro {lean}`nat_lit 2`.
:::

```lean
#check nat_lit 2  -- 2 : Nat
```

Raw natural numbers are _not_ polymorphic.

The {lean}`OfNat` instance is parametric on the numeral. So, you can define instances for particular numerals.
The second argument is often a variable as in the example above, or a _raw_ natural number.

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

# Output Parameters
%%%
tag := "output-parameters"
%%%

:::setup
```
universe u
variable (T : Type u)
```

By default, Lean only tries to synthesize an instance {lean}`Inhabited T` when the term {lean}`T` is known and does not
contain missing parts. The following command produces the error
{lit}`typeclass instance problem is stuck, it is often due to metavariables` because the type has a missing part (i.e., the {lit}`_`).
:::

```lean
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2)
-/
#guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))
```

You can view the parameter of the type class {lean}`Inhabited` as an _input_ value for the type class synthesizer.
When a type class has multiple parameters, you can mark some of them as {deftech}_output parameters_.
Lean will start type class synthesizer even when these parameters have missing parts.
In the following example, we use output parameters to define a _heterogeneous_ polymorphic
multiplication.

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12

#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
------
end Ex
```

The parameters {leanRef}`α` and {leanRef}`β` are considered input parameters and {leanRef}`γ` an output one.
Given an application {leanRef}`hMul a b`, after the types of {leanRef}`a` and {leanRef}`b` are known, the type class
synthesizer is invoked, and the resulting type is obtained from the output parameter {leanRef}`γ`.
In the example above, we defined two instances. The first one is the homogeneous
multiplication for natural numbers. The second is the scalar multiplication for arrays.
Note that you chain instances and generalize the second instance.

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12

#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]

#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]

#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
------
end Ex
```

You can use our new scalar array multiplication instance on arrays of type {leanRef}`Array β`
with a scalar of type {leanRef}`α` whenever you have an instance {leanRef}`HMul α β γ`.
In the last {kw}`#eval`, note that the instance was used twice on an array of arrays.

Output parameters are ignored during instance synthesis. Even when instance synthesis occurs in a
context in which the values of output parameters are already determined, their values are ignored.
Once an instance is found using its input parameters, Lean ensures that the already-known values of
the output parameters match those which were found.

Lean also features {deftech}_semi-output parameters_, which have some features of input parameters
and some features of output parameters. Like input parameters, semi-output parameters are considered
when selecting instances. Like output parameters, they can be used to instantiate unknown values.
However, they do not do so uniquely. Instance synthesis with semi-output parameters can be more difficult
to predict, because the order in which instances are considered can determine which is selected, but it is
also more flexible.

# Default Instances
%%%
tag := "default-instances"
%%%

In the class {leanRef}`HMul`, the parameters {leanRef}`α` and {leanRef}`β` are treated as input values.
Thus, type class synthesis only starts after these two types are known. This may often
be too restrictive.

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

/--
error: typeclass instance problem is stuck
  HMul Int ?m.2 (?m.11 y)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `HMul` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
#eval fun y => xs.map (fun x => hMul x y)
------
end Ex
```

The instance {leanRef}`HMul` is not synthesized by Lean because the type of {leanRef}`y` has not been provided.
However, it is natural to assume that the type of {leanRef}`y` and {leanRef}`x` should be the same in
this kind of situation. We can achieve exactly that using _default instances_.

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- fun y => List.map (fun x => hMul x y) xs : Int → List Int
------
end Ex
```

:::setup
```
variable {α : Type u} {β : Type v} {γ : Type w} {a : α} {b : β} {n : Nat}
variable [HAdd α β γ] [HSub α β γ] [HMul α β γ] [HDiv α β γ] [HMod α β γ]
```
By tagging the instance above with the attribute {attr}`[default_instance]`, we are instructing Lean
to use this instance on pending type class synthesis problems.
The actual Lean implementation defines homogeneous and heterogeneous classes for arithmetical operators.
Moreover, {lean}`a + b`, {lean}`a * b`, {lean}`a - b`, {lean}`a / b`, and {lean}`a % b` are notations for the heterogeneous versions.
The instance {lean}`OfNat Nat n` is the default instance (with priority 100) for the {lean}`OfNat` class. This is why the numeral
{lean}`2` has type {lean}`Nat` when the expected type is not known. You can define default instances with higher
priority to override the builtin ones.
:::
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- 2 : Rational
```

:::setup
```
variable {α : Type u} {xs : List α} [Mul α] [OfNat α 2]
```

Priorities are also useful to control the interaction between different default instances.
For example, suppose {lean}`xs` has type {lean}`List α`. When elaborating {lean}`xs.map (fun x => 2 * x)`, we want the homogeneous instance for multiplication
to have higher priority than the default instance for {lean}`OfNat α 2`. This is particularly important when we have implemented only the instance
{lean}`HMul α α α`, and did not implement {lean}`HMul Nat α α`.
Now, we reveal how the notation {lit}`a * b` is defined in Lean.
:::
```lean
namespace Ex
------
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
------
end Ex
```

The {leanRef}`Mul` class is convenient for types that only implement the homogeneous multiplication.

# Local Instances
%%%
tag := "local-instances"
%%%

Type classes are implemented using attributes in Lean. Thus, you can
use the {kw}`local` modifier to indicate that they only have effect until
the current {kw}`section` or {kw}`namespace` is closed, or until the end
of the current file.

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

/--
error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p
```

You can also temporarily disable an instance using the {kw}`attribute` command
until the current {kw}`section` or {kw}`namespace` is closed, or until the end
of the current file.

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

/--
error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p  -- Error: failed to synthesize instance
```

We recommend you only use this command to diagnose problems.

# Scoped Instances
%%%
tag := "scoped-instances"
%%%

You can also declare scoped instances in namespaces. This kind of instance is
only active when you are inside of the namespace or open the namespace.

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

/--
error: failed to synthesize
  HAdd Point Point ?m.3

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs (error) in
#check fun (p : Point) => p + p + p

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

You can use the command {kw}`open scoped`{lit}` <namespace>` to activate scoped attributes but will
not “open” the names from the namespace.

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

/--
error: Unknown identifier `double`
-/
#guard_msgs (error) in
#check fun (p : Point) => double p
```

# Decidable Propositions
%%%
tag := "decidable-propositions"
%%%

Let us consider another example of a type class defined in the
standard library, namely the type class of {lean}`Decidable`
propositions. Roughly speaking, an element of {lean}`Prop` is said to be
decidable if we can decide whether it is true or false. The
distinction is only useful in constructive mathematics; classically,
every proposition is decidable. But if we use the classical principle,
say, to define a function by cases, that function will not be
computable. Algorithmically speaking, the {lean}`Decidable` type class can
be used to infer a procedure that effectively determines whether or
not the proposition is true. As a result, the type class supports such
computational definitions when they are possible while at the same
time allowing a smooth transition to the use of classical definitions
and classical reasoning.

In the standard library, {lean}`Decidable` is defined formally as follows:

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

:::setup
```
variable {p : Prop} (t : Decidable p) (t' : p ∨ ¬p) (a b : α)
```

Logically speaking, having an element {lean}`t : Decidable p` is stronger
than having an element {lean}`t' : p ∨ ¬p`; it enables us to define values
of an arbitrary type depending on the truth value of {lean}`p`. For
example, for the expression {lean}`if p then a else b` to make sense, we
need to know that {lean}`p` is decidable. That expression is syntactic
sugar for {lean}`ite p a b`, where {lean}`ite` is defined as follows:
:::
```lean
namespace Hidden
------
def ite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t e : α) : α :=
  h.casesOn (motive := fun _ => α) (fun _ => e) (fun _ => t)
------
end Hidden
```

:::leanFirst
The standard library also contains a variant of {leanRef}`ite` called
{leanRef}`dite`, the dependent if-then-else expression. It is defined as
follows:

```lean
namespace Hidden
------
def dite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
------
end Hidden
```
:::

:::setup
```
variable {c : Prop} [Decidable c] (t : c → α) (e : ¬c → α) (hc : c) (hnc : ¬c)
```
```lean (show := false)
example [Decidable c] (t e : α) : α := if h : c then t else e
```

That is, in {lean}`dite c t e`, we can assume {lean}`hc : c` in the “then”
branch, and {lean}`hnc : ¬c` in the “else” branch. To make {lean}`dite` more
convenient to use, Lean allows us to write {leanRef}`if h : c then t else e`
instead of {lean}`dite c (fun h : c => t h) (fun h : ¬c => e h)`.
:::

Without classical logic, we cannot prove that every proposition is
decidable. But we can prove that _certain_ propositions are
decidable. For example, we can prove the decidability of basic
operations like equality and comparisons on the natural numbers and
the integers. Moreover, decidability is preserved under propositional
connectives:

```lean
#check @instDecidableAnd -- @instDecidableAnd : {p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∧ q)

#check @instDecidableOr
#check @instDecidableNot
```

Thus we can carry out definitions by cases on decidable predicates on
the natural numbers:

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

Turning on implicit arguments shows that the elaborator has inferred
the decidability of the proposition {leanRef}`x < a ∨ x > b`, simply by
applying appropriate instances.

With the classical axioms, we can prove that every proposition is
decidable. You can import the classical axioms and make the generic
instance of decidability available by opening the {lit}`Classical` namespace.

```lean
open Classical
```

:::setup
```
open Classical
variable {p : Prop}
```
Thereafter {lean}`Decidable p` has an instance for every {leanRef}`p`.
Thus all theorems in the library
that rely on decidability assumptions are freely available when you
want to reason classically. In {ref "axioms-and-computation"}[Axioms and Computation],
we will see that using the law of the
excluded middle to define functions can prevent them from being used
computationally. Thus, the standard library assigns a low priority to
the {lean}`propDecidable` instance.
:::

```lean
namespace Hidden
------
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
------
end Hidden
```

This guarantees that Lean will favor other instances and fall back on
{leanRef}`propDecidable` only after other attempts to infer decidability have
failed.

The {lean}`Decidable` type class also provides a bit of small-scale
automation for proving theorems. The standard library introduces the
tactic {tactic}`decide` that uses the {lean}`Decidable` instance to solve simple goals,
as well as a function {name}`decide` that uses a {lean}`Decidable` instance to compute the
corresponding {lean}`Bool`.

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬(True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1 + 1 := by
  decide

#print ex

#check @of_decide_eq_true -- @of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p

#check @decide -- decide : (p : Prop) → [h : Decidable p] → Bool
```

:::setup
```
variable {p : Prop} [Decidable p]
```

They work as follows. The expression {lean}`decide p` tries to infer a
decision procedure for {leanRef}`p`, and, if it is successful, evaluates to
either {lean}`true` or {lean}`false`. In particular, if {leanRef}`p` is a true closed
expression, {leanRef}`decide p` will reduce definitionally to the Boolean {lean}`true`.
On the assumption that {lean}`decide p = true` holds, {lean}`of_decide_eq_true`
produces a proof of {lean}`p`. The tactic {tactic}`decide` puts it all together to
prove a target {lean}`p`. By the previous observations,
{tactic}`decide` will succeed any time the inferred decision procedure
 for {lean}`p` has enough information to evaluate, definitionally, to the {lean}`isTrue` case.
:::

# Managing Type Class Inference
%%%
tag := "managing-type-class-inference"
%%%

If you are ever in a situation where you need to supply an expression
that Lean can infer by type class inference, you can ask Lean to carry
out the inference using {name}`inferInstance`:

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance -- @inferInstance : {α : Sort u_1} → [i : α] → α
```

:::setup
```
variable (t : T)
```

In fact, you can use Lean's {lean}`(t : T)` notation to specify the class whose instance you are looking for,
in a concise manner:
:::

```lean
#check (inferInstance : Add Nat)
```

You can also use the auxiliary definition {lean}`inferInstanceAs`:

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs -- inferInstanceAs : (α : Sort u_1) → [i : α] → α
```

:::leanFirst
Sometimes Lean can't find an instance because the class is buried
under a definition. For example, Lean cannot
find an instance of {leanRef}`Inhabited (Set α)`. We can declare one
explicitly:

```lean
def Set (α : Type u) := α → Prop

/--
error: failed to synthesize
  Inhabited (Set α)

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Inhabited (Set α) :=
  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```
:::

At times, you may find that the type class inference fails to find an
expected instance, or, worse, falls into an infinite loop and times
out. To help debug in these situations, Lean enables you to request a
trace of the search:

```lean
set_option trace.Meta.synthInstance true
```

If you are using VS Code, you can read the results by hovering over
the relevant theorem or definition, or opening the messages window
with {kbd}[`Ctrl` `Shift` `Enter`].

You can also limit the search using the following options:

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

Option {option}`synthInstance.maxHeartbeats` specifies the maximum amount of
heartbeats per typeclass resolution problem. A heartbeat is the number of
(small) memory allocations (in thousands), 0 means there is no limit.
Option {option}`synthInstance.maxSize` is the maximum number of instances used
to construct a solution in the type class instance synthesis procedure.

Remember also that in both the VS Code and Emacs editor modes, tab
completion works in {kw}`set_option`, to help you find suitable options.

As noted above, the type class instances in a given context represent
a Prolog-like program, which gives rise to a backtracking search. Both
the efficiency of the program and the solutions that are found can
depend on the order in which the system tries the instance. Instances
which are declared last are tried first. Moreover, if instances are
declared in other modules, the order in which they are tried depends
on the order in which namespaces are opened. Instances declared in
namespaces which are opened later are tried earlier.

You can change the order that type class instances are tried by
assigning them a _priority_. When an instance is declared, it is
assigned a default priority value. You can assign other priorities
when defining an instance. The following example illustrates how this
is done:

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

# Coercions using Type Classes
%%%
tag := "coercions-using-type-classes"
%%%

:::setup
```
variable {n : Nat} {α : Type u} {as : List α}
def Set (α : Type u) := α → Prop

```

The most basic type of coercion maps elements of one type to another. For example, a coercion from {lean}`Nat` to {lean}`Int` allows us to view any element {lean}`n : Nat` as an element of {lean}`Int`. But some coercions depend on parameters; for example, for any type {lean}`α`, we can view any element {lean}`as : List α` as an element of {lean}`Set α`, namely, the set of elements occurring in the list. The corresponding coercion is defined on the “family” of types {lean}`List α`, parameterized by {lean}`α`.
:::

Lean allows us to declare three kinds of coercions:

- from a family of types to another family of types
- from a family of types to the class of sorts
- from a family of types to the class of function types

The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.

:::setup
```
variable {α : Type u} {β : Type v} [Coe α β]
```

In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from {lean}`α` to {lean}`β` by declaring an instance of {lean}`Coe α β`. For example, we can define a coercion from {lean}`Bool` to {lean}`Prop` as follows:

```lean
instance : Coe Bool Prop where
  coe b := b = true
```
:::

This enables us to use boolean terms in {kw}`if`-{kw}`then`-{kw}`else` expressions:

```lean
#eval if true then 5 else 3

#eval if false then 5 else 3
```

:::leanFirst
We can define a coercion from {leanRef}`List α` to {leanRef}`Set α` as follows:

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
------
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}

#check s ∪ [2, 3] -- s ∪ [2, 3].toSet : Set Nat
```
:::

We can use the notation {lit}`↑` to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet
instance : Coe (List α) (Set α) where
  coe a := a.toSet
------
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x -- let x := [2, 3].toSet; s ∪ x : Set Nat

#check let x := [2, 3]; s ∪ x -- let x := [2, 3]; s ∪ x.toSet : Set Nat
```


Lean also supports dependent coercions using the type class {lean}`CoeDep`. For example, we cannot coerce arbitrary propositions to {lean}`Bool`, only the ones that implement the {lean}`Decidable` typeclass.

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

Lean will also chain (non-dependent) coercions as necessary. Actually, the type class {lean}`CoeT` is the transitive closure of {lean}`Coe`.

Let us now consider the second kind of coercion. By the _class of sorts_, we mean the collection of universes {lean}`Type u`. A coercion of the second kind is of the form:

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

where {lit}`F` is a family of types as above. This allows us to write {lit}`s : t` whenever {lit}`t` is of type {lit}`F a₁ ... aₙ`. In other words, the coercion allows us to view the elements of {lit}`F a₁ ... aₙ` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a {lean}`Type`. For example, we can define a semigroup as follows:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

:::setup

```
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

variable {S : Semigroup} (a b : S.carrier)

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
universe u
```
In other words, a semigroup consists of a type, {leanRef}`carrier`, and a multiplication, {leanRef}`mul`, with the property that the multiplication is associative. The {kw}`instance` command allows us to write {lean}`a * b` instead of {lean}`Semigroup.mul S a b` whenever we have {lean}`a b : S.carrier`; notice that Lean can infer the argument {leanRef}`S` from the types of {leanRef}`a` and {leanRef}`b`. The function {lean}`Semigroup.carrier` maps the class {leanRef}`Semigroup` to the sort {leanRef}`Type u`:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
#check Semigroup.carrier -- Semigroup.carrier.{u} (self : Semigroup) : Type u
```

If we declare this function to be a coercion, then whenever we have a semigroup {lean}`S : Semigroup`, we can write {lean}`a : S` instead of {lean}`a : S.carrier`:

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

It is the coercion that makes it possible to write {leanRef}`(a b c : S)`. Note that, we define an instance of {leanRef}`CoeSort Semigroup (Type u)` instead of {lean}`Coe Semigroup (Type u)`.

:::

::::setup
```
variable (B : Type u) (C : Type v)

```

By the _class of function types_, we mean the collection of Pi types {lean}`(z : B) → C`. The third kind of coercion has the form:

```
    c : (x₁ : A₁) → ... → (xₙ : Aₙ) → (y : F x₁ ... xₙ) → (z : B) → C
```

:::leanFirst
where {lit}`F` is again a family of types and {lit}`B` and {lit}`C` can depend on {lit}`x₁, ..., xₙ, y`. This makes it possible to write {lit}`t s` whenever {lit}`t` is an element of {lit}`F a₁ ... aₙ`. In other words, the coercion enables us to view elements of {lit}`F a₁ ... aₙ` as functions. Continuing the example above, we can define the notion of a morphism between semigroups {leanRef}`S1` and {leanRef}`S2`. That is, a function from the carrier of {leanRef}`S1` to the carrier of {leanRef}`S2` (note the implicit coercion) that respects the multiplication. The projection {leanRef}`Morphism.mor` takes a morphism to the underlying function:


```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
------
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```
:::

As a result, it is a prime candidate for the third type of coercion.
::::

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
------
instance (S1 S2 : Semigroup) :
    CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
```

With the coercion in place, we can write {leanRef}`f (a * a * a)` instead of {leanRef}`f.mor (a * a * a)`. When the {leanRef}`Morphism`, {leanRef}`f`, is used where a function is expected, Lean inserts the coercion. Similar to {lean}`CoeSort`, we have yet another class {lean}`CoeFun` for this class of coercions. The parameter {lit}`γ` is used to specify the function type we are coercing to. This type may depend on the type we are coercing from.
