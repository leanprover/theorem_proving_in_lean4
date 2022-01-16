# Type classes

Type classes were introduced as a principled way of enabling
ad-hoc polymorphism in functional programming languages. We first observe that it
would be easy to implement an ad-hoc polymorphic function (such as addition) if the
function simply took the type-specific implementation of addition as an argument
and then called that implementation on the remaining arguments. For example,
suppose we declare a structure in Lean to hold implementations of addition
```lean
# namespace Ex
structure Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
# end Ex
```
In the above Lean code, the field `add` has type
`Add.add : {α : Type} → Add α → α → α → α`
where the curly braces around the type `a` mean that it is an implicit argument.
We could implement `double` by
```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a -> a -> a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20

# end Ex
```
Note that you can double a natural number `n` by `double { add := Nat.add } n`.
Of course, it would be highly cumbersome for users to manually pass the
implementations around in this way.
Indeed, it would defeat most of the potential benefits of ad-hoc
polymorphism.

The main idea behind type classes is to make arguments such as `Add a` implicit,
and to use a database of user-defined instances to synthesize the desired instances
automatically through a process known as typeclass resolution. In Lean, by changing
`structure` to `class` in the example above, the type of `Add.add` becomes
```lean
# namespace Ex
class Add (a : Type) where
  add : a -> a -> a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```
where the square brackets indicate that the argument of type `Add a` is *instance implicit*,
i.e. that it should be synthesized using typeclass resolution. This version of
`add` is the Lean analogue of the Haskell term `add :: Add a => a -> a -> a`.
Similarly, we can register an instance by
```lean
# namespace Ex
# class Add (a : Type) where
#  add : a -> a -> a
instance : Add Nat where
  add := Nat.add

# end Ex
```
Then for `n : Nat` and `m : Nat`, the term `Add.add n m` triggers typeclass resolution with the goal
of `Add Nat`, and typeclass resolution will synthesize the instance above. In
general, instances may depend on other instances in complicated ways. For example,
you can declare an (anonymous) instance stating that if `a` has addition, then `Array a`
has addition:
```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (. + .)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```
Note that `x + y` is notation for `Add.add x y` in Lean.

The example above demonstrates how type classes are used to overload notation.
Now, we explore another application. We often need an arbitrary element of a given type.
Recall that types may not have any elements in Lean.
It often happens that we would like a definition to return an arbitrary element in a "corner case."
For example, we may like the expression ``head xs`` to be of type ``a`` when ``xs`` is of type ``List a``.
Similarly, many theorems hold under the additional assumption that a type is not empty.
For example, if ``a`` is a type, ``exists x : a, x = x`` is true only if ``a`` is not empty.
The standard library defines a type class ``Inhabited`` to enable type class inference to infer a
"default" element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```
Note `Inhabited.default` doesn't have any explicit argument.

An element of the class ``Inhabited a`` is simply an expression of the form ``Inhabited.mk x``, for some element ``x : a``.
The projection ``Inhabited.default`` will allow us to "extract" such an element of ``a`` from an element of ``Inhabited a``.
Now we populate the class with some instances:

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```
You can use the command `export` to create the alias `default` for `Inhabited.default`
```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```

## Chaining Instances

If that were the extent of type class inference, it would not be all that impressive;
it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
What makes type class inference powerful is that one can *chain* instances. That is,
an instance declaration can in turn depend on an implicit instance of a type class.
This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.

For example, the following definition shows that if two types ``a`` and ``b`` are inhabited, then so is their product:
```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```
With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``Nat × Bool``:
```lean
# namespace Ex
# class Inhabited (a : Type u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# constant default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```
Similarly, we can inhabit type function with suitable constant functions:
```lean
instance [Inhabited b] : Inhabited (a -> b) where
  default := fun _ => default
```
As an exercise, try defining default instances for other types, such as `List` and `Sum` types.

The Lean standard library contains the definition `inferInstance`. It has type `{α : Sort u} → [i : α] → α`,
and is useful for triggering the type class resolution procedure when the expected type is an instance.
```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```
You can use the command `#print` to inspect how simple `inferInstance` is.
```lean
#print inferInstance
```

## ToString

The polymorphic method `toString` has type `{α : Type u} → [ToString α] → α → String`. You implement the instance
for your own types and use chaining to convert complex values into strings. Lean comes with `ToString` instances
for most builtin types.
```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
```
## Numerals

Numerals are polymorphic in Lean. You can use a numeral (e.g., `2`) to denote an element of any type that implements
the type class `OfNat`.
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

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat
```
Lean elaborates the terms `(2 : Nat)` and `(2 : Rational)` as
`OfNat.ofNat Nat 2 (instOfNatNat 2)` and
`OfNat.ofNat Rational 2 (instOfNatRational 2)` respectively.
We say the numerals `2` occurring in the elaborated terms are *raw* natural numbers.
You can input the raw natural number `2` using the macro `nat_lit 2`.
```lean
#check nat_lit 2  -- Nat
```
Raw natural numbers are *not* polymorphic.

The `OfNat` instance is parametric on the numeral. So, you can define instances for particular numerals.
The second argument is often a variable as in the example above, or a *raw* natural number.
```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

## Output parameters

By default, Lean only tries to synthesize an instance `Inhabited T` when the term `T` is known and does not
contain missing parts. The following command produces the error
"failed to create type class instance for `Inhabited (Nat × ?m.1499)`" because the type has a missing part (i.e., the `_`).
```lean
#check_failure (inferInstance : Inhabited (Nat × _))
```
You can view the parameter of the type class `Inhabited` as an *input* value for the type class synthesizer.
When a type class has multiple parameters, you can mark some of them as output parameters.
Lean will start type class synthesizer even when these parameters have missing parts.
In the following example, we use output parameters to define a *heterogeneous* polymorphic
multiplication.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```
The parameters `α` and `β` are considered input parameters and `γ` an output one.
Given an application `hMul a b`, after types of `a` and `b` are known, the type class
synthesizer is invoked, and the resulting type is obtained from the output parameter `γ`.
In the example above, we defined two instances. The first one is the homogeneous
multiplication for natural numbers. The second is the scalar multiplication for arrays.
Note that you chain instances and generalize the second instance.
```lean
# namespace Ex
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
# end Ex
```
You can use our new scalar array multiplication instance on arrays of type `Array β`
with a scalar of type `α` whenever you have an instance `HMul α β γ`.
In the last `#eval`, note that the instance was used twice on an array of arrays.

## Default instances

In the class `HMul`, the parameters `α` and `β` are treated as input values.
Thus, type class synthesis only starts after these two types are known. This may often
be too restrictive.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "failed to create type class instance for HMul Int ?m.1767 (?m.1797 x)"
#check_failure fun y => xs.map (fun x => hMul x y)
# end Ex
```
The instance `HMul` is not synthesized by Lean because the type of `y` has not been provided.
However, it is natural to assume that the type of `y` and `x` should be the same in
this kind of situation. We can achieve exactly that using *default instances*.
```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[defaultInstance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- Int -> List Int
# end Ex
```
By tagging the instance above with the attribute `defaultInstance`, we are instructing Lean
to use this instance on pending type class synthesis problems.
The actual Lean implementation defines homogeneous and heterogeneous classes for arithmetical operators.
Moreover, `a+b`, `a*b`, `a-b`, `a/b`, and `a%b` are notations for the heterogeneous versions.
The instance `OfNat Nat n` is the default instance (with priority 100) for the `OfNat` class. This is why the numeral
`2` has type `Nat` when the expected type is not known. You can define default instances with higher
priority to override the builtin ones.
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[defaultInstance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational
```
Priorities are also useful to control the interaction between different default instances.
For example, suppose `xs` has type `α`, when elaboration `xs.map (fun x => 2 * x)`, we want the homogeneous instance for multiplication
to have higher priority than the default instance for `OfNat`. This is particularly important when we have implemented only the instance
`HMul α α α`, and did not implement `HMul Nat α α`.
Now, we reveal how the notation `a*b` is defined in Lean.
```lean
# namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[defaultInstance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[defaultInstance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * "  => HMul.hMul
# end Ex
```
The `Mul` class is convenient for types that only implement the homogeneous multiplication.

## Local Instances

Type classes are implemented using attributes in Lean. Thus, you can
use the `local` modifier to indicate that they only have effect until
the current ``section`` or ``namespace`` is closed, or until the end
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

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to sythesize instance
```

You can also temporarily disable an instance using the `attribute` command
until the current ``section`` or ``namespace`` is closed, or until the end
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

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to sythesize instance
```

We recommend you only use this command to diagnose problems.

## Scoped Instances

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

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

You can use the command `open scoped <namespace>` to activate scoped attributes but will
not "open" the names from the namespace.

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

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
```

## Decidable Propositions

Let us consider another example of a type class defined in the
standard library, namely the type class of ``Decidable``
propositions. Roughly speaking, an element of ``Prop`` is said to be
decidable if we can decide whether it is true or false. The
distinction is only useful in constructive mathematics; classically,
every proposition is decidable. But if we use the classical principle,
say, to define a function by cases, that function will not be
computable. Algorithmically speaking, the ``Decidable`` type class can
be used to infer a procedure that effectively determines whether or
not the proposition is true. As a result, the type class supports such
computational definitions when they are possible while at the same
time allowing a smooth transition to the use of classical definitions
and classical reasoning.

In the standard library, ``Decidable`` is defined formally as follows:

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

Logically speaking, having an element ``t : Decidable p`` is stronger
than having an element ``t : p ∨ ¬p``; it enables us to define values
of an arbitrary type depending on the truth value of ``p``. For
example, for the expression ``if p then a else b`` to make sense, we
need to know that ``p`` is decidable. That expression is syntactic
sugar for ``ite p a b``, where ``ite`` is defined as follows:

```lean
# namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
# end Hidden
```

The standard library also contains a variant of ``ite`` called
``dite``, the dependent if-then-else expression. It is defined as
follows:

```lean
# namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
# end Hidden
```

That is, in ``dite c t e``, we can assume ``hc : c`` in the "then"
branch, and ``hnc : ¬ c`` in the "else" branch. To make ``dite`` more
convenient to use, Lean allows us to write ``if h : c then t else e``
instead of ``dite c (λ h : c, t) (λ h : ¬ c, e)``.

Without classical logic, we cannot prove that every proposition is
decidable. But we can prove that *certain* propositions are
decidable. For example, we can prove the decidability of basic
operations like equality and comparisons on the natural numbers and
the integers. Moreover, decidability is preserved under propositional
connectives:

```lean
#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot
#check @instDecidableArrow
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
the decidability of the proposition ``x < a ∨ x > b``, simply by
applying appropriate instances.

With the classical axioms, we can prove that every proposition is
decidable. You can import the classical axioms and make the generic
instance of decidability available by opening the `Classical` namespace.

```lean
open Classical
```

Thereafter ``decidable p`` has an instance for every ``p``.
Thus all theorems in the library
that rely on decidability assumptions are freely available when you
want to reason classically. In [Chapter Axioms and Computation](./axioms_and_computation.md),
we will see that using the law of the
excluded middle to define functions can prevent them from being used
computationally. Thus, the standard library assigns a low priority to
the `propDecidable` instance.

```lean
# namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
# end Hidden
```

The guarantees that Lean will favor other instances and fall back on
``propDecidable`` only after other attempts to infer decidability have
failed.

The ``Decidable`` type class also provides a bit of small-scale
automation for proving theorems. The standard library introduces the
tactic `decide` that uses the `Decidable` instance to solve simple goals.

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
```

They work as follows. The expression ``decide p`` tries to infer a
decision procedure for ``p``, and, if it is successful, evaluates to
either ``true`` or ``false``. In particular, if ``p`` is a true closed
expression, ``decide p`` will reduce definitionally to the Boolean ``true``.
On the assumption that ``decide p = true`` holds, ``of_decide_eq_true``
produces a proof of ``p``. The tactic ``decide`` puts it all together: to
prove a target ``p``. By the previous observations,
``decide`` will succeed any time the inferred decision procedure
 for ``c`` has enough information to evaluate, definitionally, to the ``isTrue`` case.


Managing Type Class Inference
-----------------------------

If you are ever in a situation where you need to supply an expression
that Lean can infer by type class inference, you can ask Lean to carry
out the inference using `inferInstance`:

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α
```

In fact, you can use Lean's ``(t : T)`` notation to specify the class whose instance you are looking for,
in a concise manner:

```lean
#check (inferInstance : Add Nat)
```

You can also use the auxiliary definition `inferInstanceAs`:

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α
```


Sometimes Lean can't find an instance because the class is buried
under a definition. For example, Lean cannot
find an instance of ``Inhabited (Set α)``. We can declare one
explicitly:

```lean

def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```

At times, you may find that the type class inference fails to find an
expected instance, or, worse, falls into an infinite loop and times
out. To help debug in these situations, Lean enables you to request a
trace of the search:

```
set_option trace.Meta.synthInstance true
```

If you are using VS Code, you can read the results by hovering over
the relevant theorem or definition, or opening the messages window
with ``Ctrl-Shift-Enter``. In Emacs, you can use ``C-c C-x`` to run an
independent Lean process on your file, and the output buffer will show
a trace every time the type class resolution procedure is subsequently
triggered.

You can also limit the search using the following options:
```
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

Option `synthInstance.maxHeartbeats` specifies the maximum amount of
heartbeats per typeclass resolution problem. A heartbeat is number of
(small) memory allocations (in thousands), 0 means there is no limit.
Option `synthInstance.maxSize` is the maximum number of instances used
to construct a solution in the type class instance synthesis procedure

Remember also that in both the VS Code and Emacs editor modes, tab
completion works in ``set_option``, to help you find suitable options.

As noted above, the type class instances in a given context represent
a Prolog-like program, which gives rise to a backtracking search. Both
the efficiency of the program and the solutions that are found can
depend on the order in which the system tries the instance. Instances
which are declared last are tried first. Moreover, if instances are
declared in other modules, the order in which they are tried depends
on the order in which namespaces are opened. Instances declared in
namespaces which are opened later are tried earlier.

You can change the order that type classes instances are tried by
assigning them a *priority*. When an instance is declared, it is
assigned a default priority value. You can assign other priorities
when defining an instance. The following example illustrates how this
is done:

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

<!--
TODO: we may change the coercion mechanism
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

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}
    def l : list nat := [3, 4]

    #check s ∪ l -- set nat

Coercions are only considered if the given and expected types do not contain metavariables at elaboration time. In the following example, when we elaborate the union operator, the type of ``[3, 2]`` is ``list ?m``, and a coercion will not be considered since it contains metavariables.

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
      has_coe (list α) (set α) :=
    ⟨list.to_set⟩

    def s : set nat  := {1, 2}

    -- BEGIN
    /- The following #check command produces an error. -/
    -- #check s ∪ [3, 2]
    -- END

We can work around this issue by using a type ascription.

.. code-block:: lean

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
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

    def list.to_set {α : Type*} : list α → set α
    | []     := ∅
    | (h::t) := {h} ∪ list.to_set t

    instance list_to_set_coe (α : Type*) :
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

    namespace hidden
    -- BEGIN
    instance coe_subtype {α : Type*} {p : α → Prop} :
      has_coe {x // p x} α :=
    ⟨λ s, subtype.val s⟩
    -- END
    end hidden

Lean will also chain coercions as necessary. Actually, the type class ``has_coe_t`` is the transitive closure of ``has_coe``. You may have noticed that the type of ``coe`` depends on ``has_lift_t``, the transitive closure of the type class ``has_lift``, instead of ``has_coe_t``. Every instance of ``has_coe_t`` is also an instance of ``has_lift_t``, but the elaborator only introduces automatically instances of ``has_coe_t``. That is, to be able to coerce using an instance of ``has_lift_t``, we must use the operator ``↑``. In the standard library, we have the following instance:

.. code-block:: lean

    namespace hidden
    universes u v

    instance lift_list {a : Type u} {b : Type v} [has_lift_t a b] :
      has_lift (list a) (list b) :=
    ⟨λ l, list.map (@coe a b _) l⟩

    variables s : list nat
    variables r : list int
    #check ↑s ++ r

    end hidden

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

With the coercion in place, we can write ``f (a * a * a)`` instead of ``morphism.mor f (a * a * a)``. When the ``morphism``, ``f``, is used where a function is expected, Lean inserts the coercion. Similar to ``has_coe_to_sort``, we have yet another class ``has_coe_to_fun`` for this class of coercions. The field ``F`` is used to specify the function type we are coercing to. This type may depend on the type we are coercing from.

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
-->
