Quantifiers and Equality
========================

The last chapter introduced you to methods that construct proofs of
statements involving the propositional connectives. In this chapter,
we extend the repertoire of logical constructions to include the
universal and existential quantifiers, and the equality relation.

The Universal Quantifier
------------------------

Notice that if ``α`` is any type, we can represent a unary predicate
``p`` on ``α`` as an object of type ``α → Prop``. In that case, given
``x : α``, ``p x`` denotes the assertion that ``p`` holds of
``x``. Similarly, an object ``r : α → α → Prop`` denotes a binary
relation on ``α``: given ``x y : α``, ``r x y`` denotes the assertion
that ``x`` is related to ``y``.

The universal quantifier, ``∀ x : α, p x`` is supposed to denote the
assertion that "for every ``x : α``, ``p x``" holds. As with the
propositional connectives, in systems of natural deduction, "forall"
is governed by an introduction and elimination rule. Informally, the
introduction rule states:

> Given a proof of ``p x``, in a context where ``x : α`` is arbitrary, we obtain a proof ``∀ x : α, p x``.

The elimination rule states:

> Given a proof ``∀ x : α, p x`` and any term ``t : α``, we obtain a proof of ``p t``.

As was the case for implication, the propositions-as-types
interpretation now comes into play. Remember the introduction and
elimination rules for dependent arrow types:

> Given a term ``t`` of type ``β x``, in a context where ``x : α`` is arbitrary, we have ``(fun x : α => t) : (x : α) → β x``.

The elimination rule states:

> Given a term ``s : (x : α) → β x`` and any term ``t : α``, we have ``s t : β t``.

In the case where ``p x`` has type ``Prop``, if we replace
``(x : α) → β x`` with ``∀ x : α, p x``, we can read these as the correct rules
for building proofs involving the universal quantifier.

The Calculus of Constructions therefore identifies dependent arrow
types with forall-expressions in this way. If ``p`` is any expression,
``∀ x : α, p`` is nothing more than alternative notation for
``(x : α) → p``, with the idea that the former is more natural than the latter
in cases where ``p`` is a proposition. Typically, the expression ``p``
will depend on ``x : α``. Recall that, in the case of ordinary
function spaces, we could interpret ``α → β`` as the special case of
``(x : α) → β`` in which ``β`` does not depend on ``x``. Similarly, we
can think of an implication ``p → q`` between propositions as the
special case of ``∀ x : p, q`` in which the expression ``q`` does not
depend on ``x``.

Here is an example of how the propositions-as-types correspondence gets put into practice.

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

As a notational convention, we give the universal quantifier the
widest scope possible, so parentheses are needed to limit the
quantifier over ``x`` to the hypothesis in the example above. The
canonical way to prove ``∀ y : α, p y`` is to take an arbitrary ``y``,
and prove ``p y``. This is the introduction rule. Now, given that
``h`` has type ``∀ x : α, p x ∧ q x``, the expression ``h y`` has type
``p y ∧ q y``. This is the elimination rule. Taking the left conjunct
gives the desired conclusion, ``p y``.

Remember that expressions which differ up to renaming of bound
variables are considered to be equivalent. So, for example, we could
have used the same variable, ``x``, in both the hypothesis and
conclusion, and instantiated it by a different variable, ``z``, in the
proof:

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

As another example, here is how we can express the fact that a relation, ``r``, is transitive:

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c -- r a b → r b c → r a c
#check trans_r a b c hab -- r b c → r a c
#check trans_r a b c hab hbc -- r a c
```

Think about what is going on here. When we instantiate ``trans_r`` at
the values ``a b c``, we end up with a proof of ``r a b → r b c → r a c``.
Applying this to the "hypothesis" ``hab : r a b``, we get a proof
of the implication ``r b c → r a c``. Finally, applying it to the
hypothesis ``hbc`` yields a proof of the conclusion ``r a c``.

In situations like this, it can be tedious to supply the arguments
``a b c``, when they can be inferred from ``hab hbc``. For that reason, it
is common to make these arguments implicit:

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

The advantage is that we can simply write ``trans_r hab hbc`` as a
proof of ``r a c``. A disadvantage is that Lean does not have enough
information to infer the types of the arguments in the expressions
``trans_r`` and ``trans_r hab``. The output of the first ``#check``
command is ``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``, indicating
that the implicit arguments are unspecified in this case.

Here is an example of how we can carry out elementary reasoning with an equivalence relation:

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

To get used to using universal quantifiers, you should try some of the
exercises at the end of this section.

It is the typing rule for dependent arrow types, and the universal
quantifier in particular, that distinguishes ``Prop`` from other
types.  Suppose we have ``α : Sort i`` and ``β : Sort j``, where the
expression ``β`` may depend on a variable ``x : α``. Then
``(x : α) → β`` is an element of ``Sort (imax i j)``, where ``imax i j`` is the
maximum of ``i`` and ``j`` if ``j`` is not 0, and 0 otherwise.

The idea is as follows. If ``j`` is not ``0``, then ``(x : α) → β`` is
an element of ``Sort (max i j)``. In other words, the type of
dependent functions from ``α`` to ``β`` "lives" in the universe whose
index is the maximum of ``i`` and ``j``. Suppose, however, that ``β``
is of ``Sort 0``, that is, an element of ``Prop``. In that case,
``(x : α) → β`` is an element of ``Sort 0`` as well, no matter which
type universe ``α`` lives in. In other words, if ``β`` is a
proposition depending on ``α``, then ``∀ x : α, β`` is again a
proposition. This reflects the interpretation of ``Prop`` as the type
of propositions rather than data, and it is what makes ``Prop``
*impredicative*.

The term "predicative" stems from foundational developments around the
turn of the twentieth century, when logicians such as Poincaré and
Russell blamed set-theoretic paradoxes on the "vicious circles" that
arise when we define a property by quantifying over a collection that
includes the very property being defined. Notice that if ``α`` is any
type, we can form the type ``α → Prop`` of all predicates on ``α``
(the "power type of ``α``"). The impredicativity of ``Prop`` means that we
can form propositions that quantify over ``α → Prop``. In particular,
we can define predicates on ``α`` by quantifying over all predicates
on ``α``, which is exactly the type of circularity that was once
considered problematic.

Equality
--------

Let us now turn to one of the most fundamental relations defined in
Lean's library, namely, the equality relation. In [Chapter Inductive Types](inductive_types.md),
we will explain *how* equality is defined from the primitives of Lean's logical framework.
In the meanwhile, here we explain how to use it.

Of course, a fundamental property of equality is that it is an equivalence relation:

```lean
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

We can make the output easier to read by telling Lean not to insert
the implicit arguments (which are displayed here as metavariables).

```lean
universe u

#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

The inscription ``.{u}`` tells Lean to instantiate the constants at the universe ``u``.

Thus, for example, we can specialize the example from the previous section to the equality relation:

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

We can also use the projection notation:

```lean
# variable (α : Type) (a b c d : α)
# variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd
```

Reflexivity is more powerful than it looks. Recall that terms in the
Calculus of Constructions have a computational interpretation, and
that the logical framework treats terms with a common reduct as the
same. As a result, some nontrivial identities can be proved by
reflexivity:

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

This feature of the framework is so important that the library defines a notation ``rfl`` for ``Eq.refl _``:

```lean
# variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

Equality is much more than an equivalence relation, however. It has
the important property that every assertion respects the equivalence,
in the sense that we can substitute equal expressions without changing
the truth value. That is, given ``h1 : a = b`` and ``h2 : p a``, we
can construct a proof for ``p b`` using substitution:
``Eq.subst h1 h2``.

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

The triangle in the second presentation is a macro built on top of
``Eq.subst`` and ``Eq.symm``, and you can enter it by typing ``\t``.

The rule ``Eq.subst`` is used to define the following auxiliary rules,
which carry out more explicit substitutions. They are designed to deal
with applicative terms, that is, terms of form ``s t``. Specifically,
``congrArg`` can be used to replace the argument, ``congrFun`` can be
used to replace the term that is being applied, and ``congr`` can be
used to replace both at once.

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

Lean's library contains a large number of common identities, such as these:

```lean
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

Note that ``Nat.mul_add`` and ``Nat.add_mul`` are alternative names
for ``Nat.left_distrib`` and ``Nat.right_distrib``, respectively.  The
properties above are stated for the natural numbers (type ``Nat``).

Here is an example of a calculation in the natural numbers that uses
substitution combined with associativity and distributivity.

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

Notice that the second implicit parameter to ``Eq.subst``, which
provides the context in which the substitution is to occur, has type
``α → Prop``.  Inferring this predicate therefore requires an instance
of *higher-order unification*. In full generality, the problem of
determining whether a higher-order unifier exists is undecidable, and
Lean can at best provide imperfect and approximate solutions to the
problem. As a result, ``Eq.subst`` doesn't always do what you want it
to.  The macro ``h ▸ e`` uses more effective heuristics for computing
this implicit parameter, and often succeeds in situations where
applying ``Eq.subst`` fails.

Because equational reasoning is so common and important, Lean provides
a number of mechanisms to carry it out more effectively. The next
section offers syntax that allow you to write calculational proofs in
a more natural and perspicuous way. But, more importantly, equational
reasoning is supported by a term rewriter, a simplifier, and other
kinds of automation. The term rewriter and simplifier are described
briefly in the next section, and then in greater detail in the next
chapter.

Calculational Proofs
--------------------

A calculational proof is just a chain of intermediate results that are
meant to be composed by basic principles such as the transitivity of
equality. In Lean, a calculational proof starts with the keyword
``calc``, and has the following syntax:

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

Note that the `calc` relations all have the same indentation. Each
``<proof>_i`` is a proof for ``<expr>_{i-1} op_i <expr>_i``.

We can also use `_` in the first relation (right after ``<expr>_0``)
which is useful to align the sequence of relation/proof pairs:

```
calc <expr>_0 
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

Here is an example:

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

This style of writing proofs is most effective when it is used in
conjunction with the ``simp`` and ``rewrite`` tactics, which are
discussed in greater detail in the next chapter. For example, using
the abbreviation ``rw`` for rewrite, the proof above could be written
as follows:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

Essentially, the ``rw`` tactic uses a given equality (which can be a
hypothesis, a theorem name, or a complex term) to "rewrite" the
goal. If doing so reduces the goal to an identity ``t = t``, the
tactic applies reflexivity to prove it.

Rewrites can be applied sequentially, so that the proof above can be
shortened to this:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

Or even this:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

The ``simp`` tactic, instead, rewrites the goal by applying the given
identities repeatedly, in any order, anywhere they are applicable in a
term. It also uses other rules that have been previously declared to
the system, and applies commutativity wisely to avoid looping. As a
result, we can also prove the theorem as follows:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

We will discuss variations of ``rw`` and ``simp`` in the next chapter.

The ``calc`` command can be configured for any relation that supports
some form of transitivity. It can even combine different relations.

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

You can "teach" `calc` new transitivity theorems by adding new instances
of the `Trans` type class. Type classes are introduced later, but the following
small example demonstrates how to extend the `calc` notation using new `Trans` instances.

```lean
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..
```

The example above also makes it clear that you can use `calc` even if you
do not have an infix notation for your relation. Finally we remark that
the vertical bar `∣` in the example above is the unicode one. We use
unicode to make sure we do not overload the ASCII `|` used in the
`match .. with` expression.

With ``calc``, we can write the proof in the last section in a more
natural and perspicuous way.

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
```

The alternative `calc` notation is worth considering here. When the
first expression is taking this much space, using `_` in the first
relation naturally aligns all relations:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
```

Here the left arrow before ``Nat.add_assoc`` tells rewrite to use the
identity in the opposite direction. (You can enter it with ``\l`` or
use the ascii equivalent, ``<-``.) If brevity is what we are after,
both ``rw`` and ``simp`` can do the job on their own:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

The Existential Quantifier
--------------------------

Finally, consider the existential quantifier, which can be written as
either ``exists x : α, p x`` or ``∃ x : α, p x``.  Both versions are
actually notationally convenient abbreviations for a more long-winded
expression, ``Exists (fun x : α => p x)``, defined in Lean's library.

As you should by now expect, the library includes both an introduction
rule and an elimination rule. The introduction rule is
straightforward: to prove ``∃ x : α, p x``, it suffices to provide a
suitable term ``t`` and a proof of ``p t``. Here are some examples:

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p
```

We can use the anonymous constructor notation ``⟨t, h⟩`` for
``Exists.intro t h``, when the type is clear from the context.

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

Note that ``Exists.intro`` has implicit arguments: Lean has to infer
the predicate ``p : α → Prop`` in the conclusion ``∃ x, p x``.  This
is not a trivial affair. For example, if we have
``hg : g 0 0 = 0`` and write ``Exists.intro 0 hg``, there are many possible values
for the predicate ``p``, corresponding to the theorems ``∃ x, g x x = x``,
``∃ x, g x x = 0``, ``∃ x, g x 0 = x``, etc. Lean uses the
context to infer which one is appropriate. This is illustrated in the
following example, in which we set the option ``pp.explicit`` to true
to ask Lean's pretty-printer to show the implicit arguments.

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
```

We can view ``Exists.intro`` as an information-hiding operation, since
it hides the witness to the body of the assertion. The existential
elimination rule, ``Exists.elim``, performs the opposite operation. It
allows us to prove a proposition ``q`` from ``∃ x : α, p x``, by
showing that ``q`` follows from ``p w`` for an arbitrary value
``w``. Roughly speaking, since we know there is an ``x`` satisfying
``p x``, we can give it a name, say, ``w``. If ``q`` does not mention
``w``, then showing that ``q`` follows from ``p w`` is tantamount to
showing that ``q`` follows from the existence of any such ``x``. Here
is an example:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

It may be helpful to compare the exists-elimination rule to the
or-elimination rule: the assertion ``∃ x : α, p x`` can be thought of
as a big disjunction of the propositions ``p a``, as ``a`` ranges over
all the elements of ``α``. Note that the anonymous constructor
notation ``⟨w, hw.right, hw.left⟩`` abbreviates a nested constructor
application; we could equally well have written ``⟨w, ⟨hw.right, hw.left⟩⟩``.

Notice that an existential proposition is very similar to a sigma
type, as described in dependent types section.  The difference is that
given ``a : α`` and ``h : p a``, the term ``Exists.intro a h`` has
type ``(∃ x : α, p x) : Prop`` and ``Sigma.mk a h`` has type
``(Σ x : α, p x) : Type``. The similarity between ``∃`` and ``Σ`` is another
instance of the Curry-Howard isomorphism.

Lean provides a more convenient way to eliminate from an existential
quantifier with the ``match`` expression:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

The ``match`` expression is part of Lean's function definition system,
which provides convenient and expressive ways of defining complex
functions.  Once again, it is the Curry-Howard isomorphism that allows
us to co-opt this mechanism for writing proofs as well.  The ``match``
statement "destructs" the existential assertion into the components
``w`` and ``hw``, which can then be used in the body of the statement
to prove the proposition. We can annotate the types used in the match
for greater clarity:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

We can even use the match statement to decompose the conjunction at the same time:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

Lean also provides a pattern-matching ``let`` expression:

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

This is essentially just alternative notation for the ``match``
construct above. Lean will even allow us to use an implicit ``match``
in the ``fun`` expression:

```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

We will see in [Chapter Induction and Recursion](./induction_and_recursion.md) that all these variations are
instances of a more general pattern-matching construct.

In the following example, we define ``is_even a`` as ``∃ b, a = 2 * b``,
and then we show that the sum of two even numbers is an even number.

```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
```

Using the various gadgets described in this chapter --- the match
statement, anonymous constructors, and the ``rewrite`` tactic, we can
write this proof concisely as follows:

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

Just as the constructive "or" is stronger than the classical "or," so,
too, is the constructive "exists" stronger than the classical
"exists". For example, the following implication requires classical
reasoning because, from a constructive standpoint, knowing that it is
not the case that every ``x`` satisfies ``¬ p`` is not the same as
having a particular ``x`` that satisfies ``p``.

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```

What follows are some common identities involving the existential
quantifier. In the exercises below, we encourage you to prove as many
as you can. We also leave it to you to determine which are
nonconstructive, and hence require some form of classical reasoning.

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

Notice that the second example and the last two examples require the
assumption that there is at least one element ``a`` of type ``α``.

Here are solutions to two of the more difficult ones:

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

More on the Proof Language
--------------------------

We have seen that keywords like ``fun``, ``have``, and ``show`` make
it possible to write formal proof terms that mirror the structure of
informal mathematical proofs. In this section, we discuss some
additional features of the proof language that are often convenient.

To start with, we can use anonymous "have" expressions to introduce an
auxiliary goal without having to label it. We can refer to the last
expression introduced in this way using the keyword ``this``:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

Often proofs move from one fact to the next, so this can be effective
in eliminating the clutter of lots of labels.

When the goal can be inferred, we can also ask Lean instead to fill in
the proof by writing ``by assumption``:

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

This tells Lean to use the ``assumption`` tactic, which, in turn,
proves the goal by finding a suitable hypothesis in the local
context. We will learn more about the ``assumption`` tactic in the
next chapter.

We can also ask Lean to fill in the proof by writing ``‹p›``, where
``p`` is the proposition whose proof we want Lean to find in the
context.  You can type these corner quotes using ``\f<`` and ``\f>``,
respectively. The letter "f" is for "French," since the unicode
symbols can also be used as French quotation marks. In fact, the
notation is defined in Lean as follows:

```lean
notation "‹" p "›" => show p by assumption
```

This approach is more robust than using ``by assumption``, because the
type of the assumption that needs to be inferred is given
explicitly. It also makes proofs more readable. Here is a more
elaborate example:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

Keep in mind that you can use the French quotation marks in this way
to refer to *anything* in the context, not just things that were
introduced anonymously. Its use is also not limited to propositions,
though using it for data is somewhat odd:

```lean
example (n : Nat) : Nat := ‹Nat›
```

Later, we show how you can extend the proof language using the Lean macro system.

Exercises
---------

1. Prove these equivalences:

```lean
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```

You should also try to understand why the reverse implication is not derivable in the last example.

2. It is often possible to bring a component of a formula outside a
   universal quantifier, when it does not depend on the quantified
   variable. Try proving these (one direction of the second of these
   requires classical logic):

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

3. Consider the "barber paradox," that is, the claim that in a certain
   town there is a (male) barber that shaves all and only the men who
   do not shave themselves. Prove that this is a contradiction:

```lean
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
```

4. Remember that, without any parameters, an expression of type
   ``Prop`` is just an assertion. Fill in the definitions of ``prime``
   and ``Fermat_prime`` below, and construct each of the given
   assertions. For example, you can say that there are infinitely many
   primes by asserting that for every natural number ``n``, there is a
   prime number greater than ``n``. Goldbach's weak conjecture states
   that every odd number greater than 5 is the sum of three
   primes. Look up the definition of a Fermat prime or any of the
   other statements, if necessary.

```lean
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
```

5. Prove as many of the identities listed in the Existential
   Quantifier section as you can.
