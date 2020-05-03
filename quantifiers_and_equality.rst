.. _quantifiers_and_equality:

Quantifiers and Equality
========================

The last chapter introduced you to methods that construct proofs of statements involving the propositional connectives. In this chapter, we extend the repertoire of logical constructions to include the universal and existential quantifiers, and the equality relation.

The Universal Quantifier
------------------------

Notice that if ``α`` is any type, we can represent a unary predicate ``p`` on ``α`` as an object of type ``α → Prop``. In that case, given ``x : α``, ``p x`` denotes the assertion that ``p`` holds of ``x``. Similarly, an object ``r : α → α → Prop`` denotes a binary relation on ``α``: given ``x y : α``, ``r x y`` denotes the assertion that ``x`` is related to ``y``.

The universal quantifier, ``∀ x : α, p x`` is supposed to denote the assertion that "for every ``x : α``, ``p x``" holds. As with the propositional connectives, in systems of natural deduction, "forall" is governed by an introduction and elimination rule. Informally, the introduction rule states:

    Given a proof of ``p x``, in a context where ``x : α`` is arbitrary, we obtain a proof ``∀ x : α, p x``.

The elimination rule states:

    Given a proof ``∀ x : α, p x`` and any term ``t : α``, we obtain a proof of ``p t``.

As was the case for implication, the propositions-as-types interpretation now comes into play. Remember the introduction and elimination rules for Pi types:

    Given a term ``t`` of type ``β x``, in a context where ``x : α`` is arbitrary, we have ``(λ x : α, t) : Π x : α, β x``.

The elimination rule states:

    Given a term ``s : Π x : α, β x`` and any term ``t : α``, we have ``s t : β t``.

In the case where ``p x`` has type ``Prop``, if we replace ``Π x : α, β x`` with ``∀ x : α, p x``, we can read these as the correct rules for building proofs involving the universal quantifier.

The Calculus of Constructions therefore identifies ``Π`` and ``∀`` in this way. If ``p`` is any expression, ``∀ x : α, p`` is nothing more than alternative notation for ``Π x : α, p``, with the idea that the former is more natural than the latter in cases where ``p`` is a proposition. Typically, the expression ``p`` will depend on ``x : α``. Recall that, in the case of ordinary function spaces, we could interpret ``α → β`` as the special case of ``Π x : α, β`` in which ``β`` does not depend on ``x``. Similarly, we can think of an implication ``p → q`` between propositions as the special case of ``∀ x : p, q`` in which the expression ``q`` does not depend on ``x``.

Here is an example of how the propositions-as-types correspondence gets put into practice.

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
    assume h : ∀ x : α, p x ∧ q x,
    assume y : α,
    show p y, from (h y).left

As a notational convention, we give the universal quantifier the widest scope possible, so parentheses are needed to limit the quantifier over ``x`` to the hypothesis in the example above. The canonical way to prove ``∀ y : α, p y`` is to take an arbitrary ``y``, and prove ``p y``. This is the introduction rule. Now, given that ``h`` has type ``∀ x : α, p x ∧ q x``, the expression ``h y`` has type ``p y ∧ q y``. This is the elimination rule. Taking the left conjunct gives the desired conclusion, ``p y``.

Remember that expressions which differ up to renaming of bound variables are considered to be equivalent. So, for example, we could have used the same variable, ``x``, in both the hypothesis and conclusion, and instantiated it by a different variable, ``z``, in the proof:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    -- BEGIN
    example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
    assume h : ∀ x : α, p x ∧ q x,
    assume z : α,
    show p z, from and.elim_left (h z)
    -- END

As another example, here is how we can express the fact that a relation, ``r``, is transitive:

.. code-block:: lean

    variables (α : Type) (r : α → α → Prop)
    variable  trans_r : ∀ x y z, r x y → r y z → r x z

    variables a b c : α
    variables (hab : r a b) (hbc : r b c)

    #check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
    #check trans_r a b c
    #check trans_r a b c hab
    #check trans_r a b c hab hbc

Think about what is going on here. When we instantiate ``trans_r`` at the values ``a b c``, we end up with a proof of ``r a b → r b c → r a c``. Applying this to the "hypothesis" ``hab : r a b``, we get a proof of the implication ``r b c → r a c``. Finally, applying it to the hypothesis ``hbc`` yields a proof of the conclusion ``r a c``.

In situations like this, it can be tedious to supply the arguments ``a b c``, when they can be inferred from ``hab hbc``. For that reason, it is common to make these arguments implicit:

.. code-block:: lean

    universe u
    variables (α : Type u) (r : α → α → Prop)
    variable  trans_r : ∀ {x y z}, r x y → r y z → r x z

    variables (a b c : α)
    variables (hab : r a b) (hbc : r b c)

    #check trans_r
    #check trans_r hab
    #check trans_r hab hbc

The advantage is that we can simply write ``trans_r hab hbc`` as a proof of ``r a c``. A disadvantage is that Lean does not have enough information to infer the types of the arguments in the expressions ``trans_r`` and ``trans_r hab``. The output of the first ``#check`` command is ``r ?M_1 ?M_2 → r ?M_2 ?M_3 → r ?M_1 ?M_3``, indicating that the implicit arguments are unspecified in this case.

Here is an example of how we can carry out elementary reasoning with an equivalence relation:

.. code-block:: lean

    variables (α : Type) (r : α → α → Prop)

    variable refl_r : ∀ x, r x x
    variable symm_r : ∀ {x y}, r x y → r y x
    variable trans_r : ∀ {x y z}, r x y → r y z → r x z

    example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : 
      r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd

To get used to using universal quantifiers, you should try some of the exercises at the end of this section.

It is the typing rule for Pi types, and the universal quantifier in particular, that distinguishes ``Prop`` from other types. Suppose we have ``α : Sort i`` and ``β : Sort j``, where the expression ``β`` may depend on a variable ``x : α``. Then ``Π x : α, β`` is an element of ``Sort (imax i j)``, where ``imax i j`` is the maximum of ``i`` and ``j`` if ``j`` is not 0, and 0 otherwise.

The idea is as follows. If ``j`` is not ``0``, then ``Π x : α, β`` is an element of ``Sort (max i j)``. In other words, the type of dependent functions from ``α`` to ``β`` "lives" in the universe whose index is the maximum of ``i`` and ``j``. Suppose, however, that ``β`` is of ``Sort 0``, that is, an element of ``Prop``. In that case, ``Π x : α, β`` is an element of ``Sort 0`` as well, no matter which type universe ``α`` lives in. In other words, if ``β`` is a proposition depending on ``α``, then ``∀ x : α, β`` is again a proposition. This reflects the interpretation of ``Prop`` as the type of propositions rather than data, and it is what makes ``Prop`` *impredicative*.

The term "predicative" stems from foundational developments around the turn of the twentieth century, when logicians such as Poincaré and Russell blamed set-theoretic paradoxes on the "vicious circles" that arise when we define a property by quantifying over a collection that includes the very property being defined. Notice that if ``α`` is any type, we can form the type ``α → Prop`` of all predicates on ``α`` (the "power type of ``α``"). The impredicativity of Prop means that we can form propositions that quantify over ``α → Prop``. In particular, we can define predicates on ``α`` by quantifying over all predicates on ``α``, which is exactly the type of circularity that was once considered
problematic.

.. _equality:

Equality
--------

Let us now turn to one of the most fundamental relations defined in Lean's library, namely, the equality relation. In :numref:`Chapter %s <inductive_types>`, we will explain *how* equality is defined from the primitives of Lean's logical framework. In the meanwhile, here we explain how to use it.

Of course, a fundamental property of equality is that it is an equivalence relation:

.. code-block:: lean

    #check eq.refl    -- ∀ (a : ?M_1), a = a
    #check eq.symm    -- ?M_2 = ?M_3 → ?M_3 = ?M_2
    #check eq.trans   -- ?M_2 = ?M_3 → ?M_3 = ?M_4 → ?M_2 = ?M_4

We can make the output easier to read by telling Lean not to insert the implicit arguments (which are displayed here as metavariables).

.. code-block:: lean

    universe u

    #check @eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
    #check @eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
    #check @eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, 
                          --   a = b → b = c → a = c

The inscription ``.{u}`` tells Lean to instantiate the constants at the universe ``u``.

Thus, for example, we can specialize the example from the previous section to the equality relation:

.. code-block:: lean

    universe u
    variables (α : Type u) (a b c d : α)
    variables (hab : a = b) (hcb : c = b) (hcd : c = d)

    example : a = d :=
    eq.trans (eq.trans hab (eq.symm hcb)) hcd

We can also use the projection notation:

.. code-block:: lean

    universe u
    variables (α : Type u) (a b c d : α)
    variables (hab : a = b) (hcb : c = b) (hcd : c = d)

    -- BEGIN
    example : a = d := (hab.trans hcb.symm).trans hcd
    -- END

Reflexivity is more powerful than it looks. Recall that terms in the Calculus of Constructions have a computational interpretation, and that the logical framework treats terms with a common reduct as the same. As a result, some nontrivial identities can be proved by reflexivity:

.. code-block:: lean

    universe u
    variables (α β : Type u)

    example (f : α → β) (a : α) : (λ x, f x) a = f a := eq.refl _
    example (a : α) (b : α) : (a, b).1 = a := eq.refl _
    example : 2 + 3 = 5 := eq.refl _

This feature of the framework is so important that the library defines a notation ``rfl`` for ``eq.refl _``:

.. code-block:: lean

    universe u
    variables (α β : Type u)

    -- BEGIN
    example (f : α → β) (a : α) : (λ x, f x) a = f a := rfl
    example (a : α) (b : α) : (a, b).1 = a := rfl
    example : 2 + 3 = 5 := rfl
    -- END

Equality is much more than an equivalence relation, however. It has the important property that every assertion respects the equivalence, in the sense that we can substitute equal expressions without changing the truth value. That is, given ``h1 : a = b`` and ``h2 : p a``, we can construct a proof for ``p b`` using substitution: ``eq.subst h1 h2``.

.. code-block:: lean

    universe u

    example (α : Type u) (a b : α) (p : α → Prop) 
      (h1 : a = b) (h2 : p a) : p b :=
    eq.subst h1 h2

    example (α : Type u) (a b : α) (p : α → Prop) 
      (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2

The triangle in the second presentation is nothing more than notation for ``eq.subst``, and you can enter it by typing ``\t``.

The rule ``eq.subst`` is used to define the following auxiliary rules, which carry out more explicit substitutions. They are designed to deal with applicative terms, that is, terms of form ``s t``. Specifically, ``congr_arg`` can be used to replace the argument, ``congr_fun`` can be used to replace the term that is being applied, and ``congr`` can be used to replace both at once.

.. code-block:: lean

    variable α : Type
    variables a b : α
    variables f g : α → ℕ
    variable h₁ : a = b
    variable h₂ : f = g

    example : f a = f b := congr_arg f h₁
    example : f a = g a := congr_fun h₂ a
    example : f a = g b := congr h₂ h₁

Lean's library contains a large number of common identities, such as these:

.. code-block:: lean

    variables a b c d : ℤ

    example : a + 0 = a := add_zero a
    example : 0 + a = a := zero_add a
    example : a * 1 = a := mul_one a
    example : 1 * a = a := one_mul a
    example : -a + a = 0 := neg_add_self a
    example : a + -a = 0 := add_neg_self a
    example : a - a = 0 := sub_self a
    example : a + b = b + a := add_comm a b
    example : a + b + c = a + (b + c) := add_assoc a b c
    example : a * b = b * a := mul_comm a b
    example : a * b * c = a * (b * c) := mul_assoc a b c
    example : a * (b + c) = a * b + a * c := mul_add a b c
    example : a * (b + c) = a * b + a * c := left_distrib a b c
    example : (a + b) * c = a * c + b * c := add_mul a b c
    example : (a + b) * c = a * c + b * c := right_distrib a b c
    example : a * (b - c) = a * b - a * c := mul_sub a b c
    example : (a - b) * c = a * c - b * c := sub_mul a b c

Note that ``mul_add`` and ``add_mul`` are alternative names for ``left_distrib`` and ``right_distrib``, respectively. The properties above are stated for the integers; the type ``ℤ`` can be entered as ``\int``, though we can also use the ascii equivalent ``int``. Identities like these are designed to work in arbitrary instances of the relevant algebraic structures, using the type class mechanism that is described in :numref:`Chapter %s <type_classes>`. In particular, all these facts hold in any commutative ring, of which Lean recognizes the integers to be an instance. :numref:`Chapter %s <interacting_with_lean>` provides some pointers as to how to find theorems like this in the library.

Here is an example of a calculation in the natural numbers that uses substitution combined with associativity, commutativity, and distributivity of the integers.

.. code-block:: lean

    variables x y z : ℤ

    example (x y z : ℕ) : x * (y + z) = x * y + x * z := mul_add x y z
    example (x y z : ℕ) : (x + y) * z = x * z + y * z := add_mul x y z
    example (x y z : ℕ) : x + y + z = x + (y + z) := add_assoc x y z

    example (x y : ℕ) : 
      (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y, 
      from mul_add (x + y) x y,
    have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y),
      from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
    h2.trans (add_assoc (x * x + y * x) (x * y) (y * y)).symm

Notice that the second implicit parameter to ``eq.subst``, which provides the context in which the substitution is to occur, has type ``α → Prop``. Inferring this predicate therefore requires an instance of *higher-order unification*. In full generality, the problem of determining whether a higher-order unifier exists is undecidable, and Lean can at best provide imperfect and approximate solutions to the problem. As a result, ``eq.subst`` doesn't always do what you want it to. This issue is discussed in greater detail in :numref:`elaboration_hints`.

Because equational reasoning is so common and important, Lean provides a number of mechanisms to carry it out more effectively. The next section offers syntax that allow you to write calculational proofs in a more natural and perspicuous way. But, more importantly, equational reasoning is supported by a term rewriter, a simplifier, and other kinds of automation. The term rewriter and simplifier are described briefly in the next section, and then in greater detail in the next chapter.

.. _calculational_proofs:

Calculational Proofs
--------------------

A calculational proof is just a chain of intermediate results that are meant to be composed by basic principles such as the transitivity of equality. In Lean, a calculation proof starts with the keyword ``calc``, and has the following syntax:

.. code-block:: text

    calc
      <expr>_0  'op_1'  <expr>_1  ':'  <proof>_1
        '...'   'op_2'  <expr>_2  ':'  <proof>_2
         ...
        '...'   'op_n'  <expr>_n  ':'  <proof>_n

Each ``<proof>_i`` is a proof for ``<expr>_{i-1} op_i <expr>_i``.

Here is an example:

.. code-block:: lean

    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    theorem T : a = e :=
    calc
      a     = b      : h1
        ... = c + 1  : h2
        ... = d + 1  : congr_arg _ h3
        ... = 1 + d  : add_comm d (1 : ℕ)
        ... =  e     : eq.symm h4

The style of writing proofs is most effective when it is used in conjunction with the ``simp`` and ``rewrite`` tactics, which are discussed in greater detail in the next chapter. For example, using the abbreviation ``rw`` for rewrite, the proof above could be written as follows:

.. code-block:: lean

    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    include h1 h2 h3 h4
    theorem T : a = e :=
    calc
      a     = b      : by rw h1
        ... = c + 1  : by rw h2
        ... = d + 1  : by rw h3
        ... = 1 + d  : by rw add_comm
        ... =  e     : by rw h4

In the next chapter, we will see that hypotheses can be introduced, renamed, and modified by tactics, so it is not always clear what the names in ``rw h1`` refer to (though, in this case, it is). For that reason, section variables and variables that only appear in a tactic command or block are not automatically added to the context. The ``include`` command takes care of that. Essentially, the ``rewrite`` tactic uses a given equality (which can be a hypothesis, a theorem name, or a complex term) to "rewrite" the goal. If doing so reduces the goal to an identity ``t = t``, the tactic applies reflexivity to prove it.

Rewrites can be applied sequentially, so that the proof above can be shortened to this:

.. code-block:: lean

    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    include h1 h2 h3 h4
    -- BEGIN
    theorem T : a = e :=
    calc
      a     = d + 1  : by rw [h1, h2, h3]
        ... = 1 + d  : by rw add_comm
        ... =  e     : by rw h4
    -- END

Or even this:

.. code-block:: lean

    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    include h1 h2 h3 h4
    -- BEGIN
    theorem T : a = e :=
    by rw [h1, h2, h3, add_comm, h4]
    -- END

The ``simp`` tactic, instead, rewrites the goal by applying the given identities repeatedly, in any order, anywhere they are applicable in a term. It also uses other rules that have been previously declared to the system, and applies associativity and commutativity wisely to put expressions in canonical forms. As a result, we can also prove the theorem as follows:

.. code-block:: lean

    variables (a b c d e : ℕ)
    variable h1 : a = b
    variable h2 : b = c + 1
    variable h3 : c = d
    variable h4 : e = 1 + d

    include h1 h2 h3 h4
    -- BEGIN
    theorem T : a = e :=
    by simp [h1, h2, h3, h4]
    -- END

We will discuss variations of ``rw`` and ``simp`` in the next chapter.

The ``calc`` command can be configured for any relation that supports some form of transitivity. It can even combine different relations.

.. code-block:: lean

    theorem T2 (a b c d : ℕ)
      (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
    calc
      a     = b     : h1
        ... < b + 1 : nat.lt_succ_self b
        ... ≤ c + 1 : nat.succ_le_succ h2
        ... < d     : h3

With ``calc``, we can write the proof in the last section in a more natural and perspicuous way.

.. code-block:: lean

    example (x y : ℕ) : 
      (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
      (x + y) * (x + y) = (x + y) * x + (x + y) * y  : by rw mul_add
        ... = x * x + y * x + (x + y) * y            : by rw add_mul
        ... = x * x + y * x + (x * y + y * y)        : by rw add_mul
        ... = x * x + y * x + x * y + y * y          : by rw ←add_assoc

Here the left arrow before ``add_assoc`` tells rewrite to use the identity in the opposite direction. (You can enter it with ``\l`` or use the ascii equivalent, ``<-``.) If brevity is what we are after, both ``rw`` and ``simp`` can do the job on their own:

.. code-block:: lean

    example (x y : ℕ) : 
      (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by rw [mul_add, add_mul, add_mul, ←add_assoc]

    example (x y : ℕ) : 
      (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by simp [mul_add, add_mul]

.. _the_existential_quantifier:

The Existential Quantifier
--------------------------

Finally, consider the existential quantifier, which can be written as either ``exists x : α, p x`` or ``∃ x : α, p x``. Both versions are actually notationally convenient abbreviations for a more long-winded expression, ``Exists (λ x : α, p x)``, defined in Lean's library.

As you should by now expect, the library includes both an introduction rule and an elimination rule. The introduction rule is straightforward: to prove ``∃ x : α, p x``, it suffices to provide a suitable term ``t`` and a proof of ``p t``. here are some examples:

.. code-block:: lean

    open nat

    example : ∃ x : ℕ, x > 0 :=
    have h : 1 > 0, from zero_lt_succ 0,
    exists.intro 1 h

    example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
    exists.intro 0 h

    example (x y z : ℕ) (hxy : x < y) (hyz : y < z) : 
      ∃ w, x < w ∧ w < z :=
    exists.intro y (and.intro hxy hyz)

    #check @exists.intro

We can use the anonymous constructor notation ``⟨t, h⟩`` for ``exists.intro t h``, when the type is clear from the context.

.. code-block:: lean

    open nat

    -- BEGIN
    example : ∃ x : ℕ, x > 0 :=
    ⟨1, zero_lt_succ 0⟩

    example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
    ⟨0, h⟩

    example (x y z : ℕ) (hxy : x < y) (hyz : y < z) : 
      ∃ w, x < w ∧ w < z :=
    ⟨y, hxy, hyz⟩
    -- END

Note that ``exists.intro`` has implicit arguments: Lean has to infer the predicate ``p : α → Prop`` in the conclusion ``∃ x, p x``. This is not a trivial affair. For example, if we have have ``hg : g 0 0 = 0`` and write ``exists.intro 0 hg``, there are many possible values for the predicate ``p``, corresponding to the theorems ``∃ x, g x x = x``, ``∃ x, g x x = 0``, ``∃ x, g x 0 = x``, etc. Lean uses the context to infer which one is appropriate. This is illustrated in the following example, in which we set the option ``pp.implicit`` to true to ask Lean's pretty-printer to show the implicit arguments.

.. code-block:: lean

    variable g : ℕ → ℕ → ℕ
    variable hg : g 0 0 = 0

    theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
    theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
    theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
    theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

    set_option pp.implicit true  -- display implicit arguments
    #print gex1
    #print gex2
    #print gex3
    #print gex4

We can view ``exists.intro`` as an information-hiding operation, since it hides the witness to the body of the assertion. The existential elimination rule, ``exists.elim``, performs the opposite operation. It allows us to prove a proposition ``q`` from ``∃ x : α, p x``, by showing that ``q`` follows from ``p w`` for an arbitrary value ``w``. Roughly speaking, since we know there is an ``x`` satisfying ``p x``, we can give it a name, say, ``w``. If ``q`` does not mention ``w``, then showing that ``q`` follows from ``p w`` is tantamount to showing the ``q`` follows from the existence of any such ``x``. Here is an example:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    exists.elim h
      (assume w,
        assume hw : p w ∧ q w,
        show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

It may be helpful to compare the exists-elimination rule to the or-elimination rule: the assertion ``∃ x : α, p x`` can be thought of as a big disjunction of the propositions ``p a``, as ``a`` ranges over all the elements of ``α``. Note that the anonymous constructor notation ``⟨w, hw.right, hw.left⟩`` abbreviates a nested constructor application; we could equally well have written ``⟨w, ⟨hw.right, hw.left⟩⟩``.

Notice that an existential proposition is very similar to a sigma type, as described in :numref:`dependent_types`. The difference is that given ``a : α`` and ``h : p a``, the term ``exists.intro a h`` has type ``(∃ x : α, p x) : Prop`` and ``sigma.mk a h`` has type ``(Σ x : α, p x) : Type``. The similarity between ``∃`` and ``Σ`` is another instance of the Curry-Howard isomorphism.

Lean provides a more convenient way to eliminate from an existential quantifier with the ``match`` statement:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with ⟨w, hw⟩ :=
      ⟨w, hw.right, hw.left⟩
    end

The ``match`` statement is part of Lean's function definition system, which provides convenient and expressive ways of defining complex functions. Once again, it is the Curry-Howard isomorphism that allows us to co-opt this mechanism for writing proofs as well. The ``match`` statement "destructs" the existential assertion into the components ``w`` and ``hw``, which can then be used in the body of the statement to prove the proposition. We can annotate the types used in the match for greater clarity:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    -- BEGIN
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
      ⟨w, hw.right, hw.left⟩
    end
    -- END

We can even use the match statement to decompose the conjunction at the same time:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    -- BEGIN
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with ⟨w, hpw, hqw⟩ :=
      ⟨w, hqw, hpw⟩
    end
    -- END

Lean also provides a pattern-matching ``let`` expression:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    -- BEGIN
    example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩
    -- END

This is essentially just alternative notation for the ``match`` construct above. Lean will even allow us to use an implicit ``match`` in the ``assume`` statement:

.. code-block:: lean

    variables (α : Type) (p q : α → Prop)

    -- BEGIN
    example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩
    -- END

We will see in :numref:`Chapter %s <induction_and_recursion>` that all these variations are instances of a more general pattern-matching construct.

In the following example, we define ``even a`` as ``∃ b, a = 2*b``, and then we show that the sum of two even numbers is an even number.

.. code-block:: lean

    def is_even (a : nat) := ∃ b, a = 2 * b

    theorem even_plus_even {a b : nat} 
      (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
    exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
      exists.intro (w1 + w2)
        (calc
          a + b = 2 * w1 + 2 * w2  : by rw [hw1, hw2]
            ... = 2*(w1 + w2)      : by rw mul_add)))

Using the various gadgets described in this chapter --- the match statement, anonymous constructors, and the ``rewrite`` tactic, we can write this proof concisely as follows:

.. code-block:: lean

    def is_even (a : nat) := ∃ b, a = 2 * b

    -- BEGIN
    theorem even_plus_even {a b : nat} 
      (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
      ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
    end
    -- END

Just as the constructive "or" is stronger than the classical "or," so, too, is the constructive "exists" stronger than the classical "exists". For example, the following implication requires classical reasoning because, from a constructive standpoint, knowing that it is not the case that every ``x`` satisfies ``¬ p`` is not the same as having a particular ``x`` that satisfies ``p``.

.. code-block:: lean

    open classical

    variables (α : Type) (p : α → Prop)

    example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    by_contradiction
      (assume h1 : ¬ ∃ x, p x,
        have h2 : ∀ x, ¬ p x, from
          assume x,
          assume h3 : p x,
          have h4 : ∃ x, p x, from  ⟨x, h3⟩,
          show false, from h1 h4,
        show false, from h h2)

What follows are some common identities involving the existential quantifier. In the exercises below, we encourage you to prove as many as you can. We also leave it to you to determine which are nonconstructive, and hence require some form of classical reasoning.

.. code-block:: lean

    open classical

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    example : (∃ x : α, r) → r := sorry
    example : r → (∃ x : α, r) := sorry
    example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

    example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
    example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
    example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
    example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

    example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
    example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
    example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

Notice that the declaration ``variable a : α`` amounts to the assumption that there is at least one element of type ``α``. This assumption is needed in the second example, as well as in the last two.

Here are solutions to two of the more difficult ones:

.. code-block:: lean

    open classical

    variables (α : Type) (p q : α → Prop)
    variable a : α
    variable r : Prop

    -- BEGIN
    example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
      (assume ⟨a, (h1 : p a ∨ q a)⟩,
        or.elim h1
          (assume hpa : p a, or.inl ⟨a, hpa⟩)
          (assume hqa : q a, or.inr ⟨a, hqa⟩))
      (assume h : (∃ x, p x) ∨ (∃ x, q x),
        or.elim h
          (assume ⟨a, hpa⟩, ⟨a, (or.inl hpa)⟩)
          (assume ⟨a, hqa⟩, ⟨a, (or.inr hqa)⟩))

    example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
      (assume ⟨b, (hb : p b → r)⟩,
        assume h2 : ∀ x, p x,
        show r, from  hb (h2 b))
      (assume h1 : (∀ x, p x) → r,
        show ∃ x, p x → r, from
          by_cases
            (assume hap : ∀ x, p x, ⟨a, λ h', h1 hap⟩)
            (assume hnap : ¬ ∀ x, p x,
              by_contradiction
                (assume hnex : ¬ ∃ x, p x → r,
                  have hap : ∀ x, p x, from
                    assume x,
                    by_contradiction
                      (assume hnp : ¬ p x,
                        have hex : ∃ x, p x → r,
                          from ⟨x, (assume hp, absurd hp hnp)⟩,
                        show false, from hnex hex),
                  show false, from hnap hap)))
    -- END

More on the Proof Language
--------------------------

We have seen that keywords like ``assume``, ``have``, and ``show`` make it possible to write formal proof terms that mirror the structure of informal mathematical proofs. In this section, we discuss some additional features of the proof language that are often convenient.

To start with, we can use anonymous "have" expressions to introduce an auxiliary goal without having to label it. We can refer to the last expression introduced in this way using the keyword ``this``:

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans this (h 1),
    show f 0 ≤ f 3, from le_trans this (h 2)

Often proofs move from one fact to the next, so this can be effective in eliminating the clutter of lots of labels.

When the goal can be inferred, we can also ask Lean instead to fill in the proof by writing ``by assumption``:

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 0 ≤ f 2, from le_trans (by assumption) (h 1),
    show f 0 ≤ f 3, from le_trans (by assumption) (h 2)

This tells Lean to use the ``assumption`` tactic, which, in turn, proves the goal by finding a suitable hypothesis in the local context. We will learn more about the ``assumption`` tactic in the next chapter.

We can also ask Lean to fill in the proof by writing ``‹p›``, where ``p`` is the proposition whose proof we want Lean to find in the context.

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    -- BEGIN
    example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    assume : f 0 ≥ f 1,
    assume : f 1 ≥ f 2,
    have f 0 ≥ f 2, from le_trans this ‹f 0 ≥ f 1›,
    have f 0 ≤ f 2, from le_trans (h 0) (h 1),
    show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›
    -- END

You can type these corner quotes using ``\f<`` and ``\f>``, respectively. The letter "f" is for "French," since the unicode symbols can also be used as French quotation marks. In fact, the notation is defined in Lean as follows:

.. code-block:: lean

    notation `‹` p `›` := show p, by assumption

This approach is more robust than using ``by assumption``, because the type of the assumption that needs to be inferred is given explicitly. It also makes proofs more readable. Here is a more elaborate example:

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    -- BEGIN
    example : f 0 ≤ f 3 :=
    have f 0 ≤ f 1, from h 0,
    have f 1 ≤ f 2, from h 1,
    have f 2 ≤ f 3, from h 2,
    show f 0 ≤ f 3, from le_trans ‹f 0 ≤ f 1›
                           (le_trans ‹f 1 ≤ f 2› ‹f 2 ≤ f 3›)
    -- END

Keep in mind that you can use the French quotation marks in this way to refer to *anything* in the context, not just things that were introduced anonymously. Its use is also not limited to propositions, though using it for data is somewhat odd:

.. code-block:: lean

    example (n : ℕ) : ℕ := ‹ℕ›

We can also ``assume`` a hypothesis without giving it a label:

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    -- BEGIN
    example : f 0 ≥ f 1 → f 0 = f 1 :=
    assume : f 0 ≥ f 1,
    show f 0 = f 1, from le_antisymm (h 0) this
    -- END

In contrast to the usage with ``have``, an anonymous ``assume`` needs an extra colon. The reason is that Lean allows us to write ``assume h`` to introduce a hypothesis without specifying it, and without the colon it would be ambiguous as to whether the ``h`` here is meant as the label or the assumption.

As with the anonymous ``have``, when you use an anonymous ``assume`` to introduce an assumption, that assumption can also be invoked later in the proof by enclosing it in French quotes.

.. code-block:: lean

    variable f : ℕ → ℕ
    variable h : ∀ x : ℕ, f x ≤ f (x + 1)

    -- BEGIN
    example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
    assume : f 0 ≥ f 1,
    assume : f 1 ≥ f 2,
    have f 0 ≥ f 2, from le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›,
    have f 0 ≤ f 2, from le_trans (h 0) (h 1),
    show f 0 = f 2, from le_antisymm this ‹f 0 ≥ f 2›
    -- END

Notice that ``le_antisymm`` is the assertion that if ``a ≤ b`` and ``b ≤ a`` then ``a = b``, and ``a ≥ b`` is definitionally equal to ``b ≤ a``.

Exercises
---------

#. Prove these equivalences:

   .. code-block:: lean

       variables (α : Type) (p q : α → Prop)

       example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
       example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
       example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

   You should also try to understand why the reverse implication is not derivable in the last example.

#. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):

   .. code-block:: lean

       variables (α : Type) (p q : α → Prop)
       variable r : Prop

       example : α → ((∀ x : α, r) ↔ r) := sorry
       example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
       example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

#. Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:

   .. code-block:: lean

       variables (men : Type) (barber : men) 
       variable  (shaves : men → men → Prop)

       example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : 
         false := sorry

#. Below, we have put definitions of ``divides`` and ``even`` in a special namespace to avoid conflicts with definitions in the library. The ``instance`` declaration makes it possible to use the notation ``m | n`` for ``divides m n``. Don't worry about how it works; you will learn about that later.

   .. code-block:: lean

       namespace hidden

       def divides (m n : ℕ) : Prop := ∃ k, m * k = n

       instance : has_dvd nat := ⟨divides⟩

       def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

       section
         variables m n : ℕ

         #check m ∣ n
         #check m^n
         #check even (m^n +3)
       end

       end hidden

   Remember that, without any parameters, an expression of type ``Prop`` is just an assertion. Fill in the definitions of ``prime`` and ``Fermat_prime`` below, and construct the given assertion. For example, you can say that there are infinitely many primes by asserting that for every natural number ``n``, there is a prime number greater than ``n``. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.

   .. code-block:: lean

       namespace hidden

       def divides (m n : ℕ) : Prop := ∃ k, m * k = n

       instance : has_dvd nat := ⟨divides⟩

       def even (n : ℕ) : Prop := 2 ∣ n

       -- BEGIN
       def prime (n : ℕ) : Prop := sorry

       def infinitely_many_primes : Prop := sorry

       def Fermat_prime (n : ℕ) : Prop := sorry

       def infinitely_many_Fermat_primes : Prop := sorry

       def goldbach_conjecture : Prop := sorry

       def Goldbach's_weak_conjecture : Prop := sorry

       def Fermat's_last_theorem : Prop := sorry
       -- END

       end hidden

#. Prove as many of the identities listed in :numref:`the_existential_quantifier` as you can.

#. Give a calculational proof of the theorem ``log_mul`` below.

   .. code-block:: lean

       variables (real : Type) [ordered_ring real]
       variables (log exp : real → real)
       variable  log_exp_eq : ∀ x, log (exp x) = x
       variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
       variable  exp_pos    : ∀ x, exp x > 0
       variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

       -- this ensures the assumptions are available in tactic proofs
       include log_exp_eq exp_log_eq exp_pos exp_add

       example (x y z : real) : 
         exp (x + y + z) = exp x * exp y * exp z :=
       by rw [exp_add, exp_add]

       example (y : real) (h : y > 0)  : exp (log y) = y := 
       exp_log_eq h

       theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) : 
         log (x * y) = log x + log y :=
       sorry

#. Prove the theorem below, using only the ring properties of ``ℤ`` enumerated in :numref:`equality` and the theorem ``sub_self``.

   .. code-block:: lean

       #check sub_self

       example (x : ℤ) : x * 0 = 0 :=
       sorry
