.. _axioms_and_computation:

Axioms and Computation
======================

We have seen that the version of the Calculus of Constructions that has been implemented in Lean includes dependent function types, inductive types, and a hierarchy of universes that starts with an impredicative, proof-irrelevant ``Prop`` at the bottom. In this chapter, we consider ways of extending the CIC with additional axioms and rules. Extending a foundational system in such a way is often convenient; it can make it possible to prove more theorems, as well as make it easier to prove theorems that could have been proved otherwise. But there can be negative consequences of adding additional axioms, consequences which may go beyond concerns about their correctness. In particular, the use of axioms bears on the computational content of definitions and theorems, in ways we will explore here.

Lean is designed to support both computational and classical reasoning. Users that are so inclined can stick to a "computationally pure" fragment, which guarantees that closed expressions in the system evaluate to canonical normal forms. In particular, any closed computationally pure expression of type ``ℕ``, for example, will reduce to a numeral.

Lean's standard library defines an additional axiom, propositional extensionality, and a quotient construction which in turn implies the principle of function extensionality. These extensions are used, for example, to develop theories of sets and finite sets. We will see below that using these theorems can block evaluation in Lean's kernel, so that closed terms of type ``ℕ`` no longer evaluate to numerals. But Lean erases types and propositional information when compiling definitions to bytecode for its virtual machine evaluator, and since these axioms only add new propositions, they are compatible with that computational interpretation. Even computationally inclined users may wish to use the classical law of the excluded middle to reason about computation. This also blocks evaluation in the kernel, but it is compatible with compilation to bytecode.

The standard library also defines a choice principle that is entirely antithetical to a computational interpretation, since it magically produces "data" from a proposition asserting its existence. Its use is essential to some classical constructions, and users can import it when needed. But expressions that use this construction to produce data do not have computational content, and in Lean we are required to mark such definitions as ``noncomputable`` to flag that fact.

Using a clever trick (known as Diaconescu's theorem), one can use propositional extensionality, function extensionality, and choice to derive the law of the excluded middle. As noted above, however, use of the law of the excluded middle is still compatible with bytecode compilation and code extraction, as are other classical principles, as long as they are not used to manufacture data.

To summarize, then, on top of the underlying framework of universes, dependent function types, and inductive types, the standard library adds three additional components:

-  the axiom of propositional extensionality
-  a quotient construction, which implies function extensionality
-  a choice principle, which produces data from an existential proposition.

The first two of these block normalization within Lean, but are compatible with bytecode evaluation, whereas the third is not amenable to computational interpretation. We will spell out the details more precisely below.

Historical and Philosophical Context
------------------------------------

For most of its history, mathematics was essentially computational: geometry dealt with constructions of geometric objects, algebra was concerned with algorithmic solutions to systems of equations, and analysis provided means to compute the future behavior of systems evolving over time. From the proof of a theorem to the effect that "for every ``x``, there is a ``y`` such that ...", it was generally straightforward to extract an algorithm to compute such a ``y`` given ``x``.

In the nineteenth century, however, increases in the complexity of mathematical arguments pushed mathematicians to develop new styles of reasoning that suppress algorithmic information and invoke descriptions of mathematical objects that abstract away the details of how those objects are represented. The goal was to obtain a powerful "conceptual" understanding without getting bogged down in computational details, but this had the effect of admitting mathematical theorems that are simply *false* on a direct computational reading.

There is still fairly uniform agreement today that computation is important to mathematics. But there are different views as to how best to address computational concerns. From a *constructive* point of view, it is a mistake to separate mathematics from its computational roots; every meaningful mathematical theorem should have a direct computational interpretation. From a *classical* point of view, it is more fruitful to maintain a separation of concerns: we can use one language and body of methods to write computer programs, while maintaining the freedom to use a nonconstructive theories and methods to reason about them. Lean is designed to support both of these approaches. Core parts of the library are developed constructively, but the system also provides support for carrying out classical mathematical reasoning.

Computationally, the purest part of dependent type theory avoids the use of ``Prop`` entirely. Inductive types and dependent function types can be viewed as data types, and terms of these types can be "evaluated" by applying reduction rules until no more rules can be applied. In principle, any closed term (that is, term with no free variables) of type ``ℕ`` should evaluate to a numeral, ``succ (... (succ zero)...)``.

Introducing a proof-irrelevant ``Prop`` and marking theorems irreducible represents a first step towards separation of concerns. The intention is that elements of a type ``p : Prop`` should play no role in computation, and so the particular construction of a term ``t : p`` is "irrelevant" in that sense. One can still define computational objects that incorporate elements of type ``Prop``; the point is that these elements can help us reason about the effects of the computation, but can be ignored when we extract "code" from the term. Elements of type ``Prop`` are not entirely innocuous, however. They include equations ``s = t : α`` for any type ``α``, and such equations can be used as casts, to type check terms. Below, we will see examples of how such casts can block computation in the system. However, computation is still possible under an evaluation scheme that erases propositional content, ignores intermediate typing constraints, and reduces terms until they reach a normal form. This is precisely what Lean's virtual machine does.

Having adopted a proof-irrelevant ``Prop``, one might consider it legitimate to use, for example, the law of the excluded middle, ``p ∨ ¬p``, where ``p`` is any proposition. Of course, this, too, can block computation according to the rules of CIC, but it does not block bytecode evaluation, as described above. It is only the choice principles discussed in :numref:`choice` that completely erase the distinction between the proof-irrelevant and data-relevant parts of the theory.

Propositional Extensionality
----------------------------

Propositional extensionality is the following axiom:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    axiom propext {a b : Prop} : (a ↔ b) → a = b
    -- END

    end hidden

It asserts that when two propositions imply one another, they are actually equal. This is consistent with set-theoretic interpretations in which any element ``a : Prop`` is either empty or the singleton set ``{*}``, for some distinguished element ``*``. The axiom has the effect that equivalent propositions can be substituted for one another in any context:

.. code-block:: lean

    section
      variables a b c d e : Prop
      variable p : Prop → Prop

      theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
      propext h ▸ iff.refl _

      theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
      propext h ▸ h₁
    end

The first example could be proved more laboriously without ``propext`` using the fact that the propositional connectives respect propositional equivalence. The second example represents a more essential use of ``propext``. In fact, it is equivalent to ``propext`` itself, a fact which we encourage you to prove.

Given any definition or theorem in Lean, you can use the ``#print axioms`` command to display the axioms it depends on.

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

Function Extensionality
-----------------------

Similar to propositional extensionality, function extensionality asserts that any two functions of type ``Π x : α, β x`` that agree on all their inputs are equal.

.. code-block:: lean

    universes u₁ u₂

    #check (@funext : ∀ {α : Type u₁} {β : α → Type u₂} 
               {f₁ f₂ : Π (x : α), β x},
             (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂)

From a classical, set-theoretic perspective, this is exactly what it means for two functions to be equal. This is known as an "extensional" view of functions. From a constructive perspective, however, it is sometimes more natural to think of functions as algorithms, or computer programs, that are presented in some explicit way. It is certainly the case that two computer programs can compute the same answer for every input despite the fact that they are syntactically quite different. In much the same way, you might want to maintain a view of functions that does not force you to identify two functions that have the same input / output behavior. This is known as an "intensional" view of functions.

In fact, function extensionality follows from the existence of quotients, which we describe in the next section. In the Lean standard library, therefore, ``funext`` is thus `proved from the quotient construction <https://github.com/leanprover/lean/blob/master/library/init/funext.lean>`__.

Suppose that for ``α : Type`` we define the ``set α := α → Prop`` to denote the type of subsets of ``α``, essentially identifying subsets with predicates. By combining ``funext`` and ``propext``, we obtain an extensional theory of such sets:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    universe u

    def set (α : Type u) := α → Prop

    namespace set

    variable {α : Type u}

    definition mem (x : α) (a : set α) := a x
    notation e ∈ a := mem e a 

    theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
    funext (assume x, propext (h x))

    end set
    -- END
    end hidden

We can then proceed to define the empty set and set intersection, for example, and prove set identities:

.. code-block:: lean

    namespace hidden

    universe u

    definition set (α : Type u) := α → Prop

    namespace set

    variable {α : Type u}

    def mem (x : α) (a : set α) := a x

    instance has_mem_set (α : Type u) : has_mem α (set α) := ⟨mem⟩

    theorem setext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
    funext (assume x, propext (h x))

    -- BEGIN
    definition empty : set α := λ x, false
    local notation `∅` := empty

    definition inter (a b : set α) : set α := λ x, x ∈ a ∧ x ∈ b
    notation a ∩ b := inter a b

    theorem inter_self (a : set α) : a ∩ a = a :=
    setext (assume x, and_self _)

    theorem inter_empty (a : set α) : a ∩ ∅ = ∅ :=
    setext (assume x, and_false _)

    theorem empty_inter (a : set α) : ∅ ∩ a = ∅ :=
    setext (assume x, false_and _)

    theorem inter.comm (a b : set α) : a ∩ b = b ∩ a :=
    setext (assume x, and_comm _ _)
    -- END

    end set
    end hidden

The following is an example of how function extensionality blocks computation inside the Lean kernel.

.. code-block:: lean

    def f₁  (x : ℕ) := x
    def f₂ (x : ℕ) := 0 + x

    theorem feq : f₁ = f₂ := funext (assume x, (zero_add x).symm)

    def val : ℕ := eq.rec_on feq (0 : ℕ)

    -- complicated!
    #reduce val

    -- evaluates to 0
    #eval val

First, we show that the two functions ``f₁`` and ``f₂`` are equal using function extensionality, and then we cast ``0`` of type ``ℕ`` by replacing ``f₁`` by ``f₂`` in the type. Of course, the cast is vacuous, because ``ℕ`` does not depend on ``f₁``. But that is enough to do the damage: under the computational rules of the system, we now have a closed term of ``ℕ`` that does not reduce to a numeral. In this case, we may be tempted to reduce the expression to ``0``. But in nontrivial examples, eliminating cast changes the type of the term, which might make an ambient expression type incorrect. The virtual machine, however, has no trouble evaluating the expression to ``0``. Here is a similarly contrived example that shows how ``propext`` can get in the way.

.. code-block:: lean

    theorem tteq : (true ∧ true) = true := propext (and_true true)

    def val : ℕ := eq.rec_on tteq 0

    -- complicated!
    #reduce val

    -- evaluates to 0
    #eval val

Current research programs, including work on *observational type theory* and *cubical type theory*, aim to extend type theory in ways that permit reductions for casts involving function extensionality, quotients, and more. But the solutions are not so clear cut, and the rules of Lean's underlying calculus do not sanction such reductions.

In a sense, however, a cast does not change the meaning of an expression. Rather, it is a mechanism to reason about the expression's type. Given an appropriate semantics, it then makes sense to reduce terms in ways that preserve their meaning, ignoring the intermediate bookkeeping needed to make the reductions type correct. In that case, adding new axioms in ``Prop`` does not matter; by proof irrelevance, an expression in ``Prop`` carries no information, and can be safely ignored by the reduction procedures.

Quotients
---------

Let ``α`` be any type, and let ``r`` be an equivalence relation on ``α``. It is mathematically common to form the "quotient" ``α / r``, that is, the type of elements of ``α`` "modulo" ``r``. Set theoretically, one can view ``α / r`` as the set of equivalence classes of ``α`` modulo ``r``. If ``f : α → β`` is any function that respects the equivalence relation in the sense that for every ``x y : α``, ``r x y`` implies ``f x = f y``, then ``f`` "lifts" to a function ``f' : α / r → β`` defined on each equivalence class ``⟦x⟧`` by ``f' ⟦x⟧ = f x``. Lean's standard library extends the Calculus of Constructions with additional constants that perform exactly these constructions, and installs this last equation as a definitional reduction rule.

In its most basic form, the quotient construction does not even require ``r`` to be an equivalence relation. The following constants are built into Lean:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    universes u v

    constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
    
    constant quot.mk : 
      Π {α : Sort u} (r : α → α → Prop), α → quot r

    axiom quot.ind : 
      ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
        (∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

    constant quot.lift : 
      Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
        (∀ a b, r a b → f a = f b) → quot r → β

    -- END
    end hidden

The first one forms a type ``quot r`` given a type ``α`` by any binary relation ``r`` on ``α``. The second maps ``α`` to ``quot α``, so that if ``r : α → α → Prop`` and ``a : α``, then ``quot.mk r a`` is an element of ``quot r``. The third principle, ``quot.ind``, says that every element of ``quot.mk r a`` is of this form.  As for ``quot.lift``, given a function ``f : α → β``, if ``h`` is a proof that ``f`` respects the relation ``r``, then ``quot.lift f h`` is the corresponding function on ``quot r``. The idea is that for each element ``a`` in ``α``, the function ``quot.lift f h`` maps ``quot.mk r a`` (the ``r``-class containing ``a``) to ``f a``, wherein ``h`` shows that this function is well defined. In fact, the computation principle is declared as a reduction rule, as the proof below makes clear.

.. code-block:: lean

    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α

    -- the quotient type
    #check (quot r : Type)

    -- the class of a
    #check (quot.mk r a : quot r)

    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂ 

    -- the corresponding function on quot r
    #check (quot.lift f h : quot r → β)

    -- the computation principle
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

The four constants, ``quot``, ``quot.mk``, ``quot.ind``, and ``quot.lift`` in and of themselves are not very strong. You can check that the ``quot.ind`` is satisfied if we take ``quot r`` to be simply ``α``, and take ``quot.lift`` to be the identity function (ignoring ``h``). For that reason, these four constants are not viewed as additional axioms:

.. code-block:: lean

    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂ 
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

    -- BEGIN
    #print axioms thm   -- no axioms
    -- END

They are, like inductively defined types and the associated constructors and recursors, viewed as part of the logical framework.

What makes the ``quot`` construction into a bona fide quotient is the following additional axiom:

.. code-block:: lean

    namespace hidden
    universe u

    -- BEGIN
    axiom quot.sound : 
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → quot.mk r a = quot.mk r b
    -- END
    end hidden

This is the axiom that asserts that any two elements of ``α`` that are related by ``r`` become identified in the quotient. If a theorem or definition makes use of ``quot.sound``, it will show up in the ``#print axioms`` command.

Of course, the quotient construction is most commonly used in situations when ``r`` is an equivalence relation. Given ``r`` as above, if we define ``r'`` according to the rule ``r' a b`` iff ``quot.mk r a = quot.mk r b``, then it's clear that ``r'`` is an equivalence relation. Indeed, ``r'`` is the *kernel* of the function ``a ↦ quot.mk r a``.  The axiom ``quot.sound`` says that ``r a b`` implies ``r' a b``. Using ``quot.lift`` and ``quot.ind``, we can show that ``r'`` is the smallest equivalence relation containing ``r``, in the sense that if ``r''`` is any equivalence relation containing ``r``, then ``r' a b`` implies ``r'' a b``. In particular, if ``r`` was an equivalence relation to start with, then for all ``a`` and ``b`` we have ``r a b`` iff ``r' a b``.

To support this common use case, the standard library defines the notion of a *setoid*, which is simply a type with an associated equivalence relation:

.. code-block:: lean

    universe u
    namespace hidden

    -- BEGIN
    class setoid (α : Type u) :=
    (r : α → α → Prop) (iseqv : equivalence r)

    namespace setoid
      infix `≈` := setoid.r

      variable {α : Type u}
      variable [s : setoid α]
      include s

      theorem refl (a : α) : a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b : α} : a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
    -- END

    end hidden

Given a type ``α``, a relation ``r`` on ``α``, and a proof ``p`` that ``r`` is an equivalence relation, we can define ``setoid.mk p`` as an instance of the setoid class.

.. code-block:: lean

    universe u
    namespace hidden

    -- BEGIN
    def quotient {α : Type u} (s : setoid α) :=
    @quot α setoid.r
    -- END

    end hidden

The constants ``quotient.mk``, ``quotient.ind``, ``quotient.lift``, and ``quotient.sound`` are nothing more than the specializations of the corresponding elements of ``quot``. The fact that type class inference can find the setoid associated to a type ``α`` brings a number of benefits. First, we can use the notation ``a ≈ b`` (entered with ``\approx``) for ``setoid.r a b``, where the instance of ``setoid`` is implicit in the notation ``setoid.r``. We can use the generic theorems ``setoid.refl``, ``setoid.symm``, ``setoid.trans`` to reason about the relation. Specifically with quotients we can use the generic notation ``⟦a⟧`` for ``quot.mk setoid.r`` where the instance of ``setoid`` is implicit in the notation ``setoid.r``, as well as the theorem ``quotient.exact``:

.. code-block:: lean

    universe u

    -- BEGIN
    #check (@quotient.exact : 
      ∀ {α : Type u} [setoid α] {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈ b)
    -- END

Together with ``quotient.sound``, this implies that the elements of the quotient correspond exactly to the equivalence classes of elements in ``α``.

Recall that in the standard library, ``α × β`` represents the Cartesian product of the types ``α`` and ``β``. To illustrate the use of quotients, let us define the type of *unordered* pairs of elements of a type ``α`` as a quotient of the type ``α × α``. First, we define the relevant equivalence relation:

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    infix `~` := eqv

The next step is to prove that ``eqv`` is in fact an equivalence relation, which is to say, it is reflexive, symmetric and transitive. We can prove these three facts in a convenient and readable way by using dependent pattern matching to perform case-analysis and break the hypotheses into pieces that are then reassembled to produce the conclusion.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    -- BEGIN
    open or

    private theorem eqv.refl {α : Type u} : 
      ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : 
      ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := 
        inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := 
        inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : 
      ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) 
        (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : 
      equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) 
      (@eqv.trans α)
    -- END

We open the namespaces ``or`` and ``eq`` to be able to use ``or.inl``, ``or.inr``, and ``eq.trans`` more conveniently.

Now that we have proved that ``eqv`` is an equivalence relation, we can construct a ``setoid (α × α)``, and use it to define the type ``uprod α`` of unordered pairs.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    -- BEGIN
    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂ 
    end uprod
    -- END

Notice that we locally define the notation ``{a₁, a₂}`` for ordered pairs as ``⟦(a₁, a₂)⟧``. This is useful for illustrative purposes, but it is not a good idea in general, since the notation will shadow other uses of curly brackets, such as for records and sets.

We can easily prove that ``{a₁, a₂} = {a₂, a₁}`` using ``quot.sound``, since we have ``(a₁, a₂) ~ (a₂, a₁)``.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂  

    -- BEGIN
      theorem mk_eq_mk {α : Type} (a₁ a₂ : α) : 
        {a₁, a₂} = {a₂, a₁} :=
      quot.sound (inr ⟨rfl, rfl⟩)
    -- END
    end uprod

To complete the example, given ``a : α`` and ``u : uprod α``, we define the proposition ``a ∈ u`` which should hold if ``a`` is one of the elements of the unordered pair ``u``. First, we define a similar proposition ``mem_fn a u`` on (ordered) pairs; then we show that ``mem_fn`` respects the equivalence relation ``eqv`` with the lemma ``mem_respects``. This is an idiom that is used extensively in the Lean standard library.

.. code-block:: lean

    universe u

    private definition eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
    (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

    local infix `~` := eqv

    open or

    private theorem eqv.refl {α : Type u} : ∀ p : α × α, p ~ p :=
    assume p, inl ⟨rfl, rfl⟩

    private theorem eqv.symm {α : Type u} : ∀ p₁ p₂ : α × α, p₁ ~ p₂ → p₂ ~ p₁
    | (a₁, a₂) (b₁, b₂) (inl ⟨a₁b₁, a₂b₂⟩) := inl ⟨symm a₁b₁, symm a₂b₂⟩
    | (a₁, a₂) (b₁, b₂) (inr ⟨a₁b₂, a₂b₁⟩) := inr ⟨symm a₂b₁, symm a₁b₂⟩

    private theorem eqv.trans {α : Type u} : ∀ p₁ p₂ p₃ : α × α, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inl ⟨trans a₁b₁ b₁c₁, trans a₂b₂ b₂c₂⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inl ⟨a₁b₁, a₂b₂⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inr ⟨trans a₁b₁ b₁c₂, trans a₂b₂ b₂c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inl ⟨b₁c₁, b₂c₂⟩) :=
      inr ⟨trans a₁b₂ b₂c₂, trans a₂b₁ b₁c₁⟩
    | (a₁, a₂) (b₁, b₂) (c₁, c₂) (inr ⟨a₁b₂, a₂b₁⟩) (inr ⟨b₁c₂, b₂c₁⟩) :=
      inl ⟨trans a₁b₂ b₂c₁, trans a₂b₁ b₁c₂⟩

    private theorem is_equivalence (α : Type u) : equivalence (@eqv α) :=
    mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α)

    instance uprod.setoid (α : Type u) : setoid (α × α) :=
    setoid.mk (@eqv α) (is_equivalence α)

    definition uprod (α : Type u) : Type u :=
    quotient (uprod.setoid α)

    namespace uprod
      definition mk {α : Type u} (a₁ a₂ : α) : uprod α :=
      ⟦(a₁, a₂)⟧

      local notation `{` a₁ `,` a₂ `}` := mk a₁ a₂  

      theorem mk_eq_mk {α : Type} (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
      quot.sound (inr ⟨rfl, rfl⟩)

    -- BEGIN
      private definition mem_fn {α : Type} (a : α) : 
        α × α → Prop
      | (a₁, a₂) := a = a₁ ∨ a = a₂

      -- auxiliary lemma for proving mem_respects
      private lemma mem_swap {α : Type} {a : α} : 
        ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
      | (a₁, a₂) := propext (iff.intro
          (λ l : a = a₁ ∨ a = a₂, 
            or.elim l (λ h₁, inr h₁) (λ h₂, inl h₂))
          (λ r : a = a₂ ∨ a = a₁, 
            or.elim r (λ h₁, inr h₁) (λ h₂, inl h₂)))

      private lemma mem_respects {α : Type} : 
        ∀ {p₁ p₂ : α × α} (a : α), 
          p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
      | (a₁, a₂) (b₁, b₂) a (inl ⟨a₁b₁, a₂b₂⟩) :=
        by { dsimp at a₁b₁, dsimp at a₂b₂, rw [a₁b₁, a₂b₂] }
      | (a₁, a₂) (b₁, b₂) a (inr ⟨a₁b₂, a₂b₁⟩) :=
        by { dsimp at a₁b₂, dsimp at a₂b₁, rw [a₁b₂, a₂b₁], 
              apply mem_swap }

      def mem {α : Type} (a : α) (u : uprod α) : Prop :=
      quot.lift_on u (λ p, mem_fn a p) (λ p₁ p₂ e, mem_respects a e)

      local infix `∈` := mem

      theorem mem_mk_left {α : Type} (a b : α) : a ∈ {a, b} :=
      inl rfl

      theorem mem_mk_right {α : Type} (a b : α) : b ∈ {a, b} :=
      inr rfl

      theorem mem_or_mem_of_mem_mk {α : Type} {a b c : α} : 
        c ∈ {a, b} → c = a ∨ c = b :=
      λ h, h
    -- END
    end uprod

For convenience, the standard library also defines ``quotient.lift₂`` for lifting binary functions, and ``quotient.ind₂`` for induction on two variables.

We close this section with some hints as to why the quotient construction implies function extenionality. It is not hard to show that extensional equality on the ``Π x : α, β x`` is an equivalence relation, and so we can consider the type ``extfun α β`` of functions "up to equivalence." Of course, application respects that equivalence in the sense that if ``f₁`` is equivalent to ``f₂``, then ``f₁ a`` is equal to ``f₂ a``. Thus application gives rise to a function ``extfun_app : extfun α β → Π x : α, β x``. But for every ``f``, ``extfun_app ⟦f⟧`` is definitionally equal to ``λ x, f x``, which is in turn definitionally equal to ``f``. So, when ``f₁`` and ``f₂`` are extensionally equal, we have the following chain of equalities:

.. code-block:: text

    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂

As a result, ``f₁`` is equal to ``f₂``.

.. _choice:

Choice
------

To state the final axiom defined in the standard library, we need the ``nonempty`` type, which is defined as follows:

.. code-block:: lean

    universe u
    namespace hidden

    -- BEGIN
    class inductive nonempty (α : Sort u) : Prop
    | intro : α → nonempty
    -- END

    end hidden

Because ``nonempty α`` has type ``Prop`` and its constructor contains data, it can only eliminate to ``Prop``. In fact, ``nonempty α`` is equivalent to ``∃ x : α, true``:

.. code-block:: lean

    universe u

    -- BEGIN
    example (α : Type u) : nonempty α ↔ ∃ x : α, true :=
    iff.intro (λ ⟨a⟩, ⟨a, trivial⟩) (λ ⟨a, h⟩, ⟨a⟩)
    -- END

Our axiom of choice is now expressed simply as follows:

.. code-block:: lean

    namespace hidden
    universe u

    -- BEGIN
    axiom choice {α : Sort u} : nonempty α → α
    -- END

    end hidden

Given only the assertion ``h`` that ``α`` is nonempty, ``choice h`` magically produces an element of ``α``. Of course, this blocks any meaningful computation: by the interpretation of ``Prop``, ``h`` contains no information at all as to how to find such an element.

This is found in the ``classical`` namespace, so the full name of the theorem is ``classical.choice``. The choice principle is equivalent to the principle of *indefinite description*, which can be expressed with subtypes as follows:

.. code-block:: lean

    namespace hidden
    universe u

    axiom choice {α : Sort u} : nonempty α → α
    -- BEGIN
    noncomputable theorem indefinite_description 
        {α : Sort u} (p : α → Prop) : 
      (∃ x, p x) → {x // p x} :=
    λ h, choice (let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩)
    -- END

    end hidden

Because it depends on ``choice``, Lean cannot generate bytecode for ``indefinite_description``, and so requires us to mark the definition as ``noncomputable``. Also in the ``classical`` namespace, the function ``some`` and the property ``some_spec`` decompose the two parts of the output of ``indefinite_description``:

.. code-block:: lean

    open classical
    namespace hidden
    universe u

    -- BEGIN
    noncomputable def some {a : Sort u} {p : a → Prop} 
      (h : ∃ x, p x) : a :=
    subtype.val (indefinite_description p h)

    theorem some_spec {a : Sort u} {p : a → Prop} 
      (h : ∃ x, p x) : p (some h) :=
    subtype.property (indefinite_description p h)
    -- END

    end hidden

The ``choice`` principle also erases the distinction between the property of being ``nonempty`` and the more constructive property of being ``inhabited``:

.. code-block:: lean

    universe u
    open classical

    -- BEGIN
    noncomputable theorem inhabited_of_nonempty {α : Type u} : 
      nonempty α → inhabited α :=
    λ h, choice (let ⟨a⟩ := h in ⟨⟨a⟩⟩)
    -- END

In the next section, we will see that ``propext``, ``funext``, and ``choice``, taken together, imply the law of the excluded middle and the decidability of all propositions. Using those, one can strengthen the principle of indefinite description as follows:

.. code-block:: lean

    universe u
    open classical

    -- BEGIN
    #check (@strong_indefinite_description :
            Π {α : Sort u} (p : α → Prop), 
              nonempty α → {x // (∃ (y : α), p y) → p x})
    -- END

Assuming the ambient type ``α`` is nonempty, ``strong_indefinite_description p`` produces an element of ``α`` satisfying ``p`` if there is one. The data component of this definition is conventionally known as *Hilbert's epsilon function*:

.. code-block:: lean

    universe u
    open classical

    -- BEGIN
    #check (@epsilon : Π {α : Sort u} [nonempty α], 
                         (α → Prop) → α)

    #check (@epsilon_spec : ∀ {a : Sort u} {p : a → Prop} 
               (hex : ∃ (y : a), p y), 
             p (@epsilon _ (nonempty_of_exists hex) p))
    -- END

The Law of the Excluded Middle
------------------------------

The law of the excluded middle is the following

.. code-block:: lean

    open classical
    namespace hidden
    -- BEGIN
    #check (@em : ∀ (p : Prop), p ∨ ¬p)
    -- END
    end hidden

`Diaconescu's theorem <http://en.wikipedia.org/wiki/Diaconescu%27s_theorem>`__ states that the axiom of choice is sufficient to derive the law of excluded middle. More precisely, it shows that the law of the excluded middle follows from ``classical.choice``, ``propext``, and ``funext``. We sketch the proof that is found in the standard library.

First, we import the necessary axioms, fix a parameter, ``p``, and define two predicates ``U`` and ``V``:

.. code-block:: lean

    open classical

    section diaconescu
    parameter  p : Prop

    def U (x : Prop) : Prop := x = true ∨ p
    def V (x : Prop) : Prop := x = false ∨ p

    lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
    lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

    end diaconescu

If ``p`` is true, then every element of ``Prop`` is in both ``U`` and ``V``. If ``p`` is false, then ``U`` is the singleton ``true``, and ``V`` is the singleton ``false``.

Next, we use ``some`` to choose an element from each of ``U`` and ``V``:

.. code-block:: lean

    open classical

    section diaconescu
    parameter  p : Prop

    def U (x : Prop) : Prop := x = true ∨ p
    def V (x : Prop) : Prop := x = false ∨ p

    lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
    lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

    -- BEGIN
    noncomputable def u := some exU
    noncomputable def v := some exV

    lemma u_def : U u := some_spec exU
    lemma v_def : V v := some_spec exV
    -- END

    end diaconescu

Each of ``U`` and ``V`` is a disjunction, so ``u_def`` and ``v_def`` represent four cases. In one of these cases, ``u = true`` and ``v = false``, and in all the other cases, ``p`` is true. Thus we have:

.. code-block:: lean

    open classical
    section diaconescu
    parameter  p : Prop

    def U (x : Prop) : Prop := x = true ∨ p
    def V (x : Prop) : Prop := x = false ∨ p

    lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
    lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

    noncomputable def u := some exU
    noncomputable def v := some exV

    lemma u_def : U u := some_spec exU
    lemma v_def : V v := some_spec exV

    -- BEGIN
    lemma not_uv_or_p : u ≠ v ∨ p :=
    or.elim u_def
      (assume hut : u = true,
        or.elim v_def
          (assume hvf : v = false,
            have hne : u ≠ v, 
              from eq.symm hvf ▸ eq.symm hut ▸ true_ne_false,
            or.inl hne)
          (assume hp : p, or.inr hp))
      (assume hp : p, or.inr hp)
    -- END

    end diaconescu

On the other hand, if ``p`` is true, then, by function extensionality
and propositional extensionality, ``U`` and ``V`` are equal. By the
definition of ``u`` and ``v``, this implies that they are equal as well.

.. code-block:: lean

    open classical
    section diaconescu
    parameter  p : Prop

    def U (x : Prop) : Prop := x = true ∨ p
    def V (x : Prop) : Prop := x = false ∨ p

    lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
    lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

    noncomputable def u := some exU
    noncomputable def v := some exV

    lemma u_def : U u := some_spec exU
    lemma v_def : V v := some_spec exV

    lemma not_uv_or_p : ¬(u = v) ∨ p :=
    or.elim u_def
      (assume hut : u = true,
        or.elim v_def
          (assume hvf : v = false,
            have hne : u ≠ v, 
              from eq.symm hvf ▸ eq.symm hut ▸ true_ne_false,
            or.inl hne)
          (assume hp : p, or.inr hp))
      (assume hp : p, or.inr hp)

    -- BEGIN
    lemma p_implies_uv : p → u = v :=
    assume hp : p,
    have hpred : U = V, from
      funext (assume x : Prop,
        have hl : (x = true ∨ p) → (x = false ∨ p), from
          assume a, or.inr hp,
        have hr : (x = false ∨ p) → (x = true ∨ p), from
          assume a, or.inr hp,
        show (x = true ∨ p) = (x = false ∨ p), from
          propext (iff.intro hl hr)),
    have h₀ : ∀ exU exV,
        @classical.some _ U exU = @classical.some _ V exV,
      from hpred ▸ λ exU exV, rfl,
    show u = v, from h₀ _ _
    -- END
    end diaconescu

Putting these last two facts together yields the desired conclusion:

.. code-block:: lean

    open classical
    section diaconescu
    parameter  p : Prop

    def U (x : Prop) : Prop := x = true ∨ p
    def V (x : Prop) : Prop := x = false ∨ p

    lemma exU : ∃ x, U x := ⟨true, or.inl rfl⟩
    lemma exV : ∃ x, V x := ⟨false, or.inl rfl⟩

    noncomputable def u := some exU
    noncomputable def v := some exV

    lemma u_def : U u := some_spec exU
    lemma v_def : V v := some_spec exV

    lemma not_uv_or_p : ¬(u = v) ∨ p :=
    or.elim u_def
      (assume hut : u = true,
        or.elim v_def
          (assume hvf : v = false,
            have hne : ¬(u = v), from eq.symm hvf ▸ eq.symm hut ▸ true_ne_false,
            or.inl hne)
          (assume hp : p, or.inr hp))
      (assume hp : p, or.inr hp)

    lemma p_implies_uv : p → u = v :=
    assume hp : p,
    have hpred : U = V, from
      funext (assume x : Prop,
        have hl : (x = true ∨ p) → (x = false ∨ p), from
          assume a, or.inr hp,
        have hr : (x = false ∨ p) → (x = true ∨ p), from
          assume a, or.inr hp,
        show (x = true ∨ p) = (x = false ∨ p), from
          propext (iff.intro hl hr)),
    have h₀ : ∀ exU exV,
        @classical.some _ U exU = @classical.some _ V exV,
      from hpred ▸ λ exU exV, rfl,
    show u = v, from h₀ _ _

    -- BEGIN
    theorem em : p ∨ ¬p :=
    have h : ¬(u = v) → ¬p, from mt p_implies_uv,
      or.elim not_uv_or_p
        (assume hne : ¬(u = v), or.inr (h hne))
        (assume hp : p, or.inl hp)
    -- END

    end diaconescu

Consequences of excluded middle include double-negation elimination, proof by cases, and proof by contradiction, all of which are described in :numref:`classical_logic`. The law of the excluded middle and propositional extensionality imply propositional completeness:

.. code-block:: lean

    open classical
    namespace hidden

    -- BEGIN
    theorem prop_complete (a : Prop) : a = true ∨ a = false :=
    or.elim (em a)
      (λ t, or.inl (propext (iff.intro (λ h, trivial) (λ h, t))))
      (λ f, or.inr (propext (iff.intro (λ h, absurd h f) 
                                       (λ h, false.elim h))))
    -- END

    end hidden

Together with choice, we also get the stronger principle that every proposition is decidable. Recall that the class of ``decidable`` propositions is defined as follows:

.. code-block:: lean

    namespace hidden

    -- BEGIN
    class inductive decidable (p : Prop)
    | is_false : ¬ p → decidable
    | is_true :  p → decidable
    -- END

    end hidden

In contrast to ``p ∨ ¬ p``, which can only eliminate to ``Prop``, the type ``decidable p`` is equivalent to the sum type ``p ⊕ ¬ p``, which can eliminate to any type. It is this data that is needed to write an if-then-else expression.

As an example of classical reasoning, we use ``some`` to show that if ``f : α → β`` is injective and ``α`` is inhabited, then ``f`` has a left inverse. To define the left inverse ``linv``, we use a dependent if-then-else expression. Recall that ``if h : c then t else e`` is notation for ``dite c (λ h : c, t) (λ h : ¬ c, e)``. In the definition of ``linv``, choice is used twice: first, to show that ``(∃ a : A, f a = b)`` is "decidable," and then to choose an ``a`` such that ``f a = b``. Notice that we make ``prop_decidable`` a local instance to justify the if-then-else expression. (See also the discussion in :numref:`decidable_propositions`.)

.. code-block:: lean

    open classical function
    local attribute [instance] prop_decidable

    noncomputable definition linv {α β : Type} [h : inhabited α] 
      (f : α → β) : β → α :=
    λ b : β, if ex : (∃ a : α, f a = b) then some ex else arbitrary α

    theorem linv_comp_self {α β : Type} {f : α → β}
        [inhabited α] (inj : injective f) :
      linv f ∘ f = id :=
    funext (assume a,
      have ex  : ∃ a₁ : α, f a₁ = f a, from exists.intro a rfl,
      have   feq : f (some ex) = f a, from some_spec ex,
      calc linv f (f a) = some ex :  dif_pos ex
                 ...    = a       :  inj feq)

From a classical point of view, ``linv`` is a function. From a constructive point of view, it is unacceptable; because there is no way to implement such a function in general, the construction is not informative.
