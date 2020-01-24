.. _induction_and_recursion:

Induction and Recursion
=======================

In the previous chapter, we saw that inductive definitions provide a powerful means of introducing new types in Lean. Moreover, the constructors and the recursors provide the only means of defining functions on these types. By the propositions-as-types correspondence, this means that induction is the fundamental method of proof.

Lean provides natural ways of defining recursive functions, performing pattern matching, and writing inductive proofs. It allows you to define a function by specifying equations that it should satisfy, and it allows you to prove a theorem by specifying how to handle various cases that can arise. Behind the scenes, these descriptions are "compiled" down to primitive recursors, using a procedure that we refer to as the "equation compiler." The equation compiler is not part of the trusted code base; its output consists of terms that are checked independently by the kernel.

.. _pattern_matching:

Pattern Matching
----------------

The interpretation of schematic patterns is the first step of the compilation process. We have seen that the ``cases_on`` recursor can be used to define functions and prove theorems by cases, according to the constructors involved in an inductively defined type. But complicated definitions may use several nested ``cases_on`` applications, and may be hard to read and understand. Pattern matching provides an approach that is more convenient, and familiar to users of functional programming languages.

Consider the inductively defined type of natural numbers. Every natural number is either ``zero`` or ``succ x``, and so you can define a function from the natural numbers to an arbitrary type by specifying a value in each of those cases:

.. code-block:: lean

    open nat

    def sub1 : ℕ → ℕ
    | zero     := zero
    | (succ x) := x

    def is_zero : ℕ → Prop
    | zero     := true
    | (succ x) := false

The equations used to define these function hold definitionally:

.. code-block:: lean

    open nat

    def sub1 : ℕ → ℕ
    | zero     := zero
    | (succ x) := x

    def is_zero : ℕ → Prop
    | zero     := true
    | (succ x) := false

    -- BEGIN
    example : sub1 0 = 0 := rfl
    example (x : ℕ) : sub1 (succ x) = x := rfl

    example : is_zero 0 = true := rfl
    example (x : ℕ) : is_zero (succ x) = false := rfl

    example : sub1 7 = 6 := rfl
    example (x : ℕ) : ¬ is_zero (x + 3) := not_false
    -- END

Instead of ``zero`` and ``succ``, we can use more familiar notation:

.. code-block:: lean

    open nat

    def sub1 : ℕ → ℕ
    | 0     := 0
    | (x+1) := x

    def is_zero : ℕ → Prop
    | 0     := true
    | (x+1) := false

Because addition and the zero notation have been assigned the ``[pattern]`` attribute, they can be used in pattern matching. Lean simply normalizes these expressions until the constructors ``zero`` and ``succ`` are exposed.

Pattern matching works with any inductive type, such as products and option types:

.. code-block:: lean

    universes u v 
    variables {α : Type u}  {β : Type v}

    def swap_pair : α × β → β × α
    | (a, b) := (b, a)

    def foo : ℕ × ℕ → ℕ
    | (m, n) := m + n

    def bar : option ℕ → ℕ 
    | (some n) := n + 1
    | none     := 0

Here we use it not only to define a function, but also to carry out a proof by cases:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    def bnot : bool → bool
    | tt := ff
    | ff := tt

    theorem bnot_bnot : ∀ (b : bool), bnot (bnot b) = b
    | tt := rfl    -- proof that bnot (bnot tt) = tt
    | ff := rfl    -- proof that bnot (bnot ff) = ff
    -- END
    end hidden

Pattern matching can also be used to destruct inductively defined propositions:

.. code-block:: lean

    example (p q : Prop) : p ∧ q → q ∧ p 
    | (and.intro h₁ h₂) := and.intro h₂ h₁ 

    example (p q : Prop) : p ∨ q → q ∨ p 
    | (or.inl hp) := or.inr hp
    | (or.inr hq) := or.inl hq

This provides a compact way of unpacking hypotheses that make use of logical connectives.

In all these examples, pattern matching was used to carry out a single case distinction. More interestingly, patterns can involve nested constructors, as in the following examples.

.. code-block:: lean

    open nat

    def sub2 : ℕ → ℕ
    | zero            := 0
    | (succ zero)     := 0
    | (succ (succ a)) := a

The equation compiler first splits on cases as to whether the input is ``zero`` or of the form ``succ x``. It then does a case split on whether ``x`` is of the form ``zero`` or ``succ a``. It determines the necessary case splits from the patterns that are presented to it, and raises and error if the patterns fail to exhaust the cases. Once again, we can use arithmetic notation, as in the version below. In either case, the defining equations hold definitionally.

.. code-block:: lean

    def sub2 : ℕ → ℕ
    | 0     := 0
    | 1     := 0
    | (a+2) := a

    example : sub2 0 = 0 := rfl
    example : sub2 1 = 0 := rfl
    example (a : nat) : sub2 (a + 2) = a := rfl
    
    example : sub2 5 = 3 := rfl

You can write ``#print sub2`` to see how the function was compiled to recursors. (Lean will tell you that ``sub2`` has been defined in terms of an internal auxiliary function, ``sub2._main``, but you can print that out too.)

Here are some more examples of nested pattern matching:

.. code-block:: lean

    universe u

    example {α : Type u} (p q : α → Prop) : 
      (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
    | (exists.intro x (or.inl px)) := or.inl (exists.intro x px) 
    | (exists.intro x (or.inr qx)) := or.inr (exists.intro x qx) 

    def foo : ℕ × ℕ → ℕ
    | (0, n)     := 0
    | (m+1, 0)   := 1
    | (m+1, n+1) := 2

The equation compiler can process multiple arguments sequentially. For example, it would be more natural to define the previous example as a function of two arguments:

.. code-block:: lean

    def foo : ℕ → ℕ → ℕ
    | 0     n     := 0
    | (m+1) 0     := 1
    | (m+1) (n+1) := 2

Here is another example:

.. code-block:: lean

    def bar : list ℕ → list ℕ → ℕ 
    | []       []       := 0
    | (a :: l) []       := a
    | []       (b :: l) := b
    | (a :: l) (b :: m) := a + b 

Note that, with compound expressions, parentheses are used to separate the arguments. 

In each of the following examples, splitting occurs on only the first argument, even though the others are included among the list of patterns.

.. code-block:: lean

    namespace hidden

    -- BEGIN
    def band : bool → bool → bool
    | tt a := a
    | ff _ := ff

    def bor : bool → bool → bool
    | tt _ := tt
    | ff a := a

    def {u} cond {a : Type u} : bool → a → a → a
    | tt x y := x
    | ff x y := y
    -- END

    end hidden

Notice also that, when the value of an argument is not needed in the definition, you can use an underscore instead. This underscore is known as a *wildcard pattern*, or an *anonymous variable*. In contrast to usage outside the equation compiler, here the underscore does *not* indicate an implicit argument. The use of underscores for wildcards is common in functional programming languages, and so Lean adopts that notation. :numref:`wildcards_and_overlapping_patterns` expands on the notion of a wildcard, and :numref:`inaccessible_terms` explains how you can use implicit arguments in patterns as well.

As described in :numref:`Chapter %s <inductive_types>`, inductive data types can depend on parameters. The following example defines the ``tail`` function using pattern matching. The argument ``α : Type`` is a parameter and occurs before the colon to indicate it does not participate in the pattern matching. Lean also allows parameters to occur after ``:``, but it cannot pattern match on them.

.. code-block:: lean

    universe u

    -- BEGIN
    def tail1 {α : Type u} : list α → list α
    | []       := []
    | (h :: t) := t

    def tail2 : Π {α : Type u}, list α → list α
    | α []       := []
    | α (h :: t) := t
    -- END

Despite the different placement of the parameter ``α`` in these two examples, in both cases it treated in the same way, in that it does not participate in a case split.

Lean can also handle more complex forms of pattern matching, in which arguments to dependent types pose additional constraints on the various cases. Such examples of *dependent pattern matching* are considered in :numref:`dependent_pattern_matching`.

.. _wildcards_and_overlapping_patterns:

Wildcards and Overlapping Patterns
----------------------------------

Consider one of the examples from the last section:

.. code-block:: lean

    def foo : ℕ → ℕ → ℕ
    | 0     n     := 0
    | (m+1) 0     := 1
    | (m+1) (n+1) := 2

The example can be written more concisely:

.. code-block:: lean

    def foo : ℕ → ℕ → ℕ
    | 0 n := 0
    | m 0 := 1
    | m n := 2

In the second presentation, the patterns overlap; for example, the pair of arguments ``0 0`` matches all three cases. But Lean handles the ambiguity by using the first applicable equation, so the net result is the same. In particular, the following equations hold definitionally:

.. code-block:: lean

    def foo : ℕ → ℕ → ℕ
    | 0 n := 0
    | m 0 := 1
    | m n := 2

    -- BEGIN
    variables (m n : nat)

    example : foo 0     0     = 0 := rfl
    example : foo 0     (n+1) = 0 := rfl
    example : foo (m+1) 0     = 1 := rfl
    example : foo (m+1) (n+1) = 2 := rfl
    -- END

Since the values of ``m`` and ``n`` are not needed, we can just as well use wildcard patterns instead.

.. code-block:: lean

    def foo : ℕ → ℕ → ℕ
    | 0 _ := 0
    | _ 0 := 1
    | _ _ := 2

You can check that this definition of ``foo`` satisfies the same definitional identities as before.

Some functional programming languages support *incomplete patterns*. In these languages, the interpreter produces an exception or returns an arbitrary value for incomplete cases. We can simulate the arbitrary value approach using the ``inhabited`` type class. Roughly, an element of ``inhabited α`` is a witness to the fact that there is an element of ``α``; in :numref:`Chapter %s <type_classes>` we will see that Lean can be instructed that suitable base types are inhabited, and can automatically infer that other constructed types are inhabited on that basis. On this basis, the standard library provides an arbitrary element, ``arbitrary α``, of any inhabited type.

We can also use the type ``option α`` to simulate incomplete patterns. The idea is to return ``some a`` for the provided patterns, and use ``none`` for the incomplete cases. The following example demonstrates both approaches.

.. code-block:: lean

    def f1 : ℕ → ℕ → ℕ
    | 0  _  := 1
    | _  0  := 2
    | _  _  := arbitrary ℕ   -- the "incomplete" case

    variables (a b : ℕ)

    example : f1 0     0     = 1 := rfl
    example : f1 0     (a+1) = 1 := rfl
    example : f1 (a+1) 0     = 2 := rfl
    example : f1 (a+1) (b+1) = arbitrary nat := rfl

    def f2 : ℕ → ℕ → option ℕ
    | 0  _  := some 1
    | _  0  := some 2
    | _  _  := none          -- the "incomplete" case

    example : f2 0     0     = some 1 := rfl
    example : f2 0     (a+1) = some 1 := rfl
    example : f2 (a+1) 0     = some 2 := rfl
    example : f2 (a+1) (b+1) = none   := rfl

The equation compiler is clever. If you leave out any of the cases in the following definition, the error message will let you know what has not been covered.

.. code-block:: lean

    def bar : ℕ → list ℕ → bool → ℕ
    | 0     _        ff := 0
    | 0     (b :: _) _  := b
    | 0     []       tt := 7
    | (a+1) []       ff := a
    | (a+1) []       tt := a + 1
    | (a+1) (b :: _) _  := a + b

It will also use an "if ... then ... else" instead of a ``cases_on`` in appropriate situations.

.. code-block:: lean

    def foo : char → ℕ 
    | 'A' := 1
    | 'B' := 2
    | _   := 3

    #print foo._main

.. _structural_recursion_and_induction:

Structural Recursion and Induction
----------------------------------

What makes the equation compiler powerful is that it also supports recursive definitions. In the next three sections, we will describe, respectively:

- structurally recursive definitions
- well-founded recursive definitions
- mutually recursive definitions

Generally speaking, the equation compiler processes input of the following form:

.. code-block:: text

    def foo (a : α) : Π (b : β), γ
    | [patterns₁] := t₁
    ...
    | [patternsₙ] := tₙ 

Here ``(a : α)`` is a sequence of parameters, ``(b : β)`` is the sequence of arguments on which pattern matching takes place, and ``γ`` is any type, which can depend on ``a`` and ``b``. Each line should contain the same number of patterns, one for each element of β. As we have seen, a pattern is either a variable, a constructor applied to other patterns, or an expression that normalizes to something of that form (where the non-constructors are marked with the ``[pattern]`` attribute). The appearances of constructors prompt case splits, with the arguments to the constructors represented by the given variables. In :numref:`dependent_pattern_matching`, we will see that it is sometimes necessary to include explicit terms in patterns that are needed to make an expression type check, though they do not play a role in pattern matching. These are called "inaccessible terms," for that reason. But we will not need to use such inaccessible terms before :numref:`dependent_pattern_matching`.

As we saw in the last section, the terms ``t₁, ..., tₙ`` can make use of any of the parameters ``a``, as well as any of the variables that are introduced in the corresponding patterns. What makes recursion and induction possible is that they can also involve recursive calls to ``foo``. In this section, we will deal with *structural recursion*, in which the arguments to ``foo`` occurring on the right-hand side of the ``:=`` are subterms of the patterns on the left-hand side. The idea is that they are structurally smaller, and hence appear in the inductive type at an earlier stage. Here are some examples of structural recursion from the last chapter, now defined using the equation compiler:

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    -- BEGIN
    def add : nat → nat → nat
    | m zero     := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    theorem add_zero (m : nat) : m + zero = m := rfl
    theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

    theorem zero_add : ∀ n, zero + n = n
    | zero     := rfl
    | (succ n) := congr_arg succ (zero_add n)

    def mul : nat → nat → nat
    | n zero     := zero
    | n (succ m) := mul n m + n
    -- END

    end nat
    end hidden

The proof of ``zero_add`` makes it clear that proof by induction is really a form of induction in Lean.

The example above shows that the defining equations for ``add`` hold definitionally, and the same is true of ``mul``. The equation compiler tries to ensure that this holds whenever possible, as is the case with straightforward structural induction. In other situations, however, reductions hold only *propositionally*, which is to say, they are equational theorems that must be applied explicitly. The equation compiler generates such theorems internally. They are not meant to be used directly by the user; rather, the `simp` and `rewrite` tactics are configured to use them when necessary. Thus both of the following proofs of `zero_add` work:

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    def add : nat → nat → nat
    | m zero     := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    -- BEGIN
    theorem zero_add : ∀ n, zero + n = n
    | zero     := by simp [add]
    | (succ n) := by simp [add, zero_add n]

    theorem zero_add' : ∀ n, zero + n = n
    | zero     := by rw [add]
    | (succ n) := by rw [add, zero_add' n]
    -- END

    end nat
    end hidden

In fact, because in this case the defining equations hold definitionally, we can use `dsimp`, the simplifier that uses definitional reductions only, to carry out the first step.

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    def add : nat → nat → nat
    | m zero     := m
    | m (succ n) := succ (add m n)

    local infix ` + ` := add

    -- BEGIN
    theorem zero_add : ∀ n, zero + n = n
    | zero     := by dsimp [add]; reflexivity
    | (succ n) := by dsimp [add]; rw [zero_add n]
    -- END

    end nat
    end hidden

As with definition by pattern matching, parameters to a structural recursion or induction may appear before the colon. Such parameters are simply added to the local context before the definition is processed. For example, the definition of addition may also be written as follows:

.. code-block:: lean

    namespace hidden

    inductive nat : Type
    | zero : nat
    | succ : nat → nat

    namespace nat

    -- BEGIN
    def add (m : nat) : nat → nat
    | zero     := m
    | (succ n) := succ (add n)
    -- END

    end nat
    end hidden

This may seem a little odd, but you should read the definition as follows: "Fix ``m``, and define the function which adds something to ``m`` recursively, as follows. To add zero, return ``m``. To add the successor of ``n``, first add ``n``, and then take the successor." The mechanism for adding parameters to the local context is what makes it possible to process match expressions within terms, as described in :numref:`match_expressions`.

A more interesting example of structural recursion is given by the Fibonacci function ``fib``.

.. code-block:: lean

    def fib : nat → nat
    | 0     := 1
    | 1     := 1
    | (n+2) := fib (n+1) + fib n

    example : fib 0 = 1 := rfl
    example : fib 1 = 1 := rfl
    example (n : nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

    example : fib 7 = 21 := rfl
    example : fib 7 = 21 :=
    begin
      dsimp [fib],   -- expands fib 7 as a sum of 1's
      reflexivity
    end

Here, the value of the ``fib`` function at ``n + 2`` (which is definitionally equal to ``succ (succ n)``) is defined in terms of the values at ``n + 1`` (which is definitionally equivalent to ``succ n``) and the value at ``n``.

To handle such  definitions, the equation compiler uses *course-of-values* recursion, using constants ``below`` and ``brec_on`` that are automatically generated with each inductively defined type. You can get a sense of how it works by looking at the types of ``nat.below`` and ``nat.brec_on``:

.. code-block:: lean

    variable (C : ℕ → Type)

    #check (@nat.below C : ℕ → Type)

    #reduce @nat.below C (3 : nat)

    #check (@nat.brec_on C : 
      Π (n : ℕ), (Π (n : ℕ), nat.below C n → C n) → C n)

The type ``@nat.below C (3 : nat)`` is a data structure that stores elements of ``C 0``, ``C 1``, and ``C 2``. The course-of-values recursion is implemented by ``nat.brec_on``. It enables us to define the value of a dependent function of type ``Π n : ℕ, C n`` at a particular input ``n`` in terms of all the previous values of the function, presented as an element of ``@nat_below C n``.

The use of course-of-values recursion is a design choice. Sometimes it works extremely well; for example, it provides an efficient implementation of ``fib``, avoiding the exponential blowup that would arise from evaluating each recursive call independently. (You can call the bytecode evaluator to evaluate ``fib 10000`` by writing ``#eval (fib 10000)`` to confirm that it has no problem doing that.) In other situations, the choice may be less optimal. In any case, keep in mind that this behavior may change in the future, as better compilation strategies are developed for Lean. 

Another good example of a recursive definition is the list ``append`` function.

.. code-block:: lean

    namespace hidden
    -- BEGIN
    def append {α : Type} : list α → list α → list α
    | []     l := l
    | (h::t) l := h :: append t l

    example : append [(1 : ℕ), 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
    -- END
    end hidden

Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.

.. code-block:: lean

    def {u} list_add {α : Type u} [has_add α] :
      list α → list α → list α
    | []       _        := []
    | _        []       := []
    | (a :: l) (b :: m) := (a + b) :: list_add l m

    #eval list_add [1, 2, 3] [4, 5, 6, 6, 9, 10]

You are encouraged to experiment with similar examples in the exercises below.

.. _well_founded_recursion_and_induction:

Well-Founded Recursion and Induction
------------------------------------

Dependent type theory is powerful enough to encode and justify well-founded recursion. Let us start with the logical background that is needed to understand how it works.

Lean's standard library defines two predicates, ``acc r a`` and ``well_founded r``, where ``r`` is a binary relation on a type ``α``, and ``a`` is an element of type ``α``.

.. code-block:: lean

    universe u
    variable α : Sort u
    variable r : α → α → Prop

    #check (acc r : α → Prop)
 
    #check (well_founded r : Prop)

The first, ``acc``, is an inductively defined predicate. According to its definition, ``acc r x`` is equivalent to ``∀ y, r y x → acc r y``. If you think of ``r y x`` as denoting a kind of order relation ``y ≺ x``, then ``acc r x`` says that ``x`` is accessible from below, in the sense that all its predecessors are accessible. In particular, if ``x`` has no predecessors, it is accessible. Given any type ``α``, we should be able to assign a value to each accessible element of ``α``, recursively, by assigning values to all its predecessors first.

The statement that ``r`` is well founded, denoted ``well_founded r``, is exactly the statement that every element of the type is accessible. By the above considerations, if ``r`` is a well-founded relation on a type ``α``, we should have a principle of well-founded recursion on ``α``, with respect to the relation ``r``. And, indeed, we do: the standard library defines ``well_founded.fix``, which serves exactly that purpose.

.. code-block:: lean

    universes u v
    variable α : Sort u
    variable r : α → α → Prop
    variable h : well_founded r 

    variable C : α → Sort v
    variable F : Π x, (Π (y : α), r y x → C y) → C x

    def f : Π (x : α), C x := well_founded.fix h F

There is a long cast of characters here, but the first block we have already seen: the type, ``α``, the relation, ``r``, and the assumption, ``h``, that ``r`` is well founded. The variable ``C`` represents the motive of the recursive definition: for each element ``x : α``, we would like to construct an element of ``C x``. The function ``F`` provides the inductive recipe for doing that: it tells us how to construct an element ``C x``, given elements of ``C y`` for each predecessor ``y`` of ``x``.

Note that ``well_founded.fix`` works equally well as an induction principle. It says that if ``≺`` is well founded and you want to prove ``∀ x, C x``, it suffices to show that for an arbitrary ``x``, if we have ``∀ y ≺ x, C y``, then we have ``C x``.

Lean knows that the usual order ``<`` on the natural numbers is well founded. It also knows a number of ways of constructing new well founded orders from others, for example, using lexicographic order. 

Here is essentially the definition of division on the natural numbers that is found in the standard library.

.. code-block:: lean

    namespace hidden

    -- BEGIN
    open nat

    def div_rec_lemma {x y : ℕ} : 0 < y ∧ y ≤ x → x - y < x :=
    λ h, sub_lt (lt_of_lt_of_le h.left h.right) h.left

    def div.F (x : ℕ) (f : Π x₁, x₁ < x → ℕ → ℕ) (y : ℕ) : ℕ :=
    if h : 0 < y ∧ y ≤ x then 
      f (x - y) (div_rec_lemma h) y + 1 
    else 
      zero

    def div := well_founded.fix lt_wf div.F
    -- END

    end hidden

The definition is somewhat inscrutable. Here the recursion is on ``x``, and ``div.F x f : ℕ → ℕ`` returns the "divide by ``y``" function for that fixed ``x``. You have to remember that the second argument to ``div.F``, the recipe for the recursion, is a function that is supposed to return the divide by ``y`` function for all values ``x₁`` smaller than ``x``.

The equation compiler is designed to make definitions like this more convenient. It accepts the following:

.. code-block:: lean

    namespace hidden
    open nat

    -- BEGIN
    def div : ℕ → ℕ → ℕ
    | x y := 
      if h : 0 < y ∧ y ≤ x then
        have x - y < x, 
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0
    -- END
        
    end hidden

When the equation compiler encounters a recursive definition, it first tries structural recursion, and only when that fails, does it fall back on well-founded recursion. In this case, detecting the possibility of well-founded recursion on the natural numbers, it uses the usual lexicographic ordering on the pair ``(x, y)``. The equation compiler in and of itself is not clever enough to derive that ``x - y`` is less than ``x`` under the given hypotheses, but we can help it out by putting this fact in the local context. The equation compiler looks in the local context for such information, and, when it finds it, puts it to good use. 

The defining equation for ``div`` does *not* hold definitionally, but the equation is available to ``rewrite`` and ``simp``. The simplifier will loop if you apply it blindly, but ``rewrite`` will do the trick.

.. code-block:: lean

    namespace hidden
    open nat

    def div : ℕ → ℕ → ℕ
    | x y :=
      if h : 0 < y ∧ y ≤ x then
        have x - y < x, 
          from sub_lt (lt_of_lt_of_le h.left h.right) h.left,
        div (x - y) y + 1
      else
        0

    -- BEGIN
    example (x y : ℕ) :  
      div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
    by rw [div]

    example (x y : ℕ) (h : 0 < y ∧ y ≤ x) : 
      div x y = div (x - y) y + 1 :=
    by rw [div, if_pos h]
    -- END
        
    end hidden

The following example is similar: it converts any natural number to a binary expression, represented as a list of 0's and 1's. We have to provide the equation compiler with evidence that the recursive call is decreasing, which we do here with a ``sorry``. The ``sorry`` does not prevent the bytecode evaluator from evaluating the function successfully.

.. code-block:: lean

    def nat_to_bin : ℕ → list ℕ
    | 0       := [0]
    | 1       := [1]
    | (n + 2) := 
      have (n + 2) / 2 < n + 2, from sorry,
      nat_to_bin ((n + 2) / 2) ++ [n % 2]

    #eval nat_to_bin 1234567

As a final example, we observe that Ackermann's function can be defined directly, because it is justified by the well foundedness of the lexicographic order on the natural numbers.

.. code-block:: lean

    def ack : nat → nat → nat
    | 0     y     := y+1
    | (x+1) 0     := ack x 1
    | (x+1) (y+1) := ack x (ack (x+1) y)

    #eval ack 3 5

Lean's mechanisms for guessing a well-founded relation and then proving that recursive calls decrease are still in a rudimentary state. They will be improved over time. When they work, they provide a much more convenient way of defining functions than using ``well_founded.fix`` manually. When they don't, the latter is always available as a backup. 

.. TO DO: eventually, describe using_well_founded.

.. _nested_and_mutual_recursion:

Mutual Recursion
----------------

Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types, as described in :numref:`mutual_and_nested_inductive_types`. Here is an example:

.. code-block:: lean

    mutual def even, odd
    with even : nat → bool
    | 0     := tt
    | (a+1) := odd a
    with odd : nat → bool
    | 0     := ff
    | (a+1) := even a

    example (a : nat) : even (a + 1) = odd a :=
    by simp [even]

    example (a : nat) : odd (a + 1) = even a :=
    by simp [odd]

    lemma even_eq_not_odd : ∀ a, even a = bnot (odd a) :=
    begin
      intro a, induction a,
      simp [even, odd],
      simp [*, even, odd]
    end

What makes this a mutual definition is that ``even`` is defined recursively in terms of ``odd``, while ``odd`` is defined recursively in terms of ``even``. Under the hood, this is compiled as a single recursive definition. The internally defined function takes, as argument, an element of a sum type, either an input to ``even``, or an input to ``odd``. It then returns an output appropriate to the input. To define that function, Lean uses a suitable well-founded measure. The internals are meant to be hidden from users; the canonical way to make use of such definitions is to use ``rewrite`` or ``simp``, as we did above.

Mutual recursive definitions also provide natural ways of working with mutual and nested inductive types, as described in :numref:`mutual_and_nested_inductive_types`. Recall the definition of ``even`` and ``odd`` as mutual inductive predicates, as presented as an example there:

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

The constructors, ``even_zero``, ``even_succ``, and ``odd_succ`` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that the zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command ``open even odd`` allows us to access them move conveniently.

.. code-block:: lean

    mutual inductive even, odd
    with even : ℕ → Prop
    | even_zero : even 0
    | even_succ : ∀ n, odd n → even (n + 1)
    with odd : ℕ → Prop
    | odd_succ : ∀ n, even n → odd (n + 1)

    -- BEGIN
    open even odd

    theorem not_odd_zero : ¬ odd 0.

    mutual theorem even_of_odd_succ, odd_of_even_succ
    with even_of_odd_succ : ∀ n, odd (n + 1) → even n
    | _ (odd_succ n h) := h
    with odd_of_even_succ : ∀ n, even (n + 1) → odd n
    | _ (even_succ n h) := h
    -- END

For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.

.. code-block:: lean

    inductive term
    | const : string → term
    | app   : string → list term → term

    -- BEGIN
    open term

    mutual def num_consts, num_consts_lst
    with num_consts : term → nat
    | (term.const n)  := 1
    | (term.app n ts) := num_consts_lst ts
    with num_consts_lst : list term → nat
    | []      := 0
    | (t::ts) := num_consts t + num_consts_lst ts

    def sample_term := app "f" [app "g" [const "x"], const "y"]

    #eval num_consts sample_term
    -- END

.. _dependent_pattern_matching:

Dependent Pattern Matching
--------------------------

All the examples of pattern matching we considered in :numref:`pattern_matching` can easily be written using ``cases_on`` and ``rec_on``. However, this is often not the case with indexed inductive families such as ``vector α n``, since case splits impose constraints on the values of the indices. Without the equation compiler, we would need a lot of boilerplate code to define very simple functions such as ``map``, ``zip``, and ``unzip`` using recursors. To understand the difficulty, consider what it would take to define a function ``tail`` which takes a vector ``v : vector α (succ n)`` and deletes the first element. A first thought might be to use the ``cases_on`` function:

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : nat → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    #check @vector.cases_on
    -- Π {α : Type}
    --   {C : Π (a : ℕ), vector α a → Type}
    --   {a : ℕ}
    --   (n : vector α a),
    --   (e1 : C 0 nil)
    --   (e2 : Π {n : ℕ} (a : α) (a_1 : vector α n), 
    --           C (n + 1) (cons a a_1)),
    --   C a n
    
    end vector

But what value should we return in the ``nil`` case? Something funny is going on: if ``v`` has type ``vector α (succ n)``, it *can't* be nil, but it is not clear how to tell that to ``cases_on``.

One solution is to define an auxiliary function:

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    -- BEGIN
    def tail_aux {α : Type} {n m : ℕ} (v : vector α m) :
        m = n + 1 → vector α n :=
    vector.cases_on v
      (assume H : 0 = n + 1, nat.no_confusion H)
      (assume m (a : α) w : vector α m,
        assume H : m + 1 = n + 1,
          nat.no_confusion H (λ H1 : m = n, eq.rec_on H1 w))

    def tail {α : Type} {n : ℕ} (v : vector α (n+1)) : 
      vector α n :=
    tail_aux v rfl
    -- END

    end vector

In the ``nil`` case, ``m`` is instantiated to ``0``, and ``no_confusion`` makes use of the fact that ``0 = succ n`` cannot occur. Otherwise, ``v`` is of the form ``a :: w``, and we can simply return ``w``, after casting it from a vector of length ``m`` to a vector of length ``n``.

The difficulty in defining ``tail`` is to maintain the relationships between the indices. The hypothesis ``e : m = n + 1`` in ``tail_aux`` is used to communicate the relationship between ``n`` and the index associated with the minor premise. Moreover, the ``zero = n + 1`` case is unreachable, and the canonical way to discard such a case is to use ``no_confusion``.

The ``tail`` function is, however, easy to define using recursive equations, and the equation compiler generates all the boilerplate code automatically for us. Here are a number of similar examples:

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    -- BEGIN
    def head {α : Type} : Π {n}, vector α (n+1) → α
    | n (h :: t) := h

    def tail {α : Type} : Π {n}, vector α (n+1) → vector α n
    | n (h :: t) := t

    lemma eta {α : Type} : 
      ∀ {n} (v : vector α (n+1)), head v :: tail v = v
    | n (h :: t) := rfl

    def map {α β γ : Type} (f : α → β → γ) :
      Π {n}, vector α n → vector β n → vector γ n
    | 0     nil       nil       := nil
    | (n+1) (a :: va) (b :: vb) := f a b :: map va vb

    def zip {α β : Type} : 
      Π {n}, vector α n → vector β n → vector (α × β) n
    | 0     nil       nil       := nil
    | (n+1) (a :: va) (b :: vb) := (a, b) :: zip va vb
    -- END

    end vector

Note that we can omit recursive equations for "unreachable" cases such as ``head nil``. The automatically generated definitions for indexed families are far from straightforward. For example:

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    def map {α β γ : Type} (f : α → β → γ)
            : Π {n : nat}, vector α n → vector β n → vector γ n
    | 0     nil     nil     := nil
    | (n+1) (a::va) (b::vb) := f a b :: map va vb

    -- BEGIN
    #print map
    #print map._main
    -- END

    end vector

The ``map`` function is even more tedious to define by hand than the ``tail`` function. We encourage you to try it, using ``rec_on``, ``cases_on`` and ``no_confusion``.

.. _inaccessible_terms:

Inaccessible Terms
------------------

Sometimes an argument in a dependent matching pattern is not essential to the definition, but nonetheless has to be included to specialize the type of the expression appropriately. Lean allows users to mark such subterms as *inaccessible* for pattern matching. These annotations are essential, for example, when a term occurring in the left-hand side is neither a variable nor a constructor application, because these are not suitable targets for pattern matching. We can view such inaccessible terms as "don't care" components of the patterns. You can declare a subterm inaccessible by writing ``.(t)``. If the inaccessible term can be inferred, you can also write ``._``.

The following example can be found in [GoMM06]_. We declare an inductive type that defines the property of "being in the image of ``f``". You can view an element of the type ``image_of f b`` as evidence that ``b`` is in the image of ``f``, whereby the constructor ``imf`` is used to build such evidence. We can then define any function ``f`` with an "inverse" which takes anything in the image of ``f`` to an element that is mapped to it. The typing rules forces us to write ``f a`` for the first argument, but this term is neither a variable nor a constructor application, and plays no role in the pattern-matching definition. To define the function ``inverse`` below, we *have to* mark ``f a`` inaccessible.

.. code-block:: lean

    variables {α β : Type}
    inductive image_of (f : α → β) : β → Type
    | imf : Π a, image_of (f a)

    open image_of

    def inverse {f : α → β} : Π b, image_of f b → α
    | .(f a) (imf .(f) a) := a

In the example above, the inaccessible annotation makes it clear that ``f`` is *not* a pattern matching variable.

Inaccessible terms can be used to clarify and control definitions that make use of dependent pattern matching. Consider the following definition of the function ``vector.add,`` which adds two vectors of elements of a type, assuming that type has an associated addition function:

.. code-block:: lean

    -- BEGIN
    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    variable {α : Type u}
    
    def add [has_add α] : Π {n : ℕ}, vector α n → vector α n → vector α n 
    | 0     nil        nil        := nil
    | (n+1) (cons a v) (cons b w) := cons (a + b) (add v w)

    end vector
    -- END

The argument ``{n : ℕ}`` has to appear after the colon, because it cannot be held fixed throughout the definition. When implementing this definition, the equation compiler starts with a case distinction as to whether the first argument is ``0`` or of the form ``n+1``. This is followed by nested case splits on the next two arguments, and in each case the equation compiler rules out the cases are not compatible with the first pattern.

But, in fact, a case split is not required on the first argument; the ``cases_on`` eliminator for ``vector`` automatically abstracts this argument and replaces it by ``0`` and ``n + 1`` when we do a case split on the second argument. Using inaccessible terms, we can prompt the equation compiler to avoid the case split on ``n``:

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    variable {α : Type u}

    -- BEGIN
    def add [has_add α] : Π {n : ℕ}, vector α n → vector α n → vector α n 
    | ._ nil        nil        := nil
    | ._ (cons a v) (cons b w) := cons (a + b) (add v w)
    -- END

    end vector

Marking the position as an inaccessible implicit argument tells the equation compiler first, that the form of the argument should be inferred from the constraints posed by the other arguments, and, second, that the first argument should *not* participate in pattern matching. 

Using explicit inaccessible terms makes it even clearer what is going on.

.. code-block:: lean

    universe u

    inductive vector (α : Type u) : ℕ → Type u
    | nil {} : vector 0
    | cons   : Π {n}, α → vector n → vector (n+1)

    namespace vector
    local notation h :: t := cons h t

    variable {α : Type u}

    -- BEGIN
    def add [has_add α] : Π {n : ℕ}, vector α n → vector α n → vector α n 
    | .(0)   nil                nil        := nil
    | .(n+1) (@cons .(α) n a v) (cons b w) := cons (a + b) (add v w)
    -- END

    end vector

We have to introduce the variable ``n`` in the pattern ``@cons .(α) n a v``, since it is involved in the pattern match over that argument. In contrast, the parameter ``α`` is held fixed; we could have left it implicit by writing ``._`` instead. The advantage to naming the variable there is that we can now use inaccessible terms in the first position to display the values that were inferred implicitly in the previous example.

.. _match_expressions:

Match Expressions
-----------------

Lean also provides a compiler for *match-with* expressions found in many functional languages. It uses essentially the same infrastructure used to compile recursive equations.

.. code-block:: lean

    def is_not_zero (m : ℕ) : bool :=
    match m with
    | 0     := ff
    | (n+1) := tt
    end

This does not look very different from an ordinary pattern matching definition, but the point is that a ``match`` can be used anywhere in an expression, and with arbitrary arguments.

.. code-block:: lean

    def is_not_zero (m : ℕ) : bool :=
    match m with
    | 0     := ff
    | (n+1) := tt
    end
    
    -- BEGIN
    variable {α : Type}
    variable p : α → bool

    def filter : list α → list α
    | []       := []
    | (a :: l) :=
      match p a with
      |  tt := a :: filter l
      |  ff := filter l
      end

    example : filter is_not_zero [1, 0, 0, 3, 0] = [1, 3] := rfl
    -- END

Here is another example:

.. code-block:: lean

    def foo (n : ℕ) (b c : bool) :=
    5 + match n - 5, b && c with
        | 0,      tt := 0
        | m+1,    tt := m + 7
        | 0,      ff := 5
        | m+1,    ff := m + 3
        end

    #eval foo 7 tt ff

    example : foo 7 tt ff = 9 := rfl

Notice that with multiple arguments, the syntax for the match statement is markedly different from that used for pattern matching in an ordinary recursive definition. Because arbitrary terms are allowed in the ``match``, parentheses are not enough to set the arguments apart; if we wrote ``(n - 5) (b && c)``, it would be interpreted as the result of applying ``n - 5`` to ``b && c``. Instead, the arguments are separated by commas. Then, for consistency, the patterns on each line are separated by commas as well.

Lean uses the ``match`` construct internally to implement a pattern-matching ``assume``, as well as a pattern-matching ``let``. Thus, all four of these definitions have the same net effect.

.. code-block:: lean

    def bar₁ : ℕ × ℕ → ℕ 
    | (m, n) := m + n

    def bar₂ (p : ℕ × ℕ) : ℕ :=
    match p with (m, n) := m + n end

    def bar₃ : ℕ × ℕ → ℕ := 
    λ ⟨m, n⟩, m + n

    def bar₄ (p : ℕ × ℕ) : ℕ :=
    let ⟨m, n⟩ := p in m + n

The second definition also illustrates the fact that in a match with a single pattern, the vertical bar is optional. These variations are equally useful for destructing propositions:

.. code-block:: lean

    variables p q : ℕ → Prop

    example : (∃ x, p x) → (∃ y, q y) → 
      ∃ x y, p x ∧ q y
    | ⟨x, px⟩ ⟨y, qy⟩ := ⟨x, y, px, qy⟩ 

    example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y) : 
      ∃ x y, p x ∧ q y :=
    match h₀, h₁ with 
    ⟨x, px⟩, ⟨y, qy⟩ := ⟨x, y, px, qy⟩ 
    end

    example : (∃ x, p x) → (∃ y, q y) → 
      ∃ x y, p x ∧ q y :=
    λ ⟨x, px⟩ ⟨y, qy⟩, ⟨x, y, px, qy⟩

    example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y) : 
      ∃ x y, p x ∧ q y :=
    let ⟨x, px⟩ := h₀,
        ⟨y, qy⟩ := h₁ in
    ⟨x, y, px, qy⟩

Exercises
---------

#. Use pattern matching to prove that the composition of surjective functions is surjective:

   .. code-block:: lean

      open function

      #print surjective

      universes u v w
      variables {α : Type u} {β : Type v} {γ : Type w}
      open function

      lemma surjective_comp {g : β → γ} {f : α → β} 
        (hg : surjective g) (hf : surjective f) : 
      surjective (g ∘ f) := sorry

#. Open a namespace ``hidden`` to avoid naming conflicts, and use the equation compiler to define addition, multiplication, and exponentiation on the natural numbers. Then use the equation compiler to derive some of their basic properties.

#. Similarly, use the equation compiler to define some basic operations on lists (like the ``reverse`` function) and prove theorems about lists by induction (such as the fact that ``reverse (reverse l) = l`` for any list ``l``).

#. Define your own function to carry out course-of-value recursion on the natural numbers. Similarly, see if you can figure out how to define ``well_founded.fix`` on your own.

#. Following the examples in :numref:`dependent_pattern_matching`, define a function that will append two vectors. This is tricky; you will have to define an auxiliary function.

#. Consider the following type of arithmetic expressions. The idea is that ``var n`` is a variable, ``vₙ``, and ``const n`` is the constant whose value is ``n``.

   .. code-block:: lean

      inductive aexpr : Type
      | const : ℕ → aexpr
      | var : ℕ → aexpr
      | plus : aexpr → aexpr → aexpr
      | times : aexpr → aexpr → aexpr

      open aexpr

      def sample_aexpr : aexpr := 
      plus (times (var 0) (const 7)) (times (const 2) (var 1))

   Here ``sample_aexpr`` represents ``(v₀ + 7) * (2 + v₁)``. 
   
   Write a function that evaluates such an expression, evaluating each ``var n`` to ``v n``. 

   .. code-block:: lean

      inductive aexpr : Type
      | const : ℕ → aexpr
      | var : ℕ → aexpr
      | plus : aexpr → aexpr → aexpr
      | times : aexpr → aexpr → aexpr

      open aexpr

      def sample_aexpr : aexpr := 
      plus (times (var 0) (const 7)) (times (const 2) (var 1))

      -- BEGIN
      def aeval (v : ℕ → ℕ) : aexpr → ℕ
      | (const n)    := sorry
      | (var n)      := v n
      | (plus e₁ e₂)  := sorry
      | (times e₁ e₂) := sorry

      def sample_val : ℕ → ℕ
      | 0 := 5
      | 1 := 6
      | _ := 0

      -- Try it out. You should get 47 here.
      -- #eval aeval sample_val sample_aexpr
      -- END

   Implement "constant fusion," a procedure that simplifies subterms like ``5 + 7`` to ``12``. Using the auxiliary function ``simp_const``, define a function "fuse": to simplify a plus or a times, first simplify the arguments recursively, and then apply ``simp_const`` to try to simplify the result.

   .. code-block:: lean

      inductive aexpr : Type
      | const : ℕ → aexpr
      | var : ℕ → aexpr
      | plus : aexpr → aexpr → aexpr
      | times : aexpr → aexpr → aexpr

      open aexpr

      def aeval (v : ℕ → ℕ) : aexpr → ℕ
      | (const n)    := sorry
      | (var n)      := v n
      | (plus e₁ e₂)  := sorry
      | (times e₁ e₂) := sorry

      -- BEGIN
      def simp_const : aexpr → aexpr
      | (plus (const n₁) (const n₂))  := const (n₁ + n₂)
      | (times (const n₁) (const n₂)) := const (n₁ * n₂)
      | e                             := e

      def fuse : aexpr → aexpr := sorry

      theorem simp_const_eq (v : ℕ → ℕ) : 
        ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
      sorry

      theorem fuse_eq (v : ℕ → ℕ) : 
        ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
      sorry
      -- END

   The last two theorems show that the definitions preserve the value.

.. [GoMM06] Healfdene Goguen, Conor McBride, and James McKinna. Eliminating dependent pattern matching. In Kokichi Futatsugi, Jean-Pierre Jouannaud, and José Meseguer, editors, Algebra, Meaning, and Computation, Essays Dedicated to Joseph A. Goguen on the Occasion of His 65th Birthday, volume 4060 of Lecture Notes in Computer Science, pages 521–540. Springer, 2006.
