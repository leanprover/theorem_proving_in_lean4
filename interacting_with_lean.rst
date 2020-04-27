.. _interacting_with_lean:

Interacting with Lean
=====================

You are now familiar with the fundamentals of dependent type theory, both as a language for defining mathematical objects and a language for constructing proofs. The one thing you are missing is a mechanism for defining new data types. We will fill this gap in the next chapter, which introduces the notion of an *inductive data type*. But first, in this chapter, we take a break from the mechanics of type theory to explore some pragmatic aspects of interacting with Lean.

Not all of the information found here will be useful to you right away. We recommend skimming this section to get a sense of Lean's features, and then returning to it as necessary.

.. _importing_files:

Importing Files
---------------

The goal of Lean's front end is to interpret user input, construct formal expressions, and check that they are well formed and type correct. Lean also supports the use of various editors, which provide continuous checking and feedback. More information can be found on the Lean `documentation pages <http://leanprover.github.io/documentation/>`__.

The definitions and theorems in Lean's standard library are spread across multiple files. Users may also wish to make use of additional libraries, or develop their own projects across multiple files. When Lean starts, it automatically imports the contents of the library ``init`` folder, which includes a number of fundamental definitions and constructions. As a result, most of the examples we present here work "out of the box."

If you want to use additional files, however, they need to be imported manually, via an ``import`` statement at the beginning of a file. The command

.. code-block:: text

    import foo bar.baz.blah

imports the files ``foo.lean`` and ``bar/baz/blah.lean``, where the descriptions are interpreted relative to the Lean *search path*. Information as to how the search path is determined can be found on the `documentation pages <http://leanprover.github.io/documentation/>`__. By default, it includes the standard library directory, and (in some contexts) the root of the user's local project. One can also specify imports relative to the current directory; for example,

.. code-block:: text

    import .foo ..bar.baz

tells Lean to import ``foo.lean`` from the current directory and ``bar/baz.lean`` relative to the parent of the current directory.

Importing is transitive. In other words, if you import ``foo`` and ``foo`` imports ``bar``, then you also have access to the contents of ``bar``, and do not need to import it explicitly.

More on Sections
----------------

Lean provides various sectioning mechanisms to help structure a theory. We saw in :numref:`variables_and_sections` that the ``section`` command makes it possible not only to group together elements of a theory that go together, but also to declare variables that are inserted as arguments to theorems and definitions, as necessary. Remember that the point of the variable command is to declare variables for use in theorems, as in the following example:

.. code-block:: lean

    section
      variables x y : ℕ

      def double := x + x

      #check double y
      #check double (2 * x)

      theorem t1 : double (x + y) = double x + double y :=
      by simp [double]

      #check t1 y
      #check t1 (2 * x)

      theorem t2 : double (x * y) = double x * y := 
      by simp [double, add_mul]
    end

The definition of ``double`` does not have to declare ``x`` as an argument; Lean detects the dependence and inserts it automatically. Similarly, Lean detects the occurrence of ``x`` in ``t1`` and ``t2``, and inserts it automatically there, too.

Note that double does *not* have ``y`` as argument. Variables are only included in declarations where they are actually mentioned. More precisely, they must be mentioned outside of a tactic block; because variables can appear and can be renamed dynamically in a tactic proof, there is no reliable way of determining when a name used in a tactic proof refers to an element of the context in which the theorem is parsed, and Lean does not try to guess. You can manually ask Lean to include a variable in every definition in a section with the ``include`` command.

.. code-block:: lean

    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)

      include h₁ h₂
      theorem foo : x = z :=
      begin
        rw [h₁, h₂]
      end
      omit h₁ h₂

      theorem bar : x = z :=
      eq.trans h₁ h₂

      theorem baz : x = x := rfl

      #check @foo
      #check @bar
      #check @baz
    end

The ``omit`` command simply undoes the effect of the ``include``. It does not, however, prevent the arguments from being included automatically in subsequent theorems that mention them. The scope of the ``include`` statement can also be delimited by enclosing it in a section.

.. code-block:: lean

    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)

    -- BEGIN
      section include_hs
      include h₁ h₂

      theorem foo : x = z :=
      begin
        rw [h₁, h₂]
      end

      end include_hs
    -- END

      theorem bar : x = z :=
      eq.trans h₁ h₂

      theorem baz : x = x := rfl

      #check @foo
      #check @bar
      #check @baz
    end

The include command is often useful with structures that are not mentioned explicitly but meant to be inferred by type class inference, as described in :numref:`Chapter %s <type_classes>`.

It is often the case that we want to declare section variables as explicit variables but later make them implicit, or vice-versa. One can do this with a ``variables`` command that mentions these variables with the desired brackets, without repeating the type again. Once again, sections can be used to delimit scope. In the example below, the variables ``x``, ``y``, and ``z`` are marked implicit in ``foo`` but explicit in ``bar``, while ``x`` is (somewhat perversely) marked as implicit in ``baz``.

.. code-block:: lean

    section
      variables (x y z : ℕ)
      variables (h₁ : x = y) (h₂ : y = z)

      section
        variables {x y z}
        include h₁ h₂
        theorem foo : x = z :=
        begin
          rw [h₁, h₂]
        end
      end

      theorem bar : x = z :=
      eq.trans h₁ h₂

      variable {x}
      theorem baz : x = x := rfl

      #check @foo
      #check @bar
      #check @baz
    end

Using these subsequent ``variables`` commands does not change the order in which variables are inserted. It only changes the explicit / implicit annotations.

In fact, Lean has two ways of introducing local elements into the sections, namely, as ``variables`` or as ``parameters``. In the initial example in this section, the variable ``x`` is generalized immediately, so that even within the section ``double`` is a function of ``x``, and ``t1`` and ``t2`` depend explicitly on ``x``. This is what makes it possible to apply ``double`` and ``t1`` to other expressions, like ``y`` and ``2 * x``. It corresponds to the ordinary mathematical locution "in this section, let ``x`` and ``y`` range over the natural numbers." Whenever ``x`` and ``y`` occur, we assume they denote natural numbers, but we do not assume they refer to the same natural number from theorem to theorem.

Sometimes, however, we wish to *fix* a value in a section. For example, following ordinary mathematical vernacular, we might say "in this section, we fix a type, ``α``, and a binary relation ``r`` on ``α``." The notion of a ``parameter`` captures this usage:

.. code-block:: lean

    section
      parameters {α : Type} (r : α → α → Type)
      parameter  transr : ∀ {x y z}, r x y → r y z → r x z

      variables {a b c d e : α}

      theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
      transr (transr h₁ h₂) h₃

      theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) 
          (h₄ : r d e) :
        r a e :=
      transr h₁ (t1 h₂ h₃ h₄)

      #check t1
      #check t2
    end

    #check t1
    #check t2

As with variables, the parameters ``α``, ``r``, and ``transr`` are inserted as arguments to definitions and theorems as needed. But there is a difference: within the section, ``t1`` is an abbreviation for ``@t1 α r transr``, which is to say, these arguments are held fixed until the section is closed. On the plus side, this means that you do not have to specify the explicit arguments ``r`` and ``transr`` when you write ``t1 h₂ h₃ h₄``, in contrast to the previous example. But it also means that you cannot specify other arguments in their place. In this example, making ``r`` a parameter is appropriate if ``r`` is the only binary relation you want to reason about in the section. In that case, it would make sense to introduce temporary infix notation like ``≼`` for ``r``, and we will see in :numref:`notation` how to do that. On the other hand, if you want to apply your theorems to arbitrary binary relations within the section, you should make ``r`` a variable.

More on Namespaces
------------------

In Lean, identifiers are given by hierarchical *names* like ``foo.bar.baz``. We saw in :numref:`namespaces` that Lean provides mechanisms for working with hierarchical names. The command ``namespace foo`` causes ``foo`` to be prepended to the name of each definition and theorem until ``end foo`` is encountered. The command ``open foo`` then creates temporary *aliases* to definitions and theorems that begin with prefix ``foo``.

.. code-block:: lean

    namespace foo
    def bar : ℕ := 1
    end foo

    open foo

    #check bar
    #check foo.bar

It is not important that the definition of ``foo.bar`` was the result of a ``namespace`` command:

.. code-block:: lean

    def foo.bar : ℕ := 1

    open foo

    #check bar
    #check foo.bar

Although the names of theorems and definitions have to be unique, the aliases that identify them do not. For example, the standard library defines a theorem ``add_sub_cancel``, which asserts ``a + b - b = a`` in any additive group. The corresponding theorem on the natural numbers is named ``nat.add_sub_cancel``; it is not a special case of ``add_sub_cancel``, because the natural numbers do not form a group. When we open the ``nat`` namespace, the expression ``add_sub_cancel`` is overloaded, and can refer to either one. Lean tries to use type information to disambiguate the meaning in context, but you can always disambiguate by giving the full name. To that end, the string ``_root_`` is an explicit description of the empty prefix.

.. code-block:: lean

    #check add_sub_cancel
    #check nat.add_sub_cancel
    #check _root_.add_sub_cancel

We can prevent the shorter alias from being created by using the ``protected`` keyword:

.. code-block:: lean

    namespace foo
    protected def bar : ℕ := 1
    end foo

    open foo

    -- #check bar -- error
    #check foo.bar

This is often used for names like ``nat.rec`` and ``nat.rec_on``, to prevent overloading of common names.

The ``open`` command admits variations. The command

.. code-block:: lean

    open nat (succ add sub)

creates aliases for only the identifiers listed. The command

.. code-block:: lean

    open nat (hiding succ add sub)

creates aliases for everything in the ``nat`` namespace *except* the identifiers listed. The command

.. code-block:: lean

    open nat (renaming mul → times) (renaming add → plus) 
      (hiding succ sub)

creates aliases for everything in the ``nat`` namespace except ``succ`` and ``sub``, renaming ``nat.add`` to ``plus``.

It is sometimes useful to ``export`` aliases from one namespace to another, or to the top level. The command

.. code-block:: lean

    export nat (succ add sub)

creates aliases for ``succ``, ``add``, and ``sub`` in the current namespace, so that whenever the namespace is open, these aliases are available. If this command is used outside a namespace, the aliases are exported to the top level. The ``export`` command admits all the variations described above.

.. _attributes:

Attributes
----------

The main function of Lean is to translate user input to formal expressions that are checked by the kernel for correctness and then stored in the environment for later use. But some commands have other effects on the environment, either assigning attributes to objects in the environment, defining notation, or declaring instances of type classes, as described in :numref:`Chapter %s <type_classes>`. Most of these commands have global effects, which is to say, that they remain in effect not only in the current file, but also in any file that imports it. However, such commands can often be prefixed with the ``local`` modifier, which indicates that they only have effect until the current ``section`` or ``namespace`` is closed, or until the end of the current file.

In :numref:`using_the_simplifier`, we saw that theorems can be annotated with the ``[simp]`` attribute, which makes them available for use by the simplifier. The following example defines the prefix relation on lists, proves that this relation is reflexive, and assigns the ``[simp]`` attribute to that theorem.

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := 
    ∃ t, l₁ ++ t = l₂

    infix ` <+: `:50 := is_prefix

    attribute [simp]
    theorem list.is_prefix_refl (l : list α) : l <+: l :=
    ⟨[], by simp⟩

    example : [1, 2, 3] <+: [1, 2, 3] := by simp

The simplifier then proves ``[1, 2, 3] <+: [1, 2, 3]`` by rewriting it to ``true``. Lean allows the alternative annotation ``@[simp]`` before a theorem to assign the attribute:

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    infix ` <+: `:50 := is_prefix

    -- BEGIN
    @[simp]
    theorem list.is_prefix_refl (l : list α) : l <+: l :=
    ⟨[], by simp⟩
    -- END

One can also assign the attribute any time after the definition takes place:

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    infix ` <+: `:50 := is_prefix

    -- BEGIN
    theorem list.is_prefix_refl (l : list α) : l <+: l :=
    ⟨[], by simp⟩

    attribute [simp] list.is_prefix_refl
    -- END

In all these cases, the attribute remains in effect in any file that imports the one in which the declaration occurs. Adding the ``local`` modifier restricts the scope:

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    infix ` <+: `:50 := is_prefix

    -- BEGIN
    section
    local attribute [simp]
    theorem list.is_prefix_refl (l : list α) : l <+: l :=
    ⟨[], by simp⟩

    example : [1, 2, 3] <+: [1, 2, 3] := by simp
    end

    -- error: 
    -- example : [1, 2, 3] <+: [1, 2, 3] := by simp
    -- END

For another example, we can use the ``instance`` command to assign the notation ``≤`` to the `is_prefix` relation. That command, which will be explained in :numref:`Chapter %s <type_classes>`, works by assigning an ``[instance]`` attribute to the associated definition.

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    -- BEGIN
    instance list_has_le : has_le (list α) := ⟨is_prefix⟩

    theorem list.is_prefix_refl (l : list α) : l ≤ l :=
    ⟨[], by simp⟩    
    -- END

That assignment can also be made local:

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    -- BEGIN
    def list_has_le : has_le (list α) := ⟨is_prefix⟩

    section
    local attribute [instance] list_has_le

    theorem foo (l : list α) : l ≤ l := ⟨[], by simp⟩
    end

    -- error:
    -- theorem bar (l : list α) : l ≤ l := ⟨[], by simp⟩
    -- END

For yet another example, the ``reflexivity`` tactic makes use of objects in the environment that have been tagged with the ``[refl]`` attribute:

.. code-block:: lean

    variable {α : Type*}

    def is_prefix (l₁ : list α) (l₂ : list α) : Prop := ∃ t, l₁ ++ t = l₂

    infix ` <+: `:50 := is_prefix

    -- BEGIN
    @[simp, refl]
    theorem list.is_prefix_refl (l : list α) : l <+: l :=
    ⟨[], by simp⟩

    example : [1, 2, 3] <+: [1, 2, 3] := by reflexivity
    -- END

The scope of the ``[refl]`` attribute can similarly be restricted using the ``local`` modifier, as above.

In :numref:`notation` below, we will discuss Lean's mechanisms for defining notation, and see that they also support the ``local`` modifier. However, in :numref:`setting_options`, we will discuss Lean's mechanisms for setting options, which does *not* follow this pattern: options can *only* be set locally, which is to say, their scope is always restricted to the current section or current file.

More on Implicit Arguments
--------------------------

In :numref:`implicit_arguments`, we saw that if Lean displays the type of a term ``t`` as ``Π {x : α}, β x``, then the curly brackets indicate that ``x`` has been marked as an *implicit argument* to ``t``. This means that whenever you write ``t``, a placeholder, or "hole," is inserted, so that ``t`` is replaced by ``@t _``. If you don't want that to happen, you have to write ``@t`` instead.

Notice that implicit arguments are inserted eagerly. Suppose we define a function ``f (x : ℕ) {y : ℕ} (z : ℕ)`` with the arguments shown. Then, when we write the expression ``f 7`` without further arguments, it is parsed as ``f 7 _``. Lean offers a weaker annotation, ``{{y : ℕ}}``, which specifies that a placeholder should only be added *before* a subsequent explicit argument. This annotation can also be written using as ``⦃y : ℕ⦄``, where the unicode brackets are entered as ``\{{`` and ``\}}``, respectively. With this annotation, the expression ``f 7`` would be parsed as is, whereas ``f 7 3`` would be parsed as ``f 7 _ 3``, just as it would be with the strong annotation.

To illustrate the difference, consider the following example, which shows that a reflexive euclidean relation is both symmetric and transitive.

.. code-block:: lean

    -- BEGIN
    namespace hidden
    variables {α : Type} (r : α → α → Prop)

    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ {a b : α}, r a b → r b a
    definition transitive : Prop := 
      ∀ {a b c : α}, r a b → r b c → r a c
    definition euclidean  : Prop := 
      ∀ {a b c : α}, r a b → r a c → r b c

    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : 
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : 
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) rbc

    -- error:
    /-
    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : 
      transitive r :=
    th2 (th1 reflr euclr) euclr
    -/

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : 
      transitive r :=
    @th2 _ _ (@th1 _ _ reflr @euclr) @euclr
    end hidden
    -- END

The results are broken down into small steps: ``th1`` shows that a relation that is reflexive and euclidean is symmetric, and ``th2`` shows that a relation that is symmetric and euclidean is transitive. Then ``th3`` combines the two results. But notice that we have to manually disable the implicit arguments in ``th1``, ``th2``, and ``euclr``, because otherwise too many implicit arguments are inserted. The problem goes away if we use weak implicit arguments:

.. code-block:: lean

    namespace hidden
    -- BEGIN
    variables {α : Type} (r : α → α → Prop)

    definition reflexive  : Prop := ∀ (a : α), r a a
    definition symmetric  : Prop := ∀ ⦃a b : α⦄, r a b → r b a
    definition transitive : Prop := 
      ∀ ⦃a b c : α⦄, r a b → r b c → r a c
    definition euclidean  : Prop := 
      ∀ ⦃a b c : α⦄, r a b → r a c → r b c

    variable {r}

    theorem th1 (reflr : reflexive r) (euclr : euclidean r) : 
      symmetric r :=
    assume a b : α, assume : r a b,
    show r b a, from euclr this (reflr _)

    theorem th2 (symmr : symmetric r) (euclr : euclidean r) : 
      transitive r :=
    assume (a b c : α), assume (rab : r a b) (rbc : r b c),
    euclr (symmr rab) rbc

    theorem th3 (reflr : reflexive r) (euclr : euclidean r) : 
      transitive r :=
    th2 (th1 reflr euclr) euclr
    -- END
    end hidden

There is a third kind of implicit argument that is denoted with square brackets, ``[`` and ``]``. These are used for type classes, as explained in :numref:`Chapter %s <type_classes>`.

.. _notation:

Notation
--------

Identifiers in Lean can include any alphanumeric characters, including Greek characters (other than Π , Σ , and λ , which, as we have seen, have a special meaning in the dependent type theory). They can also include subscripts, which can be entered by typing ``\_`` followed by the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

.. code-block:: lean

    notation `[` a `**` b `]` := a * b + 1

    def mul_square (a b : ℕ) := a * a * b * b

    infix `<*>`:50 := mul_square

    #reduce [2 ** 3]
    #reduce 2 <*> 3

In this example, the ``notation`` command defines a complex binary notation for multiplying and adding one. The ``infix`` command declares a new infix operator, with precedence 50, which associates to the left. (More precisely, the token is given left-binding power 50.) The command ``infixr`` defines notation which associates to the right, instead.

If you declare these notations in a namespace, the notation is only available when the namespace is open. You can declare temporary notation using the keyword ``local``, in which case the notation is available in the current file, and moreover, within the scope of the current ``namespace`` or ``section``, if you are in one.

.. code-block:: lean

    local notation `[` a `**` b `]` := a * b + 1
    local infix `<*>`:50 := λ a b : ℕ, a * a * b * b

Lean's core library declares the left-binding powers of a number of common symbols.

    https://github.com/leanprover/lean/blob/master/library/init/core.lean

You are welcome to overload these symbols for your own use, but you cannot change their binding power.

You can direct the pretty-printer to suppress notation with the command ``set_option pp.notation false``. You can also declare notation to be used for input purposes only with the ``[parsing_only]`` attribute:

.. code-block:: lean

    notation [parsing_only] `[` a `**` b `]` := a * b + 1

    variables a b : ℕ
    #check [a ** b]

The output of the ``#check`` command displays the expression as ``a * b + 1``. Lean also provides mechanisms for iterated notation, such as ``[a, b, c, d, e]`` to denote a list with the indicated elements. See the discussion of ``list`` in the next chapter for an example.

The possibility of declaring parameters in a section also makes it possible to define local notation that depends on those parameters. In the example below, as long as the parameter ``m`` is fixed, we can write ``a ≡ b`` for equivalence modulo ``m``. As soon as the section is closed, however, the dependence on ``m`` becomes explicit, and the notation ``a ≡ b`` is no longer valid.

.. code-block:: lean

    namespace int

    def dvd (m n : ℤ) : Prop := ∃ k, n = m * k
    instance : has_dvd int := ⟨int.dvd⟩

    @[simp]
    theorem dvd_zero (n : ℤ) : n ∣ 0 :=
    ⟨0, by simp⟩

    theorem dvd_intro {m n : ℤ} (k : ℤ) (h : n = m * k) : m ∣ n :=
    ⟨k, h⟩

    end int

    open int

    section mod_m
      parameter (m : ℤ)
      variables (a b c : ℤ)

      definition mod_equiv := (m ∣ b - a)

      local infix ≡ := mod_equiv

      theorem mod_refl : a ≡ a :=
      show m ∣ a - a, by simp

      theorem mod_symm (h : a ≡ b) : b ≡ a :=
      by cases h with c hc; apply dvd_intro (-c); simp [eq.symm hc]

      theorem mod_trans (h₁ : a ≡ b) (h₂ : b ≡ c) : a ≡ c :=
      begin
        cases h₁ with d hd, cases h₂ with e he, 
        apply dvd_intro (d + e),
        simp [mul_add, eq.symm hd, eq.symm he]
      end
    end mod_m

    #check (mod_refl : ∀ (m a : ℤ), mod_equiv m a a)

    #check (mod_symm : ∀ (m a b : ℤ), mod_equiv m a b → 
                         mod_equiv m b a)

    #check (mod_trans :  ∀ (m a b c : ℤ), mod_equiv m a b → 
                           mod_equiv m b c → mod_equiv m a c)

Coercions
---------

In Lean, the type of natural numbers, ``nat``, is different from the type of integers, ``int``. But there is a function ``int.of_nat`` that embeds the natural numbers in the integers, meaning that we can view any natural number as an integer, when needed. Lean has mechanisms to detect and insert *coercions* of this sort.

.. code-block:: lean

    variables m n : ℕ
    variables i j : ℤ

    #check i + m      -- i + ↑m : ℤ
    #check i + m + j  -- i + ↑m + j : ℤ
    #check i + m + n  -- i + ↑m + ↑n : ℤ

Notice that the output of the ``#check`` command shows that a coercion has been inserted by printing an arrow. The latter is notation for the function ``coe``; you can type the unicode arrow with ``\u`` or use ``coe`` instead. In fact, when the order of arguments is different, you have to insert the coercion manually, because Lean does not recognize the need for a coercion until it has already parsed the earlier arguments.

.. code-block:: lean

    variables m n : ℕ
    variables i j : ℤ

    -- BEGIN
    #check ↑m + i        -- ↑m + i : ℤ
    #check ↑(m + n) + i  -- ↑(m + n) + i : ℤ
    #check ↑m + ↑n + i   -- ↑m + ↑n + i : ℤ
    -- END

In fact, Lean allows various kinds of coercions using type classes; for details, see :numref:`coercions_using_type_classes`.

Displaying Information
----------------------

There are a number of ways in which you can query Lean for information about its current state and the objects and theorems that are available in the current context. You have already seen two of the most common ones, ``#check`` and ``#reduce``. Remember that ``#check`` is often used in conjunction with the ``@`` operator, which makes all of the arguments to a theorem or definition explicit. In addition, you can use the ``#print`` command to get information about any identifier. If the identifier denotes a definition or theorem, Lean prints the type of the symbol, and its definition. If it is a constant or an axiom, Lean indicates that fact, and shows the type.

.. code-block:: lean

    -- examples with equality
    #check eq
    #check @eq
    #check eq.symm
    #check @eq.symm

    #print eq.symm

    -- examples with and
    #check and
    #check and.intro
    #check @and.intro

    -- a user-defined function
    def foo {α : Type} (x : α) : α := x

    #check foo
    #check @foo
    #reduce foo
    #reduce (foo nat.zero)
    #print foo

There are other useful ``#print`` commands:

.. code-block:: text

    #print definition             : display definition
    #print inductive              : display an inductive type and its constructors
    #print notation               : display all notation
    #print notation <tokens>      : display notation using any of the tokens
    #print axioms                 : display assumed axioms
    #print options                : display options set by user
    #print prefix <namespace>     : display all declarations in the namespace
    #print classes                : display all classes
    #print instances <class name> : display all instances of the given class
    #print fields <structure>     : display all fields of a structure

We will discuss inductive types, structures, classes, instances in the next four chapters. Here are examples of how these commands are used:

.. code-block:: lean

    #print notation
    #print notation + * -
    #print axioms
    #print options
    #print prefix nat
    #print prefix nat.le
    #print classes
    #print instances ring
    #print fields ring

The behavior of the generic print command is determined by its argument, so that the following pairs of commands all do the same thing.

.. code-block:: lean

    #print list.append
    #print definition list.append

    #print +
    #print notation +

    #print nat
    #print inductive nat

    #print group
    #print inductive group

Moreover, both ``#print group`` and ``#print inductive group`` recognize that a group is a structure (see :numref:`Chapter %s <structures_and_records>`), and so print the fields as well.

.. _setting_options:

Setting Options
---------------

Lean maintains a number of internal variables that can be set by users to control its behavior. The syntax for doing so is as follows:

.. code-block:: text

    set_option <name> <value>

One very useful family of options controls the way Lean's *pretty- printer* displays terms. The following options take an input of true or false:

.. code-block:: text

    pp.implicit  : display implicit arguments
    pp.universes : display hidden universe parameters
    pp.coercions : show coercions
    pp.notation  : display output using defined notations
    pp.beta      : beta reduce terms before displaying them

As an example, the following settings yield much longer output:

.. code-block:: lean

    set_option pp.implicit true
    set_option pp.universes true
    set_option pp.notation false
    set_option pp.numerals false

    #check 2 + 2 = 4
    #reduce (λ x, x + 2) = (λ x, x + 3)
    #check (λ x, x + 1) 1

The command ``set_option pp.all true`` carries out these settings all at once, whereas ``set_option pp.all false`` reverts to the previous values. Pretty printing additional information is often very useful when you are debugging a proof, or trying to understand a cryptic error message. Too much information can be overwhelming, though, and Lean's defaults are generally sufficient for ordinary interactions.

By default, the pretty-printer does not reduce applied lambda-expressions, but this is sometimes useful. The ``pp.beta`` option controls this feature.

.. code-block:: lean

    set_option pp.beta true
    #check (λ x, x + 1) 1

.. _elaboration_hints:

Elaboration Hints
-----------------

When you ask Lean to process an expression like ``λ x y z, f (x + y) z``, you are leaving information implicit. For example, the types of ``x``, ``y``, and ``z`` have to be inferred from the context, the notation ``+`` may be overloaded, and there may be implicit arguments to ``f`` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as *type class resolution*. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function ``f`` has type ``Π {α : Type}, α → α → α`` and Lean is trying to parse the expression ``f n``, where ``n`` can be inferred to have type ``nat``. Then it is clear that the implicit argument ``α`` has to be ``nat``. However, some inference problems are *higher order*. For example, the substitution operation for equality, ``eq.subst``, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α}, 
                 a = b → p a → p b

Now suppose we are given ``a b : ℕ`` and ``h₁ : a = b`` and ``h₂ : a * b > a``. Then, in the expression ``eq.subst h₁ h₂``, ``P`` could be any of the following:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

In other words, our intent may be to replace either the first or second ``a`` in ``h₂``, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute ``[reducible]``, ``[semireducible]``, or ``[irreducible]``. Definitions are marked ``[semireducible]`` by default. A definition with the ``[reducible]`` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the ``[irreducible]`` attribute. Theorems are marked ``[irreducible]`` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the ``local`` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked ``[elab_with_expected_type]``, ``[elab_simple]``. or ``[elab_as_eliminator]``. When applied to a definition ``f``, these bear on elaboration of an expression ``f a b c ...`` in which ``f`` is applied to arguments. With the default attribute, ``[elab_with_expected_type]``, the arguments ``a``, ``b``, ``c``, ... are elaborating using information about their expected type, inferred from ``f`` and the previous arguments. In contrast, with ``[elab_simple]``, the arguments are elaborated from left to right without propagating information about their types. The last attribute, ``[elab_as_eliminator]``, is commonly used for eliminators like recursors, induction principles, and ``eq.subst``. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the ``local`` modifier to limit their scope. Moreover, using the ``@`` symbol in front of an identifier in an expression instructs the elaborator to use the ``[elab_simple]`` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, ``@@``, which leaves parameters before the first higher-order parameter explicit. For example, ``@@eq.subst`` leaves the type of the equation implicit, but makes the context of the substitution explicit.

Using the Library
-----------------

To use Lean effectively you will inevitably need to make use of definitions and theorems in the library. Recall that the ``import`` command at the beginning of a file imports previously compiled results from other files, and that importing is transitive; if you import ``foo`` and ``foo`` imports ``bar``, then the definitions and theorems from ``bar`` are available to you as well. But the act of opening a namespace, which provides shorter names, does not carry over. In each file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library and its contents, so you know what theorems, definitions, notations, and resources are available to you. Below we will see that Lean's editor modes can also help you find things you need, but studying the contents of the library directly is often unavoidable. Lean's standard library can be found online, on github:

    https://github.com/leanprover/lean/tree/master/library

You can see the contents of the directories and files using github's browser interface. If you have installed Lean on your own computer, you can find the library in the ``lean`` folder, and explore it with your file manager. Comment headers at the top of each file provide additional information.

Lean's library developers follow general naming guidelines to make it easier to guess the name of a theorem you need, or to find it using tab completion in editors with a Lean mode that supports this, which is discussed in the next section. Identifiers are generally ``snake_case``, which is to say, they are composed of words written in lower case separated by underscores. For the most part, we rely on descriptive names. Often the name of theorem simply describes the conclusion:

.. code-block:: lean

    open nat

    #check succ_ne_zero
    #check @mul_zero
    #check @mul_one
    #check @sub_add_eq_add_sub
    #check @le_iff_lt_or_eq

If only a prefix of the description is enough to convey the meaning, the name may be made even shorter:

.. code-block:: lean

    open nat

    -- BEGIN
    #check @neg_neg
    #check pred_succ
    -- END

Sometimes, to disambiguate the name of theorem or better convey the intended reference, it is necessary to describe some of the hypotheses. The word "of" is used to separate these hypotheses:

.. code-block:: lean

    #check @nat.lt_of_succ_le
    #check @lt_of_not_ge
    #check @lt_of_le_of_ne
    #check @add_lt_add_of_lt_of_le

Sometimes the word "left" or "right" is helpful to describe variants of a theorem.

.. code-block:: lean

    #check @add_le_add_left
    #check @add_le_add_right

We can also use the word "self" to indicate a repeated argument:

.. code-block:: lean

    #check mul_inv_self
    #check neg_add_self

Remember that identifiers in Lean can be organized into hierarchical namespaces. For example, the theorem named ``lt_of_succ_le`` in the namespace ``nat`` has full name ``nat.lt_of_succ_le``, but the shorter name is made available by the command ``open nat``. We will see in :numref:`Chapter %s <inductive_types>` and :numref:`Chapter %s <structures_and_records>` that defining structures and inductive data types in Lean generates associated operations, and these are stored in a namespace with the same name as the type under definition. For example, the product type comes with the following operations:

.. code-block:: lean

    #check @prod.mk
    #check @prod.fst
    #check @prod.snd
    #check @prod.rec

The first is used to construct a pair, whereas the next two, ``prod.fst`` and ``prod.snd``, project the two elements. The last, ``prod.rec``, provides another mechanism for defining functions on a product in terms of a function on the two components. Names like ``prod.rec`` are *protected*, which means that one has to use the full name even when the ``prod`` namespace is open.

With the propositions as types correspondence, logical connectives are also instances of inductive types, and so we tend to use dot notation for them as well:

.. code-block:: lean

    #check @and.intro
    #check @and.elim
    #check @and.left
    #check @and.right
    #check @or.inl
    #check @or.inr
    #check @or.elim
    #check @exists.intro
    #check @exists.elim
    #check @eq.refl
    #check @eq.subst
