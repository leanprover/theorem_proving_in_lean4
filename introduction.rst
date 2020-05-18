.. _introduction:

Introduction
============

Computers and Theorem Proving
-----------------------------

*Formal verification* involves the use of logical and computational methods to establish claims that are expressed in precise mathematical terms. These can include ordinary mathematical theorems, as well as claims that pieces of hardware or software, network protocols, and mechanical and hybrid systems meet their specifications. In practice, there is not a sharp distinction between verifying a piece of mathematics and verifying the correctness of a system: formal verification requires describing hardware and software systems in mathematical terms, at which point establishing claims as to their correctness becomes a form of theorem proving. Conversely, the proof of a mathematical theorem may require a lengthy computation, in which case verifying the truth of the theorem requires verifying that the computation does what it is supposed to do.

The gold standard for supporting a mathematical claim is to provide a proof, and twentieth-century developments in logic show most if not all conventional proof methods can be reduced to a small set of axioms and rules in any of a number of foundational systems. With this reduction, there are two ways that a computer can help establish a claim: it can help find a proof in the first place, and it can help verify that a purported proof is correct.

*Automated theorem proving* focuses on the "finding" aspect. Resolution theorem provers, tableau theorem provers, fast satisfiability solvers, and so on provide means of establishing the validity of formulas in propositional and first-order logic. Other systems provide search procedures and decision procedures for specific languages and domains, such as linear or nonlinear expressions over the integers or the real numbers. Architectures like SMT ("satisfiability modulo theories") combine domain-general search methods with domain-specific procedures. Computer algebra systems and specialized mathematical software packages provide means of carrying out mathematical computations, establishing mathematical bounds, or finding mathematical objects. A calculation can be viewed as a proof as well, and these systems, too, help establish mathematical claims.

Automated reasoning systems strive for power and efficiency, often at the expense of guaranteed soundness. Such systems can have bugs, and it can be difficult to ensure that the results they deliver are correct. In contrast, *interactive theorem proving* focuses on the "verification" aspect of theorem proving, requiring that every claim is supported by a proof in a suitable axiomatic foundation. This sets a very high standard: every rule of inference and every step of a calculation has to be justified by appealing to prior definitions and theorems, all the way down to basic axioms and rules. In fact, most such systems provide fully elaborated "proof objects" that can be communicated to other systems and checked independently. Constructing such proofs typically requires much more input and interaction from users, but it allows us to obtain deeper and more complex proofs.

The *Lean Theorem Prover* aims to bridge the gap between interactive and automated theorem proving, by situating automated tools and methods in a framework that supports user interaction and the construction of fully specified axiomatic proofs. The goal is to support both mathematical reasoning and reasoning about complex systems, and to verify claims in both domains.

Lean's underlying logic has a computational interpretation, and Lean can be viewed equally well as a programming language. More to the point, it can be viewed as a system for writing programs with a precise semantics, as well as reasoning about the functions that the programs compute. Lean also has mechanisms to serve as its own *metaprogramming language*, which means that one can implement automation and extend the functionality of Lean using Lean itself. These aspects of Lean are explored in a companion tutorial to this one, `Programming in Lean <https://leanprover.github.io/programming_in_lean>`__, though computational aspects of the system will make an appearance here.

About Lean
----------

The *Lean* project was launched by Leonardo de Moura at Microsoft Research Redmond in 2013. It is an ongoing, long-term effort, and much of the potential for automation will be realized only gradually over time. Lean is released under the Apache 2.0 license, a permissive open source license that permits others to use and extend the code and mathematical libraries freely.

There are currently two ways to use Lean. The first is to run it from the web: a Javascript version of Lean, a standard library of definitions and theorems, and an editor are actually downloaded to your browser and run there. This provides a quick and convenient way to begin experimenting with the system.

The second way to use Lean is to install and run it natively on your computer. The native version is much faster than the web version, and is more flexible in other ways, too. Special modes in Visual Studio Code (VS Code for short) and Emacs offer powerful support for writing and debugging proofs, and is much better suited for serious use. The source code, and instructions for building Lean, are available at https://github.com/leanprover/lean/.

This tutorial describes the current version of Lean, known as Lean 3. A prior version, Lean 2, had special support for homotopy type theory. You can find Lean 2 and the HoTT library at https://github.com/leanprover/lean2/. The tutorial for that version of Lean is at https://leanprover.github.io/tutorial/.

About this Book
---------------

This book is designed to teach you to develop and verify proofs in Lean. Much of the background information you will need in order to do this is not specific to Lean at all. To start with, we will explain the logical system that Lean is based on, a version of *dependent type theory* that is powerful enough to prove almost any conventional mathematical theorem, and expressive enough to do it in a natural way. More specifically, Lean is based on a version of a system known as the *Calculus of Constructions* [CoHu88]_ with *inductive types* [Dybj94]_. We will explain not only how to define mathematical objects and express mathematical assertions in dependent type theory, but also how to use it as a language for writing proofs.

Because fully detailed axiomatic proofs are so complicated, the challenge of theorem proving is to have the computer fill in as many of the details as possible. We will describe various methods to support this in dependent type theory. For example, we will discuss term rewriting, and Lean's automated methods for simplifying terms and expressions automatically. Similarly, we will discuss methods of *elaboration* and *type inference*, which can be used to support flexible forms of algebraic reasoning.

Finally, of course, we will discuss features that are specific to Lean, including the language with which you can communicate with the system, and the mechanisms Lean offers for managing complex theories and data.

Throughout the text you will find examples of Lean code like the one below:

.. code-block:: lean

    -- BEGIN
    theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
    assume hpq : p ∧ q,
    have hp : p, from and.left hpq,
    have hq : q, from and.right hpq,
    show q ∧ p, from and.intro hq hp
    -- END

If you are reading the book online, you will see a button that reads "try it!" Pressing the button opens up a tab with a Lean editor, and copies the example with enough surrounding context to make the example compile correctly. You can type things into the editor and modify the examples, and Lean will check the results and provide feedback continuously as you type. We recommend running the examples and experimenting with the code on your own as you work through the chapters that follow.

Acknowledgments
---------------

This tutorial is an open access project maintained on Github. Many people have contributed to the effort, providing corrections, suggestions, examples, and text. We are grateful to Ulrik Buchholz, Kevin Buzzard, Mario Carneiro, Nathan Carter, Eduardo Cavazos, Amine Chaieb, Joe Corneli, William DeMeo, Marcus Klaas de Vries, Ben Dyer, Gabriel Ebner, Anthony Hart, Simon Hudon, Sean Leather, Assia Mahboubi, Gihan Marasingha, Patrick Massot, Christopher John Mazey, Sebastian Ullrich, Floris van Doorn, Daniel Velleman, and Théo Zimmerman for their contributions, and we apologize to those whose names we have inadvertently omitted.

.. [CoHu88] Thierry Coquand and Gerard Huet. The calculus of constructions. Inf. Comput., 76(2-3):95–120, February 1988.

.. [Dybj94] Peter Dybjer. Inductive families. Formal Asp. Comput., 6(4):440–465, 1994.
