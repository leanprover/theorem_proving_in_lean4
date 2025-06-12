import VersoManual
import TPiL.Examples

open Verso.Genre
open Manual hiding tactic
open TPiL

#doc (Manual) "Tactics" =>

In this chapter, we describe an alternative approach to constructing
proofs, using _tactics_.  A proof term is a representation of a
mathematical proof; tactics are commands, or instructions, that
describe how to build such a proof. Informally, you might begin a
mathematical proof by saying “to prove the forward direction, unfold
the definition, apply the previous lemma, and simplify.” Just as these
are instructions that tell the reader how to find the relevant proof,
tactics are instructions that tell Lean how to construct a proof
term. They naturally support an incremental style of writing proofs,
in which you decompose a proof and work on goals one step at a time.

We will describe proofs that consist of sequences of tactics as
“tactic-style” proofs, to contrast with the ways of writing proof
terms we have seen so far, which we will call “term-style”
proofs. Each style has its own advantages and disadvantages. For
example, tactic-style proofs can be harder to read, because they
require the reader to predict or guess the results of each
instruction. But they can also be shorter and easier to
write. Moreover, tactics offer a gateway to using Lean's automation,
since automated procedures are themselves tactics.

# Entering Tactic Mode


:::leanFirst
Conceptually, stating a theorem or introducing a {kw}`have` statement
creates a goal, namely, the goal of constructing a term with the
expected type. For example, the following creates the goal of
constructing a term of type {leanRef}`p ∧ q ∧ p`, in a context with constants
{leanRef}`p q : Prop`, {leanRef}`hp : p` and {leanRef}`hq : q`:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  --                                   PROOF_STATE: X      ^
  sorry
```
:::

You can write this goal as follows:

```proofState X
  p: Prop
  q: Prop
  hp: p
  hq: q
⊢ p ∧ q ∧ p
```


Indeed, if you replace the “sorry” by an underscore in the example
above, Lean will report that it is exactly this goal that has been
left unsolved.

Ordinarily, you meet such a goal by writing an explicit term. But
wherever a term is expected, Lean allows us to insert instead a
{lit}`by <tactics>` block, where {lit}`<tactics>` is a sequence of commands,
separated by semicolons or line breaks. You can prove the theorem above
in that way:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp
```

We often put the {kw}`by` keyword on the preceding line, and write the
example above as:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
-- ^ PROOF_STATE: intro
  exact hp
  apply And.intro
  exact hq
  exact hp
```

The {leanRef}`apply` tactic applies an expression, viewed as denoting a
function with zero or more arguments. It unifies the conclusion with
the expression in the current goal, and creates new goals for the
remaining arguments, provided that no later arguments depend on
them. In the example above, the command {leanRef}`apply And.intro` yields two
subgoals:

```proofState intro
case left =>
  p: Prop
  q: Prop
  hp: p
  hq: q
⊢ p

case right =>
  p: Prop
  q: Prop
  hp: p
  hq: q
⊢ q ∧ p
```

The first goal is met with the command {leanRef}`exact hp`. The {leanRef}`exact`
command is just a variant of {leanRef}`apply` which signals that the
expression given should fill the goal exactly. It is good form to use
it in a tactic proof, since its failure signals that something has
gone wrong. It is also more robust than {leanRef}`apply`, since the
elaborator takes the expected type, given by the target of the goal,
into account when processing the expression that is being applied. In
this case, however, {leanRef}`apply` would work just as well.

You can see the resulting proof term with the {kw}`#print` command:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
------
#print test
```

::: TODO
Check these. Vim?
:::
You can write a tactic script incrementally. In VS Code, you can open
a window to display messages by pressing {kbd}[`Ctrl` `Shift` `Enter`], and
that window will then show you the current goal whenever the cursor is
in a tactic block. If the proof is incomplete, the token {kw}`by` is
decorated with a red squiggly line, and the error message contains the
remaining goals.

Tactic commands can take compound expressions, not just single
identifiers. The following is a shorter version of the preceding
proof:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp
```

Unsurprisingly, it produces exactly the same proof term:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
 apply And.intro hp
 exact And.intro hq hp
------
#print test
```

Multiple tactic applications can be written in a single line by concatenating with a semicolon.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp
```

Tactics that may produce multiple subgoals often tag them. For
example, the tactic {leanRef}`apply And.intro` tagged the first subgoal as
{goal intro}`left`, and the second as {goal intro}`right`. In the case of the {leanRef}`apply`
tactic, the tags are inferred from the parameters' names used in the
{leanRef}`And.intro` declaration. You can structure your tactics using the
notation {kw}`case`{lit}` <tag> => <tactics>`. The following is a structured
version of our first tactic proof in this chapter.

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
```

:::leanFirst

You can solve the subgoal {goal intro2}`right` before {goal intro2}`left` using the {leanRef}`case`
notation:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  -- ^ PROOF_STATE: intro2
  case right =>
    apply And.intro
    case left => exact hq
  --          ^ PROOF_STATE: leftBranch
    case right => exact hp
  case left => exact hp
```
:::

Note that Lean hides the other goals inside the {leanRef}`case` block. After {leanRef}`case left =>`,
the proof state is:

```proofState leftBranch
  p: Prop
  q: Prop
  hp: p
  hq: q
⊢ q
```

We say that {leanRef}`case` is “focusing” on the selected goal.  Moreover, Lean flags an error
if the selected goal is not fully solved at the end of the {leanRef}`case`
block.

For simple subgoals, it may not be worth selecting a subgoal using its
tag, but you may still want to structure the proof. Lean also provides
the “bullet” notation {lit}`. <tactics>` (or {lit}`· <tactics>`) for
structuring proofs:

```lean
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
```

# Basic Tactics

:::leanFirst
In addition to {leanRef}`apply` and {leanRef}`exact`, another useful tactic is
{leanRef}`intro`, which introduces a hypothesis. What follows is an example
of an identity from propositional logic that we proved in a previous
chapter, now proved using tactics.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
```
:::

The {leanRef}`intro` command can more generally be used to introduce a variable of any type:

```lean
example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
```

You can use it to introduce several variables:

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁
```

:::setup
````
variable {α : Sort u} {p : Prop} {e : p}
````

As the {leanRef}`apply` tactic is a command for constructing function
applications interactively, the {leanRef}`intro` tactic is a command for
constructing function abstractions interactively (i.e., terms of the
form {lean type:="∀ (x : α), p"}`fun x => e`).  As with lambda abstraction notation, the
{leanRef}`intro` tactic allows us to use an implicit {kw}`match`.
:::

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩
```

You can also provide multiple alternatives like in the {kw}`match` expression.

```lean
example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩
```

::::leanFirst
The {leanRef}`intros` tactic can be used without any arguments, in which
case, it chooses names and introduces as many variables as it can. You
will see an example of this in a moment.

:::leanFirst
The {leanRef}`assumption` tactic looks through the assumptions in context of
the current goal, and if there is one matching the conclusion, it
applies it.

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃
```
:::

It will unify metavariables in the conclusion if necessary:

```lean
example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃
```

The following example uses the {leanRef}`intros` command to introduce the three variables and two hypotheses automatically:

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption
```
::::

:::leanFirst
Note that names automatically generated by Lean are inaccessible by default. The motivation is to
ensure your tactic proofs do not rely on automatically generated names, and are consequently more robust.
However, you can use the combinator {leanRef}`unhygienic` to disable this restriction.

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1
```
:::

:::leanFirst
You can also use the {leanRef}`rename_i` tactic to rename the most recent inaccessible names in your context.
In the following example, the tactic {leanRef}`rename_i h1 _ h2` renames two of the last three hypotheses in
your context.

```lean
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
```
:::

:::leanFirst
The {leanRef}`rfl` tactic solves goals that are reflexive relations applied to definitionally equal arguments.
Equality is reflexive:

```lean
example (y : Nat) : (fun x : Nat => 0) y = 0 := by
  rfl
```
:::

:::leanFirst
The {leanRef}`repeat` combinator can be used to apply a tactic several times:

```lean
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption
```
:::

:::leanFirst
Another tactic that is sometimes useful is the {leanRef}`revert` tactic,
which is, in a sense, an inverse to {leanRef}`intro`:

```lean
example (x : Nat) : x = x := by
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterRevertIntro
  rfl
```

After {leanRef}`revert x`, the proof state is:

```proofState afterRevert
⊢ ∀ (x : Nat), x = x
```

After {leanRef}`intro y`, it is:

```proofState afterRevertIntro
  y: Nat
⊢ y = y
```

:::

Moving a hypothesis into the goal yields an implication:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- ^ PROOF_STATE: afterRevertH
  intro h₁
  -- ^ PROOF_STATE: afterRevertHIntro
  -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption
```

After {leanRef}`revert h`, the proof state is:

```proofState afterRevertH
  x: Nat
  y: Nat
⊢ x = y → y = x
```

After {leanRef}`intro h₁`, it is:

```proofState afterRevertHIntro
  x: Nat
  y: Nat
  h₁: x = y
⊢ y = x
```

:::leanFirst
But {leanRef}`revert` is even more clever, in that it will revert not only an
element of the context but also all the subsequent elements of the
context that depend on it. For example, reverting {leanRef (in := "revert x")}`x` in the example
above brings {leanRef}`h` along with it:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- ^ PROOF_STATE: afterRevertXH
  intros
  apply Eq.symm
  assumption
```

After {leanRef}`revert x`, the goal is:

```proofState afterRevertXH
  y: Nat
⊢ ∀ (x : Nat), x = y → y = x
```

:::

You can also revert multiple elements of the context at once:

```lean
example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- ^ PROOF_STATE: revertXY
  intros
  apply Eq.symm
  assumption
```

After {leanRef}`revert x y`, the goal is:

```proofState revertXY
⊢ ∀ (x y : Nat), x = y → y = x
```

:::leanFirst
You can only {leanRef}`revert` an element of the local context, that is, a
local variable or hypothesis. But you can replace an arbitrary
expression in the goal by a fresh variable using the {leanRef}`generalize`
tactic:

```lean showProofStates:="afterGen afterRevert afterIntro"
example : 3 = 3 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  revert x
  -- ^ PROOF_STATE: afterRevert
  intro y
  -- ^ PROOF_STATE: afterIntro
  rfl
```

In particular, after {leanRef}`generalize`, the goal is

```proofState afterGen
  x: Nat
⊢ x = x
```

:::

The mnemonic in the notation above is that you are generalizing the
goal by setting {leanRef}`3` to an arbitrary variable {leanRef in:="revert x"}`x`. Be careful: not
every generalization preserves the validity of the goal. Here,
{leanRef}`generalize` replaces a goal that could be proved using
{tactic}`rfl` with one that is not provable:

```lean showProofStates := "afterGen"
example : 2 + 3 = 5 := by
  generalize 3 = x
  -- ^ PROOF_STATE: afterGen
  sorry
```

In this example, the {leanRef}`sorry` tactic is the analogue of the {lean}`sorry`
proof term. It closes the current goal, producing the usual warning
that {lean}`sorry` has been used. To preserve the validity of the previous
goal, the {leanRef}`generalize` tactic allows us to record the fact that
{leanRef}`3` has been replaced by {leanRef}`x`. All you need to do is to provide a
label, and {leanRef}`generalize` uses it to store the assignment in the local
context:

```lean
example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- ^ PROOF_STATE: afterGen
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]
```

Following {leanRef}`generalize h : 3 = x`, {leanRef}`h` is a proof that {leanRef}`3 = x`:

```proofState afterGen
  x: Nat
  h: 3 = x
⊢ 2 + x = 5
```

Here the rewriting tactic {leanRef}`rw` uses {leanRef}`h` to replace
{leanRef}`x` by {leanRef}`3` again. The {leanRef}`rw` tactic will be discussed below.

# More Tactics

:::leanFirst
Some additional tactics are useful for constructing and destructing
propositions and data. For example, when applied to a goal of the form
{leanRef}`p ∨ q`, you use tactics such as {leanRef}`apply Or.inl` and
{leanRef}`apply Or.inr`.  Conversely, the {leanRef}`cases` tactic can be used to decompose a
disjunction:

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
```
:::

Note that the syntax is similar to the one used in {kw}`match` expressions.
The new subgoals can be solved in any order:

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp
```

You can also use a (unstructured) {leanRef}`cases` without the {leanRef}`with` and a tactic
for each alternative:

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
```

The (unstructured) {leanRef}`cases` is particularly useful when you can close several
subgoals using the same tactic:

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption
```

You can also use the combinator {lit}`tac1 `{tactic}`<;>`{lit}` tac2` to apply {lit}`tac2` to each
subgoal produced by tactic {lit}`tac1`:

```lean
example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
```

:::leanFirst
You can combine the unstructured {leanRef}`cases` tactic with the {leanRef}`case` and {leanRef}`.` notation:

```lean
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption
```
:::


The {leanRef}`cases` tactic can also be used to
decompose a conjunction:

```lean
example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp
  --             ^ PROOF_STATE: afterIntroCase
```


In this example, there is only one goal after the {leanRef}`cases` tactic is
applied, with {leanRef}`h`{lit}` : `{leanRef}`p ∧ q` replaced by a pair of assumptions,
{leanRef}`hp`{lit}` : `{leanRef}`p` and {leanRef}`hq`{lit}` : `{leanRef}`q`:

```proofState afterIntroCase
case intro =>
  p: Prop
  q: Prop
  hp: p
  hq: q
⊢ q ∧ p
```

The {leanRef}`constructor` tactic applies the unique
constructor for conjunction, {lean}`And.intro`.

With these tactics, an
example from the previous section can be rewritten as follows:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr
```

You will see in {ref "inductive-types"}[Chapter Inductive Types] that
these tactics are quite general. The {leanRef}`cases` tactic can be used to
decompose any element of an inductively defined type; {leanRef}`constructor`
always applies the first applicable constructor of an inductively defined type.
For example, you can use {leanRef}`cases` and {leanRef}`constructor` with an existential quantifier:

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px
```

Here, the {leanRef}`constructor` tactic leaves the first component of the
existential assertion, the value of {leanRef}`x`, implicit. It is represented
by a metavariable, which should be instantiated later on. In the
previous example, the proper value of the metavariable is determined
by the tactic {leanRef}`exact px`, since {leanRef}`px` has type {leanRef}`p x`. If you want
to specify a witness to the existential quantifier explicitly, you can
use the {tactic}`exists` tactic instead:

```lean
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px
```

Here is another example:

```lean
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
```

These tactics can be used on data just as well as propositions. In the
next example, they are used to define functions which swap the
components of the product and sum types:

```lean
def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption
```

Note that up to the names we have chosen for the variables, the
definitions are identical to the proofs of the analogous propositions
for conjunction and disjunction. The {leanRef}`cases` tactic will also do a
case distinction on a natural number:

```lean
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero    => exact h₀
  | succ m' => exact h₁ m'
```

The {leanRef}`cases` tactic, and its companion, the {tactic}`induction` tactic, are discussed in greater detail in
the {ref "tactics-for-inductive-types"}[Tactics for Inductive Types] section.

:::leanFirst
The {leanRef}`contradiction` tactic searches for a contradiction among the hypotheses of the current goal:

```lean
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction
```
:::

:::leanFirst
You can also use {tactic}`match` in tactic blocks.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr
```
:::

:::leanFirst
You can “combine” {leanRef}`intro` with {tactic}`match` and write the previous examples as follows:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption
```
:::

# Structuring Tactic Proofs

Tactics often provide an efficient way of building a proof, but long
sequences of instructions can obscure the structure of the
argument. In this section, we describe some means that help provide
structure to a tactic-style proof, making such proofs more readable
and robust.

:::leanFirst
One thing that is nice about Lean's proof-writing syntax is that it is
possible to mix term-style and tactic-style proofs, and pass between
the two freely. For example, the tactics {leanRef}`apply` and {leanRef}`exact`
expect arbitrary terms, which you can write using {kw}`have`, {kw}`show`,
and so on. Conversely, when writing an arbitrary Lean term, you can
always invoke the tactic mode by inserting a {kw}`by`
block. The following is a somewhat toy example:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
```
:::

The following is a more natural example:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩
```

:::leanFirst
In fact, there is a {tactic}`show` tactic, which is similar to the
{kw}`show` expression in a proof term. It simply declares the type of the
goal that is about to be solved, while remaining in tactic
mode.

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩
```
:::

The {tactic}`show` tactic can actually be used to rewrite a goal to something definitionally equivalent:

```lean
example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl
```

There is also a {tactic}`have` tactic, which introduces a new subgoal, just as when writing proof terms:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr
```

:::leanFirst
As with proof terms, you can omit the label in the {tactic}`have` tactic, in
which case, the default label {leanRef}`this` is used:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this
```
:::

:::leanFirst
The types in a {tactic}`have` tactic can be omitted, so you can write
{lit}`have hp := h.left` and {lit}`have hqr := h.right`.  In fact, with this
notation, you can even omit both the type and the label, in which case
the new fact is introduced with the label {leanRef}`this`:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this
```
:::

Lean also has a {tactic}`let` tactic, which is similar to the {tactic}`have`
tactic, but is used to introduce local definitions instead of
auxiliary facts. It is the tactic analogue of a {kw}`let` in a proof
term:

```lean
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
```

As with {tactic}`have`, you can leave the type implicit by writing
{lit}`let a := 3 * 2`. The difference between {tactic}`let` and {tactic}`have` is that
{tactic}`let` introduces a local definition in the context, so that the
definition of the local declaration can be unfolded in the proof.

We have used {leanRef}`.` to create nested tactic blocks.  In a nested block,
Lean focuses on the first goal, and generates an error if it has not
been fully solved at the end of the block. This can be helpful in
indicating the separate proofs of multiple subgoals introduced by a
tactic. The notation {leanRef}`.` is whitespace sensitive and relies on the indentation
to detect whether the tactic block ends. Alternatively, you can
define tactic blocks using curly braces and semicolons:

```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }
```

It is useful to use indentation to structure proof: every time a tactic
leaves more than one subgoal, we separate the remaining subgoals by
enclosing them in blocks and indenting.  Thus if the application of
theorem {lit}`foo` to a single goal produces four subgoals, one would
expect the proof to look like this:

```
  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>
```

or

```
  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>
```

or

```
  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
```

# Tactic Combinators

_Tactic combinators_ are operations that form new tactics from old
ones. A sequencing combinator is already implicit in the {kw}`by` block:

```lean
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption
```

Here, {leanRef}`apply Or.inl; assumption` is functionally equivalent to a
single tactic which first applies {leanRef}`apply Or.inl` and then applies
{leanRef}`assumption`.

In {lit}`t₁ `{tactic}`<;>`{lit}` t₂`, the {leanRef}`<;>` operator provides a _parallel_ version of the sequencing operation:
{lit}`t₁` is applied to the current goal, and then {lit}`t₂` is applied to _all_ the resulting subgoals:

```lean
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption
```

This is especially useful when the resulting goals can be finished off
in a uniform way, or, at least, when it is possible to make progress
on all of them uniformly.

The {tactic}`first`{lit}` | t₁ | t₂ | ... | tₙ` applies each {lit}`tᵢ` until one succeeds, or else fails:

```lean
example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption
```

In the first example, the left branch succeeds, whereas in the second one, it is the right one that succeeds.
In the next three examples, the same compound tactic succeeds in each case:

```lean
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
```

The tactic tries to solve the left disjunct immediately by assumption;
if that fails, it tries to focus on the right disjunct; and if that
doesn't work, it invokes the assumption tactic.

:::leanFirst
You will have no doubt noticed by now that tactics can fail. Indeed,
it is the “failure” state that causes the _first_ combinator to
backtrack and try the next tactic. The {leanRef}`try` combinator builds a
tactic that always succeeds, though possibly in a trivial way:
{tactic}`try`{lit}` t` executes {lit}`t` and reports success, even if {lit}`t` fails. It is
equivalent to {tactic}`first`{lit}` | t | `{tactic}`skip`, where {tactic}`skip` is a tactic that does
nothing (and succeeds in doing so). In the next example, the second
{leanRef}`constructor` succeeds on the right conjunct {leanRef}`q ∧ r` (remember that
disjunction and conjunction associate to the right) but fails on the
first. The {leanRef}`try` tactic ensures that the sequential composition
succeeds:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
```
:::

Be careful: {tactic}`repeat`{lit}` (`{tactic}`try`{lit}` t)` will loop forever, because the inner tactic never fails.

In a proof, there are often multiple goals outstanding. Parallel
sequencing is one way to arrange it so that a single tactic is applied
to multiple goals, but there are other ways to do this. For example,
{tactic}`all_goals`{lit}` t` applies {lit}`t` to all open goals:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption
```

In this case, the {tactic}`any_goals` tactic provides a more robust solution.
It is similar to {tactic}`all_goals`, except it succeeds if its argument
succeeds on at least one goal:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption
```

The first tactic in the {kw}`by` block below repeatedly splits
conjunctions:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption
```

In fact, we can compress the full tactic down to one line:

```lean
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))
```

The combinator {tactic}`focus`{lit}` t` ensures that {lit}`t` only effects the current
goal, temporarily hiding the others from the scope. So, if {lit}`t`
ordinarily only effects the current goal, {tactic}`focus`{lit}` (`{tactic}`all_goals`{lit}` t)` has
the same effect as {lit}`t`.

# Rewriting

The {tactic}`rw` tactic and the {tactic}`simp` tactic
were introduced briefly in {ref "calculational-proofs"}[Calculational Proofs]. In this
section and the next, we discuss them in greater detail.

:::setup
````
variable (x y : α) (h : x = y)
theorem add_comm : ∀ (x y : Nat), x + y = y + x := by omega
````

The {tactic}`rw` tactic provides a basic mechanism for applying
substitutions to goals and hypotheses, providing a convenient and
efficient way of working with equality. The most basic form of the
tactic is {tactic}`rw`{lit}` [t]`, where {lit}`t` is a term whose type asserts an
equality. For example, {lit}`t` can be a hypothesis {lean}`h : x = y` in the
context; it can be a general lemma, like
{lean}`add_comm : ∀ x y, x + y = y + x`, in which the rewrite tactic tries to find suitable
instantiations of {lean}`x` and {lean}`y`; or it can be any compound term
asserting a concrete or general equation. In the following example, we
use this basic form to rewrite the goal using a hypothesis.

:::

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0
```

:::setup
````
variable (t : α)
````

In the example above, the first use of {leanRef}`rw` replaces {leanRef}`k` with
{leanRef}`0` in the goal {leanRef}`f k = 0`. Then, the second one replaces {leanRef}`f 0`
with {leanRef}`0`. The tactic automatically closes any goal of the form
{lean}`t = t`. Here is an example of rewriting using a compound expression:
:::

```lean
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption
```

Here, {leanRef}`h hq` establishes the equation {leanRef}`x = y`.

Multiple rewrites can be combined using the notation {tactic}`rw`{lit}` [t_1, ..., t_n]`,
which is just shorthand for {tactic}`rw`{lit}` [t_1]; ...; `{tactic}`rw`{lit}` [t_n]`. The previous example can be written as follows:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]
```

By default, {leanRef}`rw` uses an equation in the forward direction, matching
the left-hand side with an expression, and replacing it with the
right-hand side. The notation {lit}`←t` can be used to instruct the
tactic to use the equality {lit}`t` in the reverse direction.

```lean
example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]
```

In this example, the term {leanRef}`←h₁` instructs the rewriter to replace
{leanRef}`b` with {leanRef}`a`. In the editors, you can type the backwards arrow as
{kbd}`\l`. You can also use the ascii equivalent, {lit}`<-`.

Sometimes the left-hand side of an identity can match more than one
subterm in the pattern, in which case the {tactic}`rw` tactic chooses the
first match it finds when traversing the term. If that is not the one
you want, you can use additional arguments to specify the appropriate
subterm.

```lean
example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]
```

:::TODO
Get the intermediate proof states from `rw` into the reference ring to help these examples be better
:::

In the first example above, the first step rewrites {leanRef}`a + b + c` to
{leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit}`)`. The next step applies commutativity to the term
{leanRef}`b + c`; without specifying the argument, the tactic would instead rewrite
{leanRef}`a`{lit}` + (`{leanRef}`b + c`{lit})` to {lit}`(`{leanRef}`b + c`{lit}`) + `{leanRef}`a`. Finally, the last step applies
associativity in the reverse direction, rewriting {leanRef}`a`{lit}` + (`{leanRef}c`{lit}` + `{leanRef}`b`{lit})` to
{leanRef}`a + c + b`. The next two examples instead apply associativity to
move the parenthesis to the right on both sides, and then switch `b`
and `c`. Notice that the last example specifies that the rewrite
should take place on the right-hand side by specifying the second
argument to `Nat.add_comm`.

By default, the `rw` tactic affects only the goal. The notation
{tactic}`rw`{lit}` [t] `{kw}`at`{lit} h` applies the rewrite `t` at hypothesis `h`.

```lean
example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
```

The first step, {leanRef}`rw [Nat.add_zero] at h`, rewrites the hypothesis {leanRef}`a + 0 = 0` to {leanRef}`a = 0`.
Then the new hypothesis {leanRef}`a = 0` is used to rewrite the goal to {leanRef}`f 0`{lit}` = `{leanRef}`f 0`.

:::leanFirst
The {leanRef}`rw` tactic is not restricted to propositions.
In the following example, we use {tactic}`rw`{lit}` [h] `{kw}`at`{lit}` t` to rewrite the hypothesis {leanRef}`t : Tuple α n` to {leanRef}`t : Tuple α`{lit}` 0`.

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t
```
:::

# Using the Simplifier
%%%
tag := "using-the-simplifier"
%%%

Whereas {tactic}`rw` is designed as a surgical tool for manipulating a
goal, the simplifier offers a more powerful form of automation. A
number of identities in Lean's library have been tagged with the
{attr}`[simp]` attribute, and the {tactic}`simp` tactic uses them to iteratively
rewrite subterms in an expression.

```lean
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption
```

In the first example, the left-hand side of the equality in the goal
is simplified using the usual identities involving 0 and 1, reducing
the goal to {leanRef}`x * y`{lit}` = `{leanRef}`x * y`. At that point, {leanRef}`simp` applies
reflexivity to finish it off. In the second example, {leanRef}`simp` reduces
the goal to {leanRef}`p (x * y)`, at which point the assumption {leanRef}`h`
finishes it off. Here are some more examples
with lists:

```lean
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]
```

As with {leanRef}`rw`, you can use the keyword {leanRef}`at` to simplify a hypothesis:

```lean
example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption
```

Moreover, you can use a “wildcard” asterisk to simplify all the hypotheses and the goal:

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption
```

:::setup
````
variable (x y z : Nat)
````

For operations that are commutative and associative, like
multiplication on the natural numbers, the simplifier uses these two
facts to rewrite an expression, as well as _left commutativity_. In
the case of multiplication the latter is expressed as follows:
{lean}`x * (y * z) = y * (x * z)`. The {leanRef}`local` modifier tells the simplifier
to use these rules in the current file (or section or namespace, as
the case may be). It may seem that commutativity and
left-commutativity are problematic, in that repeated application of
either causes looping. But the simplifier detects identities that
permute their arguments, and uses a technique known as _ordered
rewriting_. This means that the system maintains an internal ordering
of terms, and only applies the identity if doing so decreases the
order. With the three identities mentioned above, this has the effect
that all the parentheses in an expression are associated to the right,
and the expressions are ordered in a canonical (though somewhat
arbitrary) way. Two expressions that are equivalent up to
associativity and commutativity are then rewritten to the same
canonical form.
:::

```lean
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
------
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption
```

As with {tactic}`rw`, you can send {tactic}`simp` a list of facts to use,
including general lemmas, local hypotheses, definitions to unfold, and
compound expressions. The {tactic}`simp` tactic also recognizes the {lit}`←t`
syntax that {tactic}`rewrite` does. In any case, the additional rules are
added to the collection of identities that are used to simplify a
term.

```lean
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]
```

A common idiom is to simplify a goal using local hypotheses:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]
```

:::leanFirst
To use all the hypotheses present in the local context when
simplifying, we can use the wildcard symbol, {leanRef}`*`:

```lean
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]
```
:::

Here is another example:

```lean
example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

:::leanFirst
The simplifier will also do propositional rewriting. For example,
using the hypothesis {leanRef in:="p ∧ q"}`p`, it rewrites {leanRef}`p ∧ q` to {leanRef in:="p ∨ q"}`q` and {leanRef}`p ∨ q` to {lean}`True`,
which it then proves trivially. Iterating such
rewrites produces nontrivial propositional reasoning.

```lean
example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]
```
:::

The next example simplifies all the hypotheses, and then uses them to prove the goal.

```lean
example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]
```

One thing that makes the simplifier especially useful is that its
capabilities can grow as a library develops. For example, suppose we
define a list operation that symmetrizes its input by appending its
reversal:

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
```

:::leanFirst
Then for any list {leanRef in:="mk_symm xs"}`xs`, {leanRef}`(mk_symm xs).reverse` is equal to {leanRef}`mk_symm xs`,
which can easily be proved by unfolding the definition:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]
```
:::

We can now use this theorem to prove new results:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
       : (mk_symm xs).reverse = mk_symm xs := by
 simp [mk_symm]
------
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption
```

But using {leanRef}`reverse_mk_symm` is generally the right thing to do, and
it would be nice if users did not have to invoke it explicitly. You can
achieve that by marking it as a simplification rule when the theorem
is defined:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

The notation {leanRef}`@[simp]` declares {leanRef}`reverse_mk_symm` to have the
{attr}`[simp]` attribute, and can be spelled out more explicitly:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

The attribute can also be applied any time after the theorem is declared:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
```

:::leanFirst
Once the attribute is applied, however, there is no way to permanently
remove it; it persists in any file that imports the one where the
attribute is assigned. As we will discuss further in
{ref "attributes"}[Attributes], one can limit the scope of an attribute to the
current file or section using the {leanRef}`local` modifier:

```lean
def mk_symm (xs : List α) :=
 xs ++ xs.reverse
------
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end
```
:::

Outside the section, the simplifier will no longer use
{leanRef}`reverse_mk_symm` by default.

Note that the various {leanRef}`simp` options we have discussed—giving an
explicit list of rules, and using {leanRef}`at` to specify the location—can be combined,
but the order they are listed is rigid. You can see the correct order
in an editor by placing the cursor on the {leanRef}`simp` identifier to see
the documentation string that is associated with it.

:::leanFirst
There are two additional modifiers that are useful. By default,
{leanRef}`simp` includes all theorems that have been marked with the
attribute {attr}`[simp]`. Writing {leanRef}`simp only` excludes these defaults,
allowing you to use a more explicitly crafted list of
rules. In the examples below, the minus sign and
{leanRef}`only` are used to block the application of {leanRef}`reverse_mk_symm`.

```lean
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
```
:::

The {leanRef}`simp` tactic has many configuration options. For example, we can enable contextual simplifications as follows:

```lean
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual
```

With {leanRef}`+contextual`, the {leanRef}`simp` tactic uses the fact that {leanRef}`x = 0` when simplifying {leanRef}`y + x = y`, and
{leanRef}`x ≠ 0` when simplifying the other branch. Here is another example:

```lean
example : ∀ (x : Nat) (h : x = 0), y + x = y := by
  simp +contextual
```

:::leanFirst
Another useful configuration option is {leanRef}`+arith` which enables arithmetical simplifications.

```lean
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith
```
:::

# Split Tactic

::::leanFirst


The {leanRef}`split` tactic is useful for breaking nested {kw}`if`-{kw}`then`-{kw}`else` and {kw}`match` expressions in cases.
For a {kw}`match` expression with $`n` cases, the {leanRef}`split` tactic generates at most $`n` subgoals. Here is an example:


```lean
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl
```
::::

We can compress the tactic proof above as follows.

```lean
def f (x y z : Nat) : Nat :=
 match x, y, z with
 | 5, _, _ => y
 | _, 5, _ => y
 | _, _, 5 => y
 | _, _, _ => 1
------
example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros; simp [f]; split <;> first | contradiction | rfl
```

The tactic {leanRef}`split <;> first | contradiction | rfl` first applies the {leanRef}`split` tactic,
and then for each generated goal it tries {leanRef}`contradiction`, and then {leanRef}`rfl` if {leanRef}`contradiction` fails.
Like {leanRef}`simp`, we can apply {leanRef}`split` to a particular hypothesis:

```lean
def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp +arith at h
```

# Extensible Tactics

:::leanFirst
In the following example, we define the notation {leanRef}`triv` using the command {leanRef}`syntax`.
Then, we use the command {leanRef}`macro_rules` to specify what should
be done when {leanRef}`triv` is used. You can provide different expansions, and the tactic
interpreter will try all of them until one succeeds:

```lean
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
```
:::

# Exercises

1. Go back to the exercises in {ref "propositions-and-proofs"}[Chapter Propositions and Proofs] and
{ref "quantifiers-and-equality"}[Chapter Quantifiers and Equality] and
redo as many as you can now with tactic proofs, using also {tactic}`rw`
and {tactic}`simp` as appropriate.

2. Use tactic combinators to obtain a one-line proof of the following:

```lean
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  sorry
```
