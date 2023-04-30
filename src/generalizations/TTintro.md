#  Introduction to Type Theory

This talk is an extended digression on Type Theory.

As is usually the case, foundations of mathematics have a marginal impact on "real-world" mathematics.

This is true also when using Lean

$\ldots$ most of the times!

---

# Set Theory

Set Theory is a common choice of foundation for mathematics.

This normally comes with

* a more or less "primitive" concept of a `set`;
* the `belongs-to` relation $\in$ among sets;
* several rules for constructing new sets from old ones;
* an empty set.

Mathematics is then built on top of these foundations.

---

# Everything is a set

We practice Set Theory by ensuring that "everything is a set":

* the natural numbers are a set,
* ordered pairs are a set,
* the real numbers are a set,
* functions are a set,
* sequences are functions (and hence are a set),
* $\ldots$

Everything is a set. Everything. EVERYTHING.

---

# Set Theory -- really?

Most mathematicians `can` explain how to encode their favourite mathematical concept using only the basic axioms of set theory.

Most mathematicians would probably `not want` to do that.

`Descending` inside all the nested sets of sets of sets until we reach the empty set is probably even `detrimental` to developing an `intuition` about modular forms, schemes, or any `advanced` mathematical concept.

---

We may `undo` one nesting or two, but, after that, we probably stop and think about `structured` sets.

For instance, if $f \colon A \longrightarrow B$ is a function, we may think of it as a way of converting an element of the set $A$ to an element of the set $B$. \\
$\to$ No undoing: a `structured` function.

Sometimes, it can be useful to think of the `graph` of $f$ (which, in Set Theory `is` the function). \\
$\to$ 1 undoing: `structured` ordered pairs.

How often have you then used the Kuratowski's encoding of ordered pairs to `really` understand $f$? \\
$\to$ 2 undoings: `unstructured` chaos.

---

##  Types as structured sets

From the perspective of Set Theory,
* a `Type` is like a set,
* its elements are called `terms`,
* the `belong-to` relation is denoted by `:`.

&nbsp;

Thus, if `t` is a term of a Type `T`, we can write `t : T`.

&nbsp;

A fundamental axiom is that every term has a unique Type.

&nbsp;

Types usually come with rules, called `constructors`, for building terms of the given Type.

&nbsp;

The constructors endow their Type with some internal `structure`.

&nbsp;

Let's see the definition of natural numbers in Lean.

---

```lean
inductive myℕ
  | zero : myℕ
  | succ : myℕ → myℕ
```
[Click here to open the Lean web editor](https://leanprover-community.github.io/lean-web-editor/#code=inductive%20my%E2%84%95%0A%20%20%7C%20zero%20%3A%20my%E2%84%95%0A%20%20%7C%20succ%20%3A%20my%E2%84%95%20%E2%86%92%20my%E2%84%95%0A%0A%23print%20prefix%20my%E2%84%95%0A).

&nbsp;

The code above defines a Type `myℕ`.

&nbsp;

The Type `myℕ` contains an element (really, a `term`), that we call `zero`.

&nbsp;

We also postulate the existence of a function `succ` from `myℕ` to `myℕ`.

&nbsp;

Lean's Type Theory takes care of making `myℕ` "universal".

&nbsp;

For instance, Lean auto-generates the induction principle.

---

In Lean's Type Theory, there is an inbuilt axiom:

* *every* term has a *unique* Type.

&nbsp;

For instance, the Type `myℕ` above contains the term `zero` (really, the term is `myℕ.zero`).

&nbsp;

Imagine that we eventually we define `myℤ.zero`.

&nbsp;

The two terms `myℕ.zero : myℕ` and `myℤ.zero : myℤ` are *different*.

---

We can make Lean aware of the unique homomorphism `myℕ → myℤ`.

&nbsp;

However, we can pretend that `myℕ.zero` and `myℤ.zero` are "the same", only as long as some tactic takes care of converting between the two.

&nbsp;

Notice also that in Set Theory, the usual definitions of
$$
  0 \in \mathbb{N} \qquad {\textrm{and}} \qquad 0 \in \mathbb{Z}
$$
yield *different* elements.

&nbsp;

Even the containment $\mathbb{N} \subset \mathbb{Z}$ is false.

&nbsp;

Type Theory simply makes us more aware of these (usually inconsequential) inconsistencies.

---

## Why many proof checkers use Type Theory?

Using a proof checker, ultimately means writing a computer program to verify a mathematical reasoning.

In Set Theory, **many** syntactically correct statements are garbage.

For instance, deciding whether the relations
$$
  \mathbb{N} \in \pi
  \qquad {\textrm{or}} \qquad
  \mathbb{Q}_{\le 0} \subset e
  \qquad {\textrm{or}} \qquad
  \sqrt{2} ^ 2 = \emptyset
$$
hold is "meaningful".

In Type Theory, none of the above `Type-checks`.

---

$$
  \mathbb{N} \in \pi
  \qquad {\textrm{or}} \qquad
  \mathbb{Q}_{\le 0} \subset e
  \qquad {\textrm{or}} \qquad
  \sqrt{2} ^ 2 = \emptyset
$$

&nbsp;

In the background, Lean is constantly Type-checking every assertion.

&nbsp;

This means that it can alert us to the fact that we are writing "non-sense" *before* a proof-checker based on Set Theory would.

&nbsp;

You can think of `Type-checking` as `dimensional-analysis` in physics:

[if you compute the speed of your car to be $70$Kg, you are sure that you've made a mistake!]

---

##  Type Theory vs Set Theory

To me, the most insightful consequence of formalizing mathematics in Type Theory came from focusing on the separation:

 mathematical concept


---

Using Set Theory or Type Theory as foundations, has little bearing on the theorems that we can prove.

Sometimes, it may lead us to prefer one approach over another.

In practice, the main difference of Type Theory using Lean vs ""

---
