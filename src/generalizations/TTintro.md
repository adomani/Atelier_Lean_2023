#  Introduction to Type Theory

This talk is an extended digression on Type Theory.

&nbsp;

As is usually the case, foundations of mathematics have a marginal impact on "real-world" mathematics.

&nbsp;

This is true also when using Lean

&nbsp;

$\ldots$ most of the times!

---

# Set Theory

Most mathematicians learn that Set Theory is the foundation of mathematics.

This normally comes with

&nbsp;

* a more or less "primitive" concept of a `set`;
* the `belongs-to` relation $\in$ among sets;
* an empty set;
* several rules for constructing new sets from old ones.

&nbsp;

Mathematics is then built on top of these foundations (often assuming the existence of an infinite set).

---

# Everything is a set

Whenever we introduce a new concept, we practice Set Theory by making sure that "it is a set":

* the natural numbers are a set,
* ordered pairs are a set,
* the real numbers are a set,
* functions are a set,
* sequences are functions (and hence are a set),
* $\ldots$


&nbsp;

After all, everything is a set. Everything. EVERYTHING.

&nbsp;

---

# Set Theory -- really?

I imagine that most mathematicians *could* explain how to encode their favourite mathematical concept using only the rules for forming sets out of old sets, starting from the empty set.

&nbsp;

I also imagine that most mathematicians would rather *not* do that.

&nbsp;

Descending inside all the nested sets of sets of sets until we reach the empty set is probably detrimental to developing an intuition about modular forms, or schemes.

---

We may "undo" one nesting or two, but, after that, we probably stop and think about `structured` sets.

&nbsp;

For instance, if $f \colon A \longrightarrow B$ is a function, we may think of it as a way of converting an element of the set $A$ to an element of the set $B$.

$\to$ No undoing: a `structured` function.

&nbsp;

Sometimes, it can be useful to think of the "graph of $f$" (which, in Set Theory `is` the function).

$\to$ 1 undoing: `structured` ordered pairs.

&nbsp;

How often have you then used the Kuratowski's encoding of ordered pairs to `really` understand $f$?

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

---

 is a Type, containing



 most mathematicians who are not logicians, is this
