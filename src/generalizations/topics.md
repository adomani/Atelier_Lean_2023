# Automation

In the context of formalization of mathematics, the computer

* takes on repetitive tasks;
* helps producing more complicated arguments, as it helps separating neatly different parts of the argument;
* informs, ideally, the ***discovery*** of new mathematical results;
* works *very well* to detect unnecessary hypotheses

  > however, the resulting generality is often only useful to simplify *formalization*, rather than *discovery* of mathematics.


Currently, Machine Learning, Artificial Intelligence, Neural Networks and auto-formalizations are not yet really available, though there is lots of interest and steady progress on this front.

---

##  Tactics

The first main "automation" tactics that you will likely run into are `library_search` and `simp`.

Really, *any* tactic is a form of automation.

Tactics allow us to maintain an abstraction:

*  we humans, think that we are talking about mathematical concepts,
*  the computer has its own internal representation for these same concepts.

Tactics bridge this gap: we do not even need to know what the computer's internal representation is: tactics handle the translation.

---

## `library_search`

`mathlib` is a massive repository.

It contains over 1 million lines of code and over 60 thousand lemmas.

Most of the basic[^1] lemmas are already available.

`library_search` helps you find them!

```lean
import tactic

example {a b c : ℕ} : a ^ (b + c) = a ^ b * a ^ c :=
by library_search

--  Try this: exact pow_add a b c
```

[^1]: "Basic" means *really* basic, to a level that you may not even consider them "lemmas".

---

I personally used `library_search` constantly, when I had just started using Lean.

Later on, I became more familiar with `mathlib`'s [naming convention](https://leanprover-community.github.io/contribute/naming.html) I now use `library_search` more rarely.

---

## `simp`

As the name suggests, the `simp`lifier tries to simplify a goal (or a target hypothesis).

```lean
example {a b : ℤ} : - (-1 * a + 0 * b) = a * (1 + a * 0) :=
begin
  simp,
end
```
In the previous example, `simp` used the lemmas `one_mul, zero_mul, add_zero, neg_neg, mul_zero, mul_one, neg_mul`.

---

##  `simp`-lemmas

The lemmas that `simp` uses are "`simp`-lemmas": carefully selected lemmas to have, among others, two basic features
* they assert an equality or an iff;
* the LHS *looks more complicated* than the RHS.

```lean
#print one_mul:   --   1 * a = a
#print zero_mul:  --   0 * a = 0
#print add_zero:  --   a + 0 = 0
#print neg_neg:   --    - -a = a
#print mul_zero:  --   a * 0 = 0
#print mul_one:   --   a * 1 = a
#print neg_mul:   --  -a * b = -(a * b)
```

The asymmetry helps Lean: it only tries to apply the lemmas in the direction hard --> easy.

[Being a "`simp`-lemma" is just something that you must communicate to Lean: there is no automated mechanism that makes Lean self-select which lemmas are `simp`-lemmas.]
