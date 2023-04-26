### Automatizations

In the context of formalization of mathematics, the computer

* takes on repetitive tasks;
* helps producing more complicated arguments, as it helps separating neatly different parts of the argument;
* informs, ideally, the ***discovery*** of new mathematical results;
* works *very well* to detect unnecessary hypotheses

  > however, the resulting generality is often only useful to simplify *formalization*, rather than *discovery* of mathematics.


Currently, Machine Learning, Artificial Intelligence, Neural Networks and auto-formalizations are not yet really available, though there is lots of interest and steady progress on this front.

---

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

[^1]: basic means *really* basic, to a level that you may not even consider them "lemmas".
