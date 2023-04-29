# Automation

Computers take on repetitive tasks.

&nbsp;

In the context of formalization of mathematics, the computer also

* helps producing more complicated arguments, as it separates neatly different parts of the argument;
* informs, ideally, the **discovery** of new mathematical results;
* detects *very well* unnecessary hypotheses.

[The resulting generality is often only useful to simplify *formalization*, rather than *discovery* of mathematics.]

Currently, Machine Learning, Artificial Intelligence, Neural Networks and auto-formalizations are not yet really available.

&nbsp;

There is lots of interest and steady progress on this front.

---

##  Tactics

The first main "automation" tactics that you will likely run into are `library_search` and `simp`.

&nbsp;

Really, *any* tactic is a form of automation.

&nbsp;

Tactics allow to maintain abstraction:

*  we humans talk about mathematical concepts,
*  the computer has some representation for these concepts.

Tactics bridge this gap.

&nbsp;

We do not even need to know what the computer's internal representation is: tactics handle the translation.

---

## `library_search`

`mathlib` is a massive repository: it contains
* over 1 million lines of code
* over 60 thousand lemmas.

Most of the basic[^1] lemmas are already available.

&nbsp;

`library_search` helps you find them!

[^1]: "Basic" may mean *really* basic, to a level that you may not even consider them "lemmas".

---

```lean
import tactic

example {a b c : ℕ} : a ^ (b + c) = a ^ b * a ^ c :=
by library_search

--  Try this: exact pow_add a b c
```

&nbsp;

Besides `library_search`, `mathlib` has a very helpful [naming convention](https://leanprover-community.github.io/contribute/naming.html) that allows you to "guess" names of lemmas.

&nbsp;


---

## `simp`

As the name suggests, the `simp`lifier tries to simplify a goal (or a target hypothesis).

```lean
example {a b : ℤ} : - (-1 * a + 0 * b) = a * (1 + a * 0) :=
begin
  simp,
end
```
Here, `simp` used the lemmas

|||
|-|-|
|`neg_mul` | `neg_neg` |
|`add_zero` | |
|`one_mul` | `mul_one` |
|`mul_zero` | `zero_mul` |

---

##  "`simp`-lemmas": lemmas that `simp` uses

* They assert an equality or an iff.
* The LHS **looks more complicated** than the RHS.

```lean
#print one_mul   -- means:   1 * a = a
#print zero_mul  -- means:   0 * a = 0
#print add_zero  -- means:   a + 0 = 0
#print neg_neg   -- means:    - -a = a
#print mul_zero  -- means:   a * 0 = 0
#print mul_one   -- means:   a * 1 = a
#print neg_mul   -- means:  -a * b = -(a * b)
```

The asymmetry helps Lean: it flows along
$${\texttt{hard LHS}} \longrightarrow {\texttt{easy RHS}}.$$

[Being a "`simp`-lemma" is something that *you* must communicate to Lean: there is no automated mechanism that makes Lean self-select which lemmas are `simp`-lemmas.]
