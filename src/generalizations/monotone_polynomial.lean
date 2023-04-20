/-

#  Generalizations, automatizations, `library_search`, `simp`, tactics

## [Atelier Lean 2023](http://www.rnta.eu/7MSRNTA/index.html)

Day 1, Damiano Testa

As it happens, someone comes along and says:

"I just learned a cool fact!  A polynomial with coefficients in `ℕ` is monotone!"

Let's formalize this result!

Let's also think about what it really means...

Surely they intended to say that viewing a polynomial with coefficients in `ℕ`
as a function `ℕ → ℕ`, we obtain a monotone function.

-/

/-
### import

tells Lean to learn the facts about polynomials contained in a file called
`[root_dir]/ring_theory/polynomial/basic.lean`
-/
import ring_theory.polynomial.basic
-- we also want facts about *n*on*n*egative reals
import data.real.nnreal

/-
### namespace

means that if we construct something and we call it `X`
its real name is going to be `rome.X`.
useful to avoid name-clashes with pre-existing objects.
-/
namespace rome

/-
### open

`open whatever` instructs Lean that when we refer
to `X`, it should look for `X` or `whatever.X`.

`namespace`s are ubiquitous, thus `open` allows us to avoid
constantly writing `function.[...]` or `polynomial.[...]`.
-/
open function polynomial

/-
### open_locale

Allows to use special notations. For instance
* `open_locale nnreal` gives meaning to the symbol
  `ℝ≥0` for the non-negative reals;
* `open_locale polynomial` gives meaning to the symbol
  `R[X]` for the polynomial ring over `R`.
-/
open_locale nnreal polynomial

namespace nat

/-
### variables

`variables (x : X)` means that, from now on
(within the current `section`/`namespace`/...), if we write `x`
and Lean does not already know what `x` means, then it tries
to see if `(x : X)` works and uses it.

Useful to avoid repetitions in a group of results that have
common assumptions and notation.
-/
variables (f : ℕ[X])        -- `f` is a polynomial with coefficients in `ℕ`
          (P : ℕ[X] → Prop) -- `P` is a property of polynomials: `P f` may be
                            -- true or false

/-
### Digression on `Prop`

`Prop` is the "generic Type of propositions".  Most of the times, you can
think of this as `true/false`.
(The Type of "actual" `true/false` is called `bool` and
`true` is really `tt`, `false` is really `ff`.)

Thus, when we write `P : ℕ[X] → Prop` we are introducing a function `P`
that takes a polynomial with coefficients in `ℕ` and returns `true`
or `false`.  For instance, "being monic" could be one such function.
Also, "the leading coefficient of `f` equals the first decimal digit
of the `deg f`-th odd perfect number, if it exists, and `1` otherwise".
-/

/-
### theorem/lemma

Presumably, you already know about this.

The syntax is
  `theorem <name_of_theorem> <hypotheses> : <conclusion> := <proof>`

* <name_of_theorem> is the identifier that we can then use to refer to it.
  It is like a `\label` in laTex.

* <hypotheses> is where we list the assumptions that we make.
  For instance `(a : ℕ)` or `[comm_group G]` or `(f : ℕ → ℝ)` or
  `(Goldbach: ∀ n : ℕ, ∃ p q, prime p ∧ prime q ∧ p + q = n)`.

  Bonus: to "see" Type-inference at work, look at the outputs of
  ```lean
  #check     ∀ n, ∃ p q, prime p ∧ prime q ∧ p + q = n
  #check ∀ n : ℕ, ∃ p q, prime p ∧ prime q ∧ p + q = n
  ```

* <proof> is the actual proof term.
  Usually, this is a sequence of tactics inside a `begin ... end` block.
-/
theorem my_induction
  (P_zero  : P 0)
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  -- hover over `polynomial.induction_on'`
  apply polynomial.induction_on' f; clear f,
  { -- `hint` reports `assumption`, among others
    -- `library_search` reports `exact P_add`
    exact P_add },
  { intros n a,
    simp [← C_mul_X_pow_eq_monomial],  -- replace `monomial n a` with `a * X ^ n`
    induction a with a ha,
    -- proceed by induction on `a`, call
    -- * `a` the variable in the induction step
    -- * `ha` the inductive hypothesis
    { -- base case: `a = 0`
      -- `squeeze_simp` or `simp?` to get some insight
      simp [P_zero]
      -- `rwa [char_p.cast_eq_zero, zero_mul]` also works
    },
    { -- induction step: `a → a + 1`
      -- `a.succ` stands for `nat.succ a`: the `succ`essor function applied to `a`
      -- Lean "prefers" `nat.succ` since it is one of the two "constructors" for `ℕ`.
      simp [add_mul],
      apply P_add _ _ ha (P_X_pow _) } }
end

/-
### example

The same (almost) as `theorem`, except that we cannot assign it a name.
-/
example : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { -- show that the `0`-polynomial is monotone
    simp,
    library_search,
    -- we can compact this to `simp [monotone_const]` or more explicitly `simp only [eval_zero, monotone_const]`
  },
  { -- if two polynomials are monotone, then so is their sum
    intros f g hf hg,
    -- use that the sum of two monotone functions is monotone
    -- we can find the name of the lemma using auto-completion (Ctrl-Space) and guessing
    convert monotone.add hf hg,
    simp },
  { -- show that monomials are monotone
    intros,
    simp,
    apply monotone.pow_right,
    apply monotone_id -- we could have used `suggest` here, for a long list of proofs
  },
end

end nat

/-
Now that we proved it for `ℕ`, let's generalize to `ℝ≥0`.

Copy-paste the above, change `ℕ` to `ℝ≥0` and fix the issues.
-/
namespace nnreal

variables (f : ℝ≥0[X]) (P : ℝ≥0[X] → Prop)

theorem my_induction
  (P_zero  : P 0)
  (P_C_mul : ∀ a p, P p → P (C a * p))
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  apply polynomial.induction_on' f; clear f,
  { exact P_add },
  { intros n a,
    rw ← C_mul_X_pow_eq_monomial,
    apply P_C_mul,
    apply P_X_pow }
end

theorem monotone_eval : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { -- show that the 0-polynomial is monotone
    simp [monotone_const] },
  { -- the product of a constant and a monotone polynomial is monotone
    intros a f hf,
    simp_rw eval_C_mul,
    apply monotone.mul,
    { apply monotone_const },
    { assumption },
    { simp },
    { simp } },
  { -- use that the sum of two monotone functions is monotone
    intros f g,
    simp,
    apply monotone.add },
  { -- show that monomials are monotone
    intros,
    simp only [eval_pow, eval_X],
    apply monotone.pow_right,
    apply monotone_id },
end

end nnreal

#lint

namespace next

--  -->  semiring --> comm --> ordered --> canonically
variables {R : Type} [canonically_ordered_comm_semiring R]

variables (f : R[X]) (P : R[X] → Prop)

theorem my_induction
  (P_C_mul : ∀ a p, P p → P (C a * p))
  (P_add   : ∀ p q, P p → P q → P (p + q))
  (P_X_pow : ∀ n : ℕ, P (X ^ n)) :
  P f :=
begin
  apply polynomial.induction_on' _ P_add,
  intros n a,
  rw ← C_mul_X_pow_eq_monomial,
  apply P_C_mul,
  apply P_X_pow,
end

theorem monotone_eval : monotone (λ n, f.eval n) :=
begin
  apply my_induction f _; clear f,
  { -- the product of a constant and a monotone polynomial is monotone
    intros a f hf,
    simp_rw eval_C_mul,
    apply monotone.mul,
    { apply monotone_const },
    { assumption },
    --sorry
     { simp },
    --sorry
     { simp } },
  { -- use that the sum of two monotone functions is monotone
    intros f g,
    simp,
    apply monotone.add },
  { -- show that monomials are monotone
    intros,
    simp,
    apply monotone.pow_right,
    apply monotone_id },
end

example (f : ℕ[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

example (f : ℝ≥0[X]) : monotone (λ n, f.eval n) :=
begin
  apply next.monotone_eval,
end

end next

end rome
